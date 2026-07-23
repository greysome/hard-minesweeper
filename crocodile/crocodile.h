#ifndef CROCODILE_H
#define CROCODILE_H

#include <errno.h>
#include <fcntl.h>
/* for frexp, ldexp */
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

/* Custom assert that automatically traps, allowing gdb to be used at
   the point of failure. */
#ifdef DEBUG
  #define ASSERT(cond)                                     \
    do {                                                   \
      if (!(cond)) {                                       \
        fprintf(stderr, "assertion failed: " #cond "\n");  \
        __builtin_trap();                                  \
      }                                                    \
    } while (0)
#else
  #define ASSERT(cond)
#endif

/* -----------------------------------------------------------------------------
                                 SOLVER API
   ----------------------------------------------------------------------------- */

/* This solver works exclusively with AT_LEAST constraints, denoted as
   AT_LEAST(k; l1 l2 ... ln), where the li's are literals. It is true
   iff at least k of l1,l2,...,ln is true. Boolean clauses are special
   cases where k=1. */
typedef struct {
  /* Buffer information for reuse */
  int *buf;

  /* -1 = not done, 0 = UNSAT, 1 = SAT and the model can be found in vals */
  int is_sat;
  int num_vars;
  int decision_level;

  int num_assumptions;
  int *assumptions;
  /* For a literal l with index i,
     vals[i] = -1 if the literal is unassigned,
     vals[i] = 2d + (l & 1) otherwise, where d is the decision level of
     its assignment. */
  int *vals;
  /* Variables appearing in recent conflicts tend to have higher
     activities.  At each decision, the highest-activity variable is
     chosen (assuming all assumptions are already decided). */
  double *activities;
  /* A binary max-heap on variable activities. Satisfies the invariant
     activities[heap[i]] <= activities[heap[(i-1) >> 1]]. */
  int *heap;
  int *heap_idxs;
  int heap_size;
  /* Current contribution to variable activity. Multiplies by a
     constant factor after each conflict. */
  double delta;
  /* Once delta reaches this threshold, all activity scores will be
     normalised by dividing by the threshold. */
  double delta_threshold;

  /* Each literal has an entry pointing to the first constraint
     watching it. */
  int *watches;
  /* Each literal has an entry pointing to the constraint that it is
     propagated from, or -1 if it is a decision literal. */
  int *reasons;
  /* Used for conflict resolution. */
  int *stamps;
  /* Used for backjumping. */
  int *level_idxs;
  /* The current timestamp, used in stamps. */
  int cur_stamp;

  /* A packed buffer of variable-size constraints, each in the
     following format:
     - constraint[0]: n, no. of literals
     - constraint[1]: k, no. of true literals to satisfy constraint
     - constraint[2..2+n-1]: n lits. The first k+1 entries are the watchees.
     - constraint[2+n..2+n+k]: k+1 links for each watchee. Each entry
       points to the next constraint watching that literal. */
  int *constraints;
  /* Points to the first address of a new constraint. */
  int *next_constraint;

  int *trail;
  /* Pointers to the trail. The head represents the latest assignment
    made (which can be either a propagation or decision), while the
    tail represents the latest assignment whose propagations have been
    processed. */
  int qhead;
  int qtail;

  /* Profiling counters */
  int num_watch_updates;
  int num_learnt;
} Solver;

void solver_init_bufs(Solver *solver);
bool solver_init(Solver *solver, int num_vars);
void solver_free(Solver *solver);
void solver_debug(Solver *solver);
void solver_add_atleast(Solver *solver, int n, int k, int *slits);
void solver_add_atmost(Solver *solver, int n, int k, int *slits);
void solver_add_equals(Solver *solver, int n, int k, int *slits);
void solver_assume(Solver *solver, int slit);
void solver_solve(Solver *solver);


/* -----------------------------------------------------------------------------
                                 SOLVER CODE
   ----------------------------------------------------------------------------- */

/* A literal with index i has two encodings. The signed encoding
   stores it as i (non-negated) or -i (negated); it is accepted in
   user-facing routines and is used for input/output. The LSB encoding
   stores it as 2i+1 (non-negated) or 2i (negated); it is used
   internally since it makes for more convenient array indices.

   From now on, I will use `slit` for sign-encoded literals, and `lit`
   for LSB-encoded literals. */

/* Macros for lits */
#define LIT_FALSE(i)  ((i) << 1)
#define LIT_TRUE(i)   (((i) << 1) + 1)
#define LIT_VAR(i)    ((i) >> 1)
#define LIT_SIGN(i)   ((i) & 1)
#define LIT_NEGATE(i) ((i) ^ 1)

/* Macros for vals */
#define VAL_SIGN(i)   ((i) & 1)
#define VAL_LEVEL(i)  ((i) >> 1)

int to_lit(int slit) {
  ASSERT(slit != 0);
  return slit > 0
    ? ((slit - 1) << 1) | 1
    : ((-slit - 1) << 1);
}

int to_slit(int lit) {
  ASSERT(lit >= 0);
  int var = LIT_VAR(lit);
  return lit & 1 ? var + 1 : -var - 1;
}

/* Buffer to hold per-literal/per-variable arrays and constraints */
#define BUF_SIZE (1 << 30)

/* Explicitly clear the internal buffer pointers so that the next
   solver_init() knows to call mmap(). */
void solver_init_bufs(Solver *solver) {
  solver->buf = NULL;
}

/* Initialise the solver's internal data structures using `num_vars`
   for offset calculation into its internal buffers. Allocates buffer
   memory using mmap() if not done previously. */
bool solver_init(Solver *solver, int num_vars) {
  if (solver->buf == NULL)
    solver->buf = malloc(BUF_SIZE);
  bool check = (uintptr_t)solver->buf % 8 == 0;
  ASSERT(check);

  solver->is_sat = -1;
  solver->num_vars = num_vars;
  solver->decision_level = 0;
  solver->num_assumptions = 0;
  int *buf = solver->buf;
  solver->activities = (double *)buf;  buf += sizeof(double) / sizeof(int) * num_vars;
  solver->assumptions = buf; buf += num_vars * 2;
  solver->vals = buf;        buf += num_vars;
  solver->heap = buf;        buf += num_vars;
  solver->heap_idxs = buf;   buf += num_vars;
  solver->watches = buf;     buf += 2 * num_vars;
  solver->reasons = buf;     buf += 2 * num_vars;
  solver->stamps = buf;      buf += num_vars;
  solver->level_idxs = buf;  buf += num_vars;
  /* The trail can temporarily reach length `num_vars + 1` when there
     is a conflict. */
  solver->trail = buf;       buf += num_vars + 1;
  solver->constraints = buf;
  solver->cur_stamp = 0;
  solver->delta = 1.0;
  solver->delta_threshold = ldexp(1.0, 1000);

  for (int var = 0; var < num_vars; var++) {
    solver->vals[var] = -1;
    solver->activities[var] = var;
    solver->heap[var] = num_vars - var - 1;
    solver->heap_idxs[var] = num_vars - var - 1;

    solver->watches[LIT_FALSE(var)] = -1;
    solver->watches[LIT_TRUE(var)] = -1;
    solver->reasons[LIT_FALSE(var)] = -1;
    solver->reasons[LIT_TRUE(var)] = -1;

    solver->stamps[var] = solver->cur_stamp;
  }
  solver->heap_size = num_vars;
  solver->level_idxs[0] = 0;
  solver->next_constraint = solver->constraints;
  solver->num_learnt = 0;
  solver->num_watch_updates = 0;

  solver->qhead = 0;
  solver->qtail = 0;
  return true;
}

void solver_free(Solver *solver) {
  free(solver->buf);
}

static void _print_constraint(Solver *solver, int *constraint) {
  int *p = constraint;
  int n = *(p++);
  int k = *(p++);
  fprintf(stderr, "%d of ", k);
  for (int i = 0; i < n; i++) {
    int lit = *(p++);
    int val = solver->vals[LIT_VAR(lit)];
    if (val == -1)
      fprintf(stderr, "\033[90m");
    else if (VAL_SIGN(val) == LIT_SIGN(lit))
      fprintf(stderr, "\033[32m");
    else if (VAL_SIGN(val) != LIT_SIGN(lit))
      fprintf(stderr, "\033[31m");

    if (!LIT_SIGN(lit))
      fprintf(stderr, "%c", '-');
    fprintf(stderr, "%d ", LIT_VAR(lit));
  }
  fprintf(stderr, "\033[0m");
}

void solver_debug(Solver *solver) {
  int num = 0;
  int *p = solver->constraints;

  /*
  fprintf(stderr, "==================================================\n");
  fprintf(stderr, "\nwatches\n-------\n");
  for (int idx = 0; idx < solver->num_vars; idx++) {
    int val = solver->vals[idx];
    fprintf(stderr, "%d: +[%d], -[%d]\n",
            idx,
            solver->watches[LIT_TRUE(idx)],
            solver->watches[LIT_FALSE(idx)]);
  }
  */

  fprintf(stderr, "\nclauses\n-------\n");
  while (p < solver->next_constraint) {
    num++;
    int n = p[0];
    int k = p[1];

    fprintf(stderr, "#%d @ [%ld]: ", num, p - solver->constraints);
    _print_constraint(solver, p);
    p += 2 + n;

    fprintf(stderr, "\tlinks: ");
    for (int j = 0; j < k+1; j++) {
      int link = *(p++);
      fprintf(stderr, "[%d] ", link);
    }
    fprintf(stderr, "\n");
  }

  fprintf(stderr, "\ntrail\n-------\n");
  for (int i = 0; i < solver->qhead; i++) {
    if (i < solver->qtail)
      fprintf(stderr, "\033[90m");
    else if (i == solver->qtail)
      fprintf(stderr, "\033[0m");

    int lit = solver->trail[i];
    fprintf(stderr, "#%d: ", i);
    if (!LIT_SIGN(lit))
      fprintf(stderr, "%c", '-');
    int reason = solver->reasons[lit];
    fprintf(stderr, "%d (level=%d) from [%d]",
            LIT_VAR(lit),
            VAL_LEVEL(solver->vals[LIT_VAR(lit)]),
            reason);
    if (reason != -1) {
      fprintf(stderr, ": ");
      _print_constraint(solver, solver->constraints + reason);
    }
    fprintf(stderr, "\n");
  }
  fprintf(stderr, "\n");

  fprintf(stderr, "\033[0m==================================================\n");
}

static void _heap_verify(Solver *solver) {
  ASSERT(solver->heap_size >= 0);
  if (solver->heap_size == 0)
    return;

  bool occupied[solver->num_vars];
  for (int var = 0; var < solver->num_vars; var++)
    occupied[var] = false;

  int cvar = solver->heap[0];
  ASSERT(cvar >= 0 && cvar < solver->num_vars);
  ASSERT(solver->heap_idxs[cvar] == 0);
  occupied[cvar] = true;

  for (int i = 1; i < solver->heap_size; i++) {
    cvar = solver->heap[i];
    int pvar = solver->heap[(i-1) >> 1];
    ASSERT(!occupied[cvar]);
    occupied[cvar] = true;
    ASSERT(cvar >= 0 && cvar < solver->num_vars);
    ASSERT(solver->activities[cvar] <= solver->activities[pvar]);
    ASSERT(solver->heap_idxs[cvar] == i);
  }
}

static void _heap_remove(Solver *solver, int idx) {
  int *heap = solver->heap;
  int *heap_idxs = solver->heap_idxs;
  double *activities = solver->activities;

  int var = heap[idx];
  heap_idxs[var] = -1;

  if (solver->heap_size == 0)
    return;

  heap[0] = heap[--solver->heap_size];
  var = heap[0];
  heap_idxs[var] = 0;

  /* Heapify */
  int n = solver->heap_size;
  int parent = 0;
  int child1;
  int child2;
  int bestchild;
  int pvar;
  int c1var;
  int c2var;
  int bvar;

  while (1) {
    child1 = (parent << 1) + 1;
    /* Parent has no child */
    if (child1 > n - 1)
      return;

    /* Parent has 1 child */
    else if (child1 == n - 1) {
      pvar = heap[parent];
      c1var = heap[child1];
      if (activities[pvar] >= activities[c1var])
        return;
      bestchild = child1;
      bvar = c1var;
    }

    /* Parent has 2 children */
    else {
      pvar = heap[parent];
      child2 = (parent << 1) + 2;
      c1var = heap[child1];
      c2var = heap[child2];
      double act1 = activities[c1var];
      double act2 = activities[c2var];
      if (act1 >= act2) {
        bestchild = child1;
        bvar = c1var;
        if (activities[pvar] >= act1)
          return;
      }
      else {
        bestchild = child2;
        bvar = c2var;
        if (activities[pvar] >= act2)
          return;
      }
    }

    heap[bestchild] = pvar;
    heap[parent] = bvar;
    heap_idxs[bvar] = parent;
    heap_idxs[pvar] = bestchild;

    parent = bestchild;
  }
}

static void _heap_siftup(Solver *solver, int idx) {
  int *heap = solver->heap;
  int *heap_idxs = solver->heap_idxs;
  double *activities = solver->activities;

  while (1) {
    if (idx == 0)
      break;
    int cvar = heap[idx];
    int pidx = (idx-1) >> 1;
    int pvar = heap[pidx];
    double actc = activities[cvar];
    double actp = activities[pvar];
    if (actc <= actp)
      break;

    heap[pidx] = cvar;
    heap[idx] = pvar;
    heap_idxs[cvar] = pidx;
    heap_idxs[pvar] = idx;

    idx = pidx;
  }
}

void solver_assume(Solver *solver, int slit) {
  int lit = to_lit(slit);
  int var = LIT_VAR(lit);
  ASSERT(solver->vals[var] == -1);
  solver->assumptions[solver->num_assumptions++] = lit;
}

/* The native constraint type of crocodile. */
void solver_add_atleast(Solver *solver, int n, int k, int *slits) {
  ASSERT(n > 0);
  ASSERT(k >= 0);
  ASSERT(k <= n);

  if (k == 0)
    return;
  else if (k == n) {
    for (int i = 0; i < n; i++)
      solver_assume(solver, slits[i]);
  }
  else {
    int *constraint = solver->next_constraint;
    solver->next_constraint += 2 + n + k + 1;
    constraint[0] = n;
    constraint[1] = k;
    for (int i = 0; i < n; i++) {
      int lit = to_lit(slits[i]);
      ASSERT(LIT_VAR(lit) < solver->num_vars);
      constraint[2 + i] = lit;
    }
    for (int j = 0; j < k+1; j++) {
      int nlit = LIT_NEGATE(to_lit(slits[j]));
      constraint[2 + n + j] = solver->watches[nlit];
      solver->watches[nlit] = (int)(constraint - solver->constraints);
    }
  }
}

/* AT_MOST(k; l1 ... ln) is equivalent to AT_LEAST(n-k; ~l1 ... ~ln). */
void solver_add_atmost(Solver *solver, int n, int k, int *slits) {
  ASSERT(n > 0);
  ASSERT(k >= 0);
  ASSERT(k <= n);

  if (k == 0) {
    for (int i = 0; i < n; i++)
      solver_assume(solver, -slits[i]);
  }
  else if (k == n)
    return;
  else {
    int *slits2 = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++)
      slits2[i] = -slits[i];
    solver_add_atleast(solver, n, n - k, slits2);
    free(slits2);
  }
}

void solver_add_equals(Solver *solver, int n, int k, int *slits) {
  solver_add_atleast(solver, n, k, slits);
  solver_add_atmost(solver, n, k, slits);
}

/* `reason_idx` is the offset of the constraint within
   `solver->constraint` that caused the conflict on the last literal
   in the trail. Appends the learnt clause to `solver->constraints`.

   To make implementation simple, the conflict only learns a plain
   clause (i.e. k=1). This is done by weakening the constraints in the
   resolution step (see comment below). */
static bool _resolve_conflict(Solver *solver) {
  solver->cur_stamp++;
  int *constraint = solver->next_constraint;
  int *clits = constraint + 2;
  int *plit = solver->trail + solver->qhead - 1;
  int pvar = LIT_VAR(*plit);
  /* Conflict at top-level */
  ASSERT(solver->vals[pvar] != -1);
  if (VAL_LEVEL(solver->vals[pvar]) == 0)
    return false;
  /* Number of literals in the conflict clause, assigned at the
     current decision level. */
  int dcount = 0;
  /* Max level out of all lower-level stamped literals, or level 0. */
  int level_max = 0;
  bool first_time = true;

  /* The conditions at the start of while loop don't apply to the
     first literal */
  solver->stamps[pvar] = solver->cur_stamp;
  int level = VAL_LEVEL(solver->vals[pvar]);
  if (level < solver->decision_level) {
    if (level > level_max)
      level_max = level;
    *(clits++) = *plit;
  }
  else
    dcount++;
  goto body;

  while (1) {
    pvar = LIT_VAR(*plit);

    /* Non-stamped literals on the trail are not involved in the
       conflict */
    if (solver->stamps[pvar] < solver->cur_stamp)
      goto skip;

    /* The learnt clause has the form '(literals on lower levels) or
       -plit'. This is the first UIP. */
    if (dcount == 1) {
      *(clits++) = LIT_NEGATE(*plit);
      break;
    }

body:
    ASSERT(solver->reasons[*plit] != -1);
    int *reason = solver->constraints + solver->reasons[*plit];
    int n = reason[0];
    int k = reason[1];
    int remaining = n - k;

    /* Derive a (weaker) clause of the form 'plit or l1 or ... or
       l(n-k)' from `reason`, where li's are all assigned false. This
       makes conflict resolution simpler.

       Note that more than n-k literals within the reason may be
       false, but we just choose n-k of them (and stop when remaining
       = 0). */

    for (int i = 0; i < n; i++) {
      int rlit = reason[2 + i];
      int rvar = LIT_VAR(rlit);
      int rval = solver->vals[rvar];
      if (rvar == pvar)
        continue;

      /* Stamp n-k false literals in the clause, and add them to the
         learnt clause if assigned at a lower decision level */
      if (rval != -1 && VAL_SIGN(rval) != LIT_SIGN(rlit)) {
        remaining--;

        if (solver->stamps[rvar] < solver->cur_stamp) {
          solver->activities[rvar] += solver->delta;
          if (solver->heap_idxs[rvar] != -1) {
            _heap_siftup(solver, solver->heap_idxs[rvar]);
#ifdef DEBUG
            _heap_verify(solver);
#endif
          }

          solver->stamps[rvar] = solver->cur_stamp;

          int rlevel = VAL_LEVEL(rval);
          if (rlevel < solver->decision_level) {
            if (rlevel > level_max)
              level_max = rlevel;
            *(clits++) = rlit;
          }
          else
            dcount++;
        }
        /* We have finished constructing the clause */
        if (remaining == 0)
          break;
      }
    }
    ASSERT(remaining == 0);
    if (!first_time)
      dcount--;
skip:
    plit--;

    if (first_time)
      first_time = false;
  }

  /* Backjump to the max level of lower-level stamped literals,
     unassigning all variables along the trail. */
  for (solver->qhead--; solver->qhead > solver->level_idxs[level_max + 1]; solver->qhead--) {
    int lit = solver->trail[solver->qhead - 1];
    int idx = LIT_VAR(lit);
    solver->vals[idx] = -1;
    solver->reasons[lit] = -1;

    /* Re-insert into heap if not inside */
    if (solver->heap_idxs[idx] == -1) {
      solver->heap_size++;
      solver->heap[solver->heap_size - 1] = idx;
      solver->heap_idxs[idx] = solver->heap_size - 1;
      _heap_siftup(solver, solver->heap_size - 1);
#ifdef DEBUG
      _heap_verify(solver);
#endif
    }
  }

  /* Propagate the new clause */
  solver->decision_level = level_max;
  pvar = LIT_VAR(*plit);
  solver->vals[pvar] = (level_max << 1) | ((~*plit) & 1);

  int n = (int)(clits - (constraint + 2));
  if (n == 1)
    solver->reasons[LIT_NEGATE(*plit)] = -1;
  else {
    int offset = (int)(constraint - solver->constraints);
    solver->reasons[LIT_NEGATE(*plit)] = offset;
    /* Form the new clause */
    constraint[0] = n;
    constraint[1] = 1;
    /* constraint[2..2+n-1] is populated via clit */

    /* Add the first two constraints to the watch list */
    int lit = LIT_NEGATE(constraint[2]);
    constraint[2 + n] = solver->watches[lit];
    solver->watches[lit] = offset;

    lit = LIT_NEGATE(constraint[3]);
    constraint[2 + n + 1] = solver->watches[lit];
    solver->watches[lit] = offset;

    solver->next_constraint = constraint + 2 + n + 2;
  }

  solver->trail[solver->qhead] = LIT_NEGATE(*plit);
  solver->qtail = solver->qhead;
  solver->qhead++;
  solver->num_learnt++;

  solver->delta /= 0.99;
  if (solver->delta >= solver->delta_threshold) {
    solver->delta /= solver->delta_threshold;
    for (int var = 0; var < solver->num_vars; var++)
      solver->activities[var] /= solver->delta_threshold;
  }

  return true;
}

void solver_solve(Solver *solver) {
#ifdef DEBUG
  _heap_verify(solver);
#endif
  while (1) {
    if (solver->qtail == solver->qhead) {
      /* Make a decision */
      int dlit;
      int dvar;

      /* Prioritise assumptions first */
      for (int i = 0; i < solver->num_assumptions; i++) {
        int alit = solver->assumptions[i];
        int avar = LIT_VAR(alit);
        int aval = solver->vals[avar];
        if (aval == -1) {
          dlit = alit;
          dvar = LIT_VAR(dlit);
          goto found;
        }
        else if (LIT_SIGN(alit) == VAL_SIGN(solver->vals[avar]))
          continue;
        /* UNSAT under assumptions */
        else {
          solver->is_sat = 0;
          return;
        }
      }

      /* If no assumption, then keep popping from the heap until we
         find an unassigned variable */
      do {
        if (solver->heap_size == 0) {
          solver->is_sat = 1;
          return;
        }
        dvar = solver->heap[0];
        _heap_remove(solver, 0);
#ifdef DEBUG
        _heap_verify(solver);
#endif
      } while (solver->vals[dvar] != -1);
      dlit = (dvar << 1) | 1;

found:
      solver->decision_level++;
      solver->level_idxs[solver->decision_level] = solver->qhead;
      solver->vals[dvar] = (solver->decision_level << 1) | LIT_SIGN(dlit);
      solver->reasons[dlit] = -1;
      solver->trail[solver->qhead++] = dlit;
    }

    else {
advance:
      ASSERT(solver->qtail < solver->qhead);
      /* Literal has been falsified; iterate through literal's watch
         list for potential propagations */
      int lit = solver->trail[solver->qtail++];
      int wcur = solver->watches[lit];
      int wnext = -1;
      /* Used when removing a literal from the watch list */
      int *prevlink = solver->watches + lit;

      while (wcur != -1) {
        solver->num_watch_updates++;
        int n = solver->constraints[wcur];
        int k = solver->constraints[wcur + 1];
        int *lits = solver->constraints + wcur + 2;
        int *watchlinks = solver->constraints + wcur + 2 + n;

        int lit_i;
        int newlit, newlit_i;

        /* Find the index of lit within lits[0..k+1] */
        for (int i = 0; i < k+1; i++) {
          int wlit = lits[i];
          if (wlit == LIT_NEGATE(lit)) {
            lit_i = i;
            break;
          }
        }
        wnext = watchlinks[lit_i];

        /* Find a non-false literal in lits[k+1..n] to swap lit
           with */
        for (newlit_i = k+1; newlit_i < n; newlit_i++) {
          newlit = lits[newlit_i];
          int val = solver->vals[LIT_VAR(newlit)];
          if (val == -1 || VAL_SIGN(val) == LIT_SIGN(newlit))
            goto found2;
        }

        /* No literal found; propagate all watched literals in
           lits[0..k] besides the current one */
        for (int i = 0; i < k+1; i++) {
          if (i == lit_i)
            continue;
          int plit = lits[i];
          int pvar = LIT_VAR(plit);
          int pval = solver->vals[pvar];
          /* Make unassigned watched literal true */
          if (pval == -1) {
            solver->trail[solver->qhead++] = plit;
            solver->reasons[plit] = wcur;
            solver->vals[pvar] = (solver->decision_level << 1) | LIT_SIGN(plit);
          }
          /* A false propagated literal is a conflict; we clausify the
             reasons for plit and -plit and combine them into a new
             clause. */
          else if (VAL_SIGN(pval) != LIT_SIGN(plit)) {
            solver->trail[solver->qhead++] = plit;
            solver->reasons[plit] = wcur;
            if (_resolve_conflict(solver))
              /* This might be a truly nontrivial goto */
              goto advance;
            else {
              solver->is_sat = 0;
              return;
            }
          }
        }
        goto next_iter;

found2:
        /* Swap */
        lits[lit_i] = newlit;
        lits[newlit_i] = LIT_NEGATE(lit);

        /* Add constraint to -newlit's watchlist */
        int nnewlit = LIT_NEGATE(newlit);
        watchlinks[lit_i] = solver->watches[nnewlit];
        solver->watches[nnewlit] = wcur;

        /* Remove constraint from lit's watchlist */
        *prevlink = wnext;
        goto next_iter2;

next_iter:
        prevlink = watchlinks + lit_i;
next_iter2:
        wcur = wnext;
      }
    }
  }
}


/* -----------------------------------------------------------------------------
                                 TEST HARNESS
   ----------------------------------------------------------------------------- */

#ifdef CROCODILE_TEST_HARNESS

/* Some comments on the parser:

   1. Constraint count in line starting with 'p' is not needed, it can
      be set to arbitrary value like -1.

   2. A newline is added to the file contents to simplify the
      implementation of parsing functions, by eliminating checks of
      the form (*c == '\0').

   3. Jumping to the next nonempty line (instead of merely the next
      line) allows for a trailng newline in the input file. Otherwise
      the 'clause line' branch is called for empty lines, which throws
      an error when a '>=' or '<=' is not detected.
 */

#define RED   "\033[31m"
#define RESET "\033[0m"

typedef struct {
  char *s;
  size_t n;
} strview;

int next_nonempty_line(char **buf) {
  int lines_skipped = 0;
  char *c = *buf;
  if (*c == '\0') return 0;
  for (; *c != '\n'; c++) { }
  for (; *c == '\n'; c++) { lines_skipped++; }
  *buf = c;
  return lines_skipped;
}

/* Parse integer if *buf matches the regex
   [ ]*-?[0-9]+[ \n]
   and advance **buf to the last space or newline. */
bool parse_int(char **buf, int *ii) {
  int i = 0;
  bool neg = false;
  char *c = *buf;

  for (; *c == ' '; c++) { }

  if (*c == '-') {
    neg = true;
    c++;
  }

  if (*c < '0' || *c > '9') /* no digits */
    return false;

  for (; *c != ' ' && *c != '\n'; c++) {
    if (*c < '0' || *c > '9')
      return false;
    i = i * 10 + (*c - '0');
  }

  *ii = neg ? -i : i;
  *buf = c;
  return true;
}

/* Parse word if *buf matches the regex
   [ ]*[^ \n]+[ \n]
   and advance **buf to the last space or newline. */
strview parse_word(char **buf) {
  strview sv;
  char *c = *buf;

  for (; *c == ' '; c++) { }
  sv.s = c;
  for (; *c != ' ' && *c != '\n'; c++) { }
  sv.n = c - sv.s;
  *buf = c;

  return sv;
}

bool match_char(char **buf, char c) {
  if (**buf == c) {
    (*buf)++;
    return true;
  }
  else
    return false;
}

bool match_word(char **buf, char *s) {
  char *oldbuf = *buf;
  strview sv = parse_word(buf);
  if (sv.n != strlen(s))
    goto nope;
  if (memcmp(sv.s, s, sv.n) == 0)
    return true;
nope:
  *buf = oldbuf;
  return false;
}

bool parse_cnfp(char *filename, char *buf, Solver *solver) {
  int line_num = 1;
  int num_vars = -1;
  int num_clauses;

  int max_cvars = 1024;
  int *slits = malloc(max_cvars * sizeof(int));

  while (1) {
    if (*buf == '\0') {
      free(slits);
      return true;
    }

    else if (match_char(&buf, 'c'))
      line_num += next_nonempty_line(&buf);

    else if (match_char(&buf, 'p')) {
      if (num_vars != -1) /* a previous p line already parsed */
        goto err;

      if (!match_word(&buf, "cnf+"))
        goto err;
      if (!parse_int(&buf, &num_vars))
        goto err;
      if (!parse_int(&buf, &num_clauses))
        goto err;
      printf("vars    : %d\n", num_vars);
      printf("clauses : %d\n", num_clauses);
      line_num += next_nonempty_line(&buf);

      solver_init_bufs(solver);
      solver_init(solver, num_vars);
    }

    else { /* clause line */
      if (num_vars == -1)
        goto err;

      int n = 0;

      while (1) {
        if (parse_int(&buf, slits + n)) {
          n++;
          if (n == max_cvars) {
            max_cvars <<= 1;
            slits = realloc(slits, max_cvars * sizeof(int));
          }
        }

        else {
          int type;
          if (match_word(&buf, ">="))
            type = 0;
          else if (match_word(&buf, "<="))
            type = 1;
          else
            goto err;

          int k;
          if (!parse_int(&buf, &k))
            goto err;

          switch (type) {
          case 0:
            solver_add_atleast(solver, n, k, slits);
            break;
          case 1:
            solver_add_atmost(solver, n, k, slits);
            break;
          }

          line_num += next_nonempty_line(&buf);
          break;
        }
      }
    }
  }

err:
  free(slits);
  fprintf(stderr, RED "parse error at %s:%d\n" RESET, filename, line_num);
  return false;
}

void run_cnfp(char *filename, char *buf) {
  Solver solver;
  if (!parse_cnfp(filename, buf, &solver))
    return;
  solver_solve(&solver);

  if (solver.is_sat == 1) {
    printf("SATISFIABLE\n");
    for (int i = 0; i < solver.num_vars; i++) {
      if (VAL_SIGN(solver.vals[i]) == 0)
        printf("-");
      printf("%d ", i+1);
    }
    printf("\n");
  }
  else
    printf("UNSATISFIABLE\n");

  solver_free(&solver);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, RED "missing input file\n" RESET);
    return 1;
  }

  char *arg = argv[1];
  int fd = open(arg, O_RDONLY);
  if (fd == -1) {
    fprintf(stderr, RED "failed to open %s - %s\n" RESET, arg, strerror(errno));
    return 1;
  }

  struct stat sb;
  if (fstat(fd, &sb) == -1) {
    fprintf(stderr, RED "failed to stat %s - %s\n" RESET, arg, strerror(errno));
    return 1;
  }

  char *buf = malloc(sb.st_size + 2);
  size_t remaining = sb.st_size;
  ssize_t n_read;
  char *buff = buf;

  while (remaining > 0) {
    n_read = read(fd, buff, remaining);
    if (n_read == -1) {
      fprintf(stderr, RED "failed to read from %s - %s\n" RESET, arg, strerror(errno));
      return 1;
    }
    buff += n_read;
    remaining -= n_read;
  }
  *(buff++) = '\n';
  *buff = '\0';

  run_cnfp(arg, buf);
  free(buf);
  return 0;
}

#endif /* CROCODILE_TEST_HARNESS */
#endif /* CROCODILE_H */