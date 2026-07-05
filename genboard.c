#include <errno.h>
#include <inttypes.h>
#include <stdbit.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>
#include <time.h>
// Includes the ASSERT macro
#include "crocodile/crocodile.h"

/* -----------------------------------------------------------------------------
               PCG32 GENERATOR (BY M.E. O'Neill, slightly adapted)
   ----------------------------------------------------------------------------- */

typedef struct {
  uint64_t state;
  uint64_t inc;
} Pcg;

uint32_t pcg_next(Pcg *pcg0) {
  uint64_t oldstate = pcg0->state;
  pcg0->state = oldstate * 6364136223846793005ULL + (pcg0->inc|1);
  uint32_t xorshifted = (uint32_t) (((oldstate >> 18u) ^ oldstate) >> 27u);
  uint32_t rot = (uint32_t) (oldstate >> 59u);
  return (xorshifted >> rot) | (xorshifted << ((-rot) & 31));
}

static inline uint32_t pcg_next_upto(Pcg *pcg0, uint32_t bound) {
  uint32_t x;
  while ((x = pcg_next(pcg0)) >= 4294967295 / bound * bound) { }
  return x % bound;
}

/* -----------------------------------------------------------------------------
                              BOARD GENERATION CODE
   ----------------------------------------------------------------------------- */

typedef struct {
  int w;
  int h;
  int area;
  int mine_count;
  int *board;

  /* For each square, store the reveal/flagged/border state of each of
     its 8 neighbors. This will be used for the basic solver
     heuristics (before the SAT solver is invoked). */
  unsigned char *revealed_masks;
  unsigned char *flagged_masks;
  unsigned char *interior_masks;
} BoardState;

/* The generator needs to distinguish between flag and reveal
   deductions because it is possible for the solver to deduce all safe
   squares, but not deduce all mines (because they are completely
   surrounded by other mines). Heuristic and SAT deductions count both
   types, and they are a proxy for board difficulty. */
typedef struct {
  int flag_deductions;
  int reveal_deductions;
  int heuristic_deductions;
  int sat_deductions;
} DeductionStats;

#define SQ_MINE         10
/* These are status bits so that we don't destroy the number/mine
   information */
#define SQ_FLAG_BIT     (1 << 30)
#define SQ_REVEAL_BIT   (1 << 29)
#define SQ_FRONTIER_BIT (1 << 28)
#define SQ_FRONTIER2_BIT (1 << 27)
#define SQ_NO_BITS(sq) ((sq) & 0xf)

static inline int adjacent_square(int sq, int w, int h, int dir) {
  int x = sq % w;
  int y = sq / w;
  ASSERT(x >= 0 && x < w);
  ASSERT(y >= 0 && y < h);
  ASSERT(dir >= 0 && dir <= 8);
  if (dir == 0 && x > 0 && y > 0) return sq - w - 1;
  else if (dir == 1 && y > 0) return sq - w;
  else if (dir == 2 && x < w-1 && y > 0) return sq - w + 1;
  else if (dir == 3 && x > 0) return sq - 1;
  else if (dir == 4 && x < w-1) return sq + 1;
  else if (dir == 5 && x > 0 && y < h-1) return sq + w - 1;
  else if (dir == 6 && y < h-1) return sq + w;
  else if (dir == 7 && x < w-1 && y < h-1) return sq + w + 1;
  else if (dir == 8) return sq;
  else return -1;
}

void bs_init(BoardState *bs, int w, int h, int mine_count) {
  bs->w = w;
  bs->h = h;
  int area = w * h;
  bs->area = area;
  bs->mine_count = mine_count;
  bs->board = malloc(area * sizeof(int));
  bs->revealed_masks = malloc(area);
  bs->flagged_masks = malloc(area);
  bs->interior_masks = malloc(area);
}

void bs_copy(BoardState *bs, BoardState *obs) {
  bs->w = obs->w;
  bs->h = obs->h;
  int area = obs->area;
  bs->area = area;
  bs->mine_count = obs->mine_count;
  memcpy(bs->board, obs->board, area * sizeof(int));
  memcpy(bs->revealed_masks, obs->revealed_masks, area);
  memcpy(bs->flagged_masks, obs->flagged_masks, area);
  memcpy(bs->interior_masks, obs->interior_masks, area);
}

void bs_free(BoardState *bs) {
  free(bs->board);
  free(bs->revealed_masks);
  free(bs->flagged_masks);
  free(bs->interior_masks);
}

void bs_debug(BoardState *bs) {
  int w = bs->w;
  int area = bs->area;
  int *board = bs->board;

  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];
    if (square & SQ_REVEAL_BIT)
      fprintf(stderr, "\033[32m");
    else if (square & SQ_FLAG_BIT)
      fprintf(stderr, "\033[31m");

    if (SQ_NO_BITS(square) == SQ_MINE)
      fprintf(stderr, "X");
    else
      fprintf(stderr, "%c", '0' + SQ_NO_BITS(square));

    fprintf(stderr, "\033[0m");
    if (sq % w == w - 1)
      fprintf(stderr, "\n");
  }
}

/* -----------------------------------------------------------------------------
                              MINE PLACEMENT CODE
   ----------------------------------------------------------------------------- */

int cmp_int(const void *x, const void *y) {
  int a = *(int *)x;
  int b = *(int *)y;
  return a < b ? -1 : a > b ? 1 : 0;
}

/* Generate a `h`-by-`w` board with `mine_count` mines placed, in such
   a way every non-mine square is king-move adjacent to a mine. Note
   that `mine_count` has to be large enough for such an arrangement to
   be possible -- otherwise the output is invalid. `buf` is a scratch
   buffer that is expected to hold at least `h*w + mine_count`
   integers.

   The output is written to a length `h*w` array board. */
void place_mines(BoardState *bs, int *buf, Pcg *pcg) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;

  ASSERT(w >= 3 && h >= 3);
  ASSERT(mine_count > 0);

  /* Each square counts how many times it is covered by king-move-adjacent mines */
  int *covered_counts = board;
  for (int i = 0; i < area; i++)
    covered_counts[i] = 0;
  /* The indices of uncovered squares after doing an initial mine placement */
  int *mines = buf;
  int *uncovered = buf + mine_count;
  int mines_placed = 0;

  /* Initial random placement -- it might not satisfy the
     king-move-adjacency condition yet. */
  for (int sq = 0; sq < area; sq++) {
    if (mines_placed == mine_count)
      break;

    if ((int) pcg_next_upto(pcg, area - sq) <= mine_count - mines_placed) {
      /* Place a mine */
      mines[mines_placed++] = sq;
      /* Cover the cells in the 3x3 grid. */
      for (int dir = 0; dir < 9; dir++) {
        int asq = adjacent_square(sq, w, h, dir);
        if (asq != -1)
          covered_counts[asq]++;
      }
    }
  }

  /* Adjust the initial random placement to obtain a valid
     arrangement, by repeatedly adding mines next to uncovered squares
     and removing redundant mines. */
  int uncovered_count;
  while (1) {
    uncovered_count = 0;
    /* Populate uncovered array */
    for (int sq = 0; sq < area; sq++) {
      if (covered_counts[sq] == 0)
        uncovered[uncovered_count++] = sq;
    }

    ASSERT(uncovered_count <= area - mine_count);
    if (uncovered_count == 0)
      break;

    /* Place a necessary mine at a random uncovered square */
    int usq = uncovered[pcg_next_upto(pcg, uncovered_count)];
    for (int dir = 0; dir < 9; dir++) {
      int asq = adjacent_square(usq, w, h, dir);
      if (asq != -1)
        covered_counts[asq]++;
    }

    /* Look for a redundant mine. Redundant square means all squares
       in surrounding 3x3 grid are covered more than once. */
    for (int i = 0; i < mines_placed; i++) {
      bool is_redundant = true;
      int msq = mines[i];

      for (int dir = 0; dir < 9; dir++) {
        int asq = adjacent_square(msq, w, h, dir);
        if (asq != -1 && covered_counts[asq] == 1) {
          is_redundant = false;
          break;
        }
      }

      if (is_redundant) {
        /* Uncover the cells in the 3x3 grid */
        for (int dir = 0; dir < 9; dir++) {
          int asq = adjacent_square(msq, w, h, dir);
          if (asq != -1)
            covered_counts[asq]--;
        }

        /* Replace the redundant mine with the necessary mine */
        mines[i] = usq;
        break;
      }
    }
  }

  /* board = covered_counts, so all the other squares are populated
     already */
  for (int i = 0; i < mine_count; i++)
    board[mines[i]] = SQ_MINE;
}

/* -----------------------------------------------------------------------------
                            REVEAL PLACEMENT CODE
   ----------------------------------------------------------------------------- */

int get_frontier(BoardState *bs, int *frontier) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int *board = bs->board;

  for (int sq = 0; sq < area; sq++)
    board[sq] &= ~SQ_FRONTIER_BIT;

  int k = 0;
  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];
    if (square & SQ_REVEAL_BIT) {
      for (int dir = 0; dir < 8; dir++) {
        int asq = adjacent_square(sq, w, h, dir);
        if (asq == -1)
          continue;
        int asquare = board[asq];
        if (!(asquare & SQ_FLAG_BIT) &&
            !(asquare & SQ_FRONTIER_BIT) &&
            !(asquare & SQ_REVEAL_BIT)) {
          frontier[k++] = asq;
          board[asq] |= SQ_FRONTIER_BIT;
        }
      }
    }
  }
  return k;
}

int get_frontier2(BoardState *bs, int *frontier) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int *board = bs->board;

  for (int sq = 0; sq < area; sq++) {
    board[sq] &= ~SQ_FRONTIER_BIT;
    board[sq] &= ~SQ_FRONTIER2_BIT;
  }

  int bit1 = SQ_REVEAL_BIT;
  int bit2 = SQ_FRONTIER_BIT;
  int k = 0;
relax:
  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];
    if (square & bit1) {
      for (int dir = 0; dir < 8; dir++) {
        int asq = adjacent_square(sq, w, h, dir);
        if (asq == -1)
          continue;
        int asquare = board[asq];
        if (!(asquare & SQ_REVEAL_BIT) &&
            !(asquare & bit1) &&
            !(asquare & bit2)) {
          frontier[k++] = asq;
          ASSERT(k < area);
          board[asq] |= bit2;
        }
      }
    }
  }

  if (bit1 == SQ_REVEAL_BIT) {
    bit1 = SQ_FRONTIER_BIT;
    bit2 = SQ_FRONTIER2_BIT;
    goto relax;
  }

  return k;
}

void solver_from_board(BoardState *bs, Solver *solver) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;

  int slits[area];
  bool status = solver_init(solver, area);
  ASSERT(status);

  /* Global mine count */
  for (int sq = 0; sq < area; sq++)
    slits[sq] = sq + 1;
  solver_add_equals(solver, area, mine_count, slits);

  /* Square clues */
  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];

    if (square & SQ_REVEAL_BIT) {
      int n = 0;
      for (int dir = 0; dir < 8; dir++) {
        int adj = adjacent_square(sq, w, h, dir);
        if (adj != -1)
          slits[n++] = adj + 1;
      }
      solver_add_equals(solver, n, SQ_NO_BITS(square), slits);
      solver_assume(solver, -(sq + 1));
    }

    else if (square & SQ_FLAG_BIT)
      solver_assume(solver, sq + 1);
  }
}

void set_neighbor_masks(int sq, BoardState *bs, unsigned char *masks) {
  int w = bs->w;
  int h = bs->h;

  for (int dir = 0; dir < 8; dir++) {
    int asq = adjacent_square(sq, w, h, dir);
    if (asq == -1)
      continue;
    /* This is correct, think about it a bit */
    masks[asq] |= (1 << dir);
  }
}

void unset_neighbor_masks(int sq, BoardState *bs, unsigned char *masks) {
  int w = bs->w;
  int h = bs->h;

  for (int dir = 0; dir < 8; dir++) {
    int asq = adjacent_square(sq, w, h, dir);
    if (asq == -1)
      continue;
    /* This is correct, think about it a bit */
    masks[asq] &= ~(1 << dir);
  }
}

void reveal_masked(int sq, BoardState *bs, unsigned char mask) {
  int w = bs->w;
  int h = bs->h;
  int *board = bs->board;
  unsigned char *revealed_masks = bs->revealed_masks;

  for (int dir = 7; dir >= 0; dir--) {
    if (mask & 1) {
      int asq = adjacent_square(sq, w, h, dir);
      ASSERT(!(board[asq] & SQ_REVEAL_BIT));
      ASSERT(SQ_NO_BITS(board[asq]) != SQ_MINE);
      board[asq] |= SQ_REVEAL_BIT;
      set_neighbor_masks(asq, bs, revealed_masks);
    }
    mask >>= 1;
  }
}

void flag_masked(int sq, BoardState *bs, unsigned char mask) {
  int w = bs->w;
  int h = bs->h;
  int *board = bs->board;
  unsigned char *flagged_masks = bs->flagged_masks;

  for (int dir = 7; dir >= 0; dir--) {
    if (mask & 1) {
      int asq = adjacent_square(sq, w, h, dir);
      ASSERT(!(board[asq] & SQ_FLAG_BIT));
      ASSERT(SQ_NO_BITS(board[asq]) == SQ_MINE);
      board[asq] |= SQ_FLAG_BIT;
      set_neighbor_masks(asq, bs, flagged_masks);
    }
    mask >>= 1;
  }
}

/* Takes in two neighbour sets represented as bitmasks centered around
   two squares, and compute the set difference, represented as a
   bitmask centered around the first square. */
unsigned char difference_mask(int sq, unsigned char mask, int osq, unsigned char omask, BoardState *bs) {
  int w = bs->w;
  int h = bs->h;
  unsigned char dmask = 0;

  for (int dir = 7; dir >= 0; dir--) {
    if (mask & 1) {
      int asq = adjacent_square(sq, w, h, dir);
      bool present = false;
      unsigned char omsk = omask;

      for (int odir = 7; odir >= 0; odir--) {
        if (omsk & 1) {
          int aosq = adjacent_square(osq, w, h, odir);
          if (asq == aosq) {
            present = true;
            break;
          }
        }
        omsk >>= 1;
      }

      if (!present)
        dmask |= (1 << (7 - dir));
    }
    mask >>= 1;
  }

  return dmask;
}

void apply_heuristics(BoardState *bs, DeductionStats *stats) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int *board = bs->board;
  unsigned char *revealed_masks = bs->revealed_masks;
  unsigned char *flagged_masks = bs->flagged_masks;
  unsigned char *interior_masks = bs->interior_masks;

  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];
    if (!(square & SQ_REVEAL_BIT))
      continue;

    unsigned char rmask = revealed_masks[sq];
    unsigned char fmask = flagged_masks[sq];
    unsigned char imask = interior_masks[sq];

    ASSERT(!(rmask & fmask));
    unsigned char unknown_mask = imask & ~fmask & ~rmask;
    int unknown_count = stdc_count_ones_uc(unknown_mask);
    int effective_count = SQ_NO_BITS(square) - stdc_count_ones_uc(fmask);
    ASSERT(effective_count >= 0);

    /* -------- 1-square deductions -------- */

    if (unknown_count == 0)
      goto twosquare;

    /* If effective count = 0, then all unknown squares are safe. */
    if (effective_count == 0) {
      reveal_masked(sq, bs, unknown_mask);
      int n = stdc_count_ones_uc(unknown_mask);
      stats->reveal_deductions += n;
      stats->heuristic_deductions += n;
    }

    /* If effective count = unknown count, then all unknown squares
       are mines. */
    if (effective_count == unknown_count) {
      flag_masked(sq, bs, unknown_mask);
      int n = stdc_count_ones_uc(unknown_mask);
      stats->flag_deductions += n;
      stats->heuristic_deductions += n;
    }

    /* -------- 2-square deductions -------- */

twosquare:
    int x = sq % w;
    int y = sq / w;

    /* Only pairs of squares at most 2 king moves apart can yield a
       deduction. By symmetry, for each square we need check at most
       (25-1)/2 = 12 candidate counterparts. */

    int dx = 1;
    int dy = 0;
    for (; dy <= 2; dy++) {
      for (; dx <= 2; dx++) {
        /* These have to be constantly updated as deductions in
           adjacent squares affect this squares' masks */
        rmask = revealed_masks[sq];
        fmask = flagged_masks[sq];
        unknown_mask = imask & ~fmask & ~rmask;
        unknown_count = stdc_count_ones_uc(unknown_mask);
        effective_count = SQ_NO_BITS(square) - stdc_count_ones_uc(fmask);

        int ox = x + dx;
        int oy = y + dy;
        if (ox < 0 || ox > w-1 || oy < 0 || oy > h-1)
          continue;

        int osq = oy * w + ox;
        int osquare = board[osq];
        if (!(osquare & SQ_REVEAL_BIT))
          continue;

        unsigned char o_rmask = revealed_masks[osq];
        unsigned char o_fmask = flagged_masks[osq];
        unsigned char o_imask = interior_masks[osq];
        unsigned char o_unknown_mask = o_imask & ~o_fmask & ~o_rmask;
        int o_effective_count = SQ_NO_BITS(osquare) - stdc_count_ones_uc(o_fmask);
        unsigned char dmask;
        unsigned char dmask2;

        int num_diff = effective_count - o_effective_count;

        /* Set-difference rule: if squares A and B have neighbor sets
           S1, S2 and |S1\S2| = A-B, then all squares in S1\S2 are
           mines. */

        if (num_diff < 0) {
          dmask = difference_mask(osq, o_unknown_mask, sq, unknown_mask, bs);
          if ((int) stdc_count_ones_uc(dmask) == -num_diff) {
            flag_masked(osq, bs, dmask);
            int n = stdc_count_ones_uc(dmask);
            stats->flag_deductions += n;
            stats->heuristic_deductions += n;
          }
        }

        else if (num_diff > 0) {
          dmask = difference_mask(sq, unknown_mask, osq, o_unknown_mask, bs);
          if ((int) stdc_count_ones_uc(dmask) == num_diff) {
            flag_masked(sq, bs, dmask);
            int n = stdc_count_ones_uc(dmask);
            stats->flag_deductions += n;
            stats->heuristic_deductions += n;
          }
        }

        /* Subset rule: if squares A and B are equal and have neighbor
           sets S1 subset S2, then all squares in S2\S1 are safe. */

        else {
          dmask = difference_mask(sq, unknown_mask, osq, o_unknown_mask, bs);
          dmask2 = difference_mask(osq, o_unknown_mask, sq, unknown_mask, bs);

          if (stdc_count_ones_uc(dmask) == 0) {
            reveal_masked(osq, bs, dmask2);
            int n = stdc_count_ones_uc(dmask2);
            stats->reveal_deductions += n;
            stats->heuristic_deductions += n;
          }
          else if (stdc_count_ones_uc(dmask2) == 0) {
            reveal_masked(sq, bs, dmask);
            int n = stdc_count_ones_uc(dmask);
            stats->reveal_deductions += n;
            stats->heuristic_deductions += n;
          }
        }
      }
      dx = -2;
    }
  }
}

/* From a given board state (with some reveals and flags), keep making
   deductions and revealing new squares, until no more new deductions
   can be made. */
void solver_grind(BoardState *bs, Solver *solver, DeductionStats *stats) {
  int area = bs->area;
  int *board = bs->board;
  unsigned char *revealed_masks = bs->revealed_masks;
  unsigned char *flagged_masks = bs->flagged_masks;

  stats->flag_deductions = 0;
  stats->reveal_deductions = 0;
  stats->heuristic_deductions = 0;
  stats->sat_deductions = 0;

  int *frontier = malloc(area * sizeof(int));

  while (1) {
    int d;
    int newd;
    do {
      d = stats->reveal_deductions + stats->flag_deductions;
      apply_heuristics(bs, stats);
      newd = stats->reveal_deductions + stats->flag_deductions;
    } while (newd - d > 0);

again:
    /* Find any consistent arrangement of mines in the frontier, given
       the current reveals */
    solver_from_board(bs, solver);
    solver_solve(solver);
    ASSERT(solver->is_sat == 1);

    int k = get_frontier(bs, frontier);

    /* No frontier means the board is completely solved */
    if (k == 0)
      break;

    /* valid_vals[i] is either 0, 1 or 2 depending on whether the
       current reveal state is consistent with square i being safe, a
       mine, or both. We can skip squares where valid_vals is set to 2
       from solving a previous square. */
    int valid_vals[k];
    for (int i = 0; i < k; i++)
      valid_vals[i] = solver->vals[frontier[i]] & 1;

    /* For each frontier square, re-solve under the assumption of the
       negation of its value in the model. If it's unsatisfiable, that
       means the square can be deduced. */
    for (int i = 0; i < k; i++) {
      if (valid_vals[i] == 2)
        continue;

      int fsq = frontier[i];
      int slit = (valid_vals[i] & 1) ? (fsq+1) : -(fsq+1);
      solver_from_board(bs, solver);
      solver_assume(solver, -slit);
      solver_solve(solver);

      if (solver->is_sat == 1) {
        for (int j = i+1; j < k; j++) {
          int val = solver->vals[frontier[j]] & 1;
          if (val != valid_vals[j])
            valid_vals[j] = 2;
        }
      }

      else {
        int dsq;

        if (slit < 0) {
          dsq = -slit - 1;
          ASSERT(SQ_NO_BITS(board[dsq]) != SQ_MINE);
          board[dsq] |= SQ_REVEAL_BIT;
          set_neighbor_masks(dsq, bs, revealed_masks);
          stats->reveal_deductions++;
        }

        else {
          dsq = slit - 1;
          ASSERT(SQ_NO_BITS(board[dsq]) == SQ_MINE);
          board[dsq] |= SQ_FLAG_BIT;
          set_neighbor_masks(dsq, bs, flagged_masks);
          stats->flag_deductions++;
        }

        stats->sat_deductions++;
        goto again;
      }
    }

    break;
  }

  free(frontier);
}

/* Generate a set of sufficient initial clues incrementally, as follows:
   1. Initialise the algorithm with two randomly placed clues.

   2. Suppose current clueset is S. Every unrevealed square that is <=
      2 king moves from a clue is a candidate for the next clue. For
      each candidate square s, make as much progress as possible on
      the clueset S + {s} (in solver_grind()), using a combination of
      heuristics and SAT solving.

   3. Pick s that gives the most progress and add it to S. If board is
      completely solved, then return S. */
int forward_pass(BoardState *bs, int *clues, Solver *solver, Pcg *pcg) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;
  unsigned char *revealed_masks = bs->revealed_masks;
  unsigned char *flagged_masks = bs->flagged_masks;

  int square;
  /* Initial clues so the solver has something to work with */
  int num_clues = 2;
  /* The forward pass doesn't care about breakdown into heuristic /
     SAT, that is for backward pass to compute with the finalised
     clueset */

  /* The next revealed square */
  int csq;

  /* First reveal in random spot */
  pcg_next(pcg); /* I noticed that if the high bits of the initial state are 0, then
                    two pcg_next() iterations are needed for noise to show up in the
                    high bits. */
  do {
    csq = pcg_next_upto(pcg, area);
    square = board[csq];
  } while (square == SQ_MINE);
  int x1 = csq % w;
  int y1 = csq / w;
  clues[0] = csq;
  board[csq] |= SQ_REVEAL_BIT;
  set_neighbor_masks(csq, bs, revealed_masks);

  /* Second reveal, distance <= 3 away */
  while (1) {
    csq = pcg_next_upto(pcg, area);
    square = board[csq];
    if ((square & SQ_REVEAL_BIT) ||
        SQ_NO_BITS(square) == SQ_MINE)
      continue;

    int x2 = csq % w;
    int y2 = csq / w;
    int dx = x1 > x2 ? x1-x2 : x2-x1;
    int dy = y1 > y2 ? y1-y2 : y2-y1;
    int dist = dx + dy;
    if (dist > 3)
      continue;

    clues[1] = csq;
    board[csq] |= SQ_REVEAL_BIT;
    set_neighbor_masks(csq, bs, revealed_masks);
    break;
  }

  int frontier2[area];
  int max_new_deductions;
  int total_reveal_deductions = 0;

  /* Can initialise mine_count with dummy value because it will be
     copied directly from another BoardState */
  BoardState old_bs;
  bs_init(&old_bs, w, h, 0);
  BoardState best_bs;
  bs_init(&best_bs, w, h, 0);

  while (1) {
    DeductionStats best_stats;
    best_stats.reveal_deductions = 0;
    bs_copy(&old_bs, bs);
    max_new_deductions = -1;

    /* Iterate through all non-mine squares at distance <= 2 from a
       revealed square. We will next reveal the one that results in the
       most solver deductions. */

    /* BUG: cannot make progress if there is an unrevealed connected
       component isolated by mines. This happens rarely. */

    int k = get_frontier2(bs, frontier2);

    for (int i = 0; i < k; i++) {
      int sq = frontier2[i];
      square = board[sq];

      if (SQ_NO_BITS(square) == SQ_MINE || (square & SQ_REVEAL_BIT))
        continue;

      /* Tentatively try a new clue */
      board[sq] |= SQ_REVEAL_BIT;
      set_neighbor_masks(sq, bs, revealed_masks);

      solver_from_board(bs, solver);

      DeductionStats tmp_stats;
      solver_grind(bs, solver, &tmp_stats);
      ASSERT(tmp_stats.flag_deductions + tmp_stats.reveal_deductions ==
             tmp_stats.heuristic_deductions + tmp_stats.sat_deductions);
      int d = tmp_stats.flag_deductions + tmp_stats.reveal_deductions;

      if (d > max_new_deductions) {
        max_new_deductions = d;
        csq = sq;
        bs_copy(&best_bs, bs);
        memcpy(&best_stats, &tmp_stats, sizeof(DeductionStats));
      }

      /* Undo the partially solved board */
      bs_copy(bs, &old_bs);
    }

    bs_copy(bs, &best_bs);
    total_reveal_deductions += best_stats.reveal_deductions;

    bs_debug(bs); fprintf(stderr, "\n");

    clues[num_clues++] = csq;

    ASSERT(num_clues + total_reveal_deductions + mine_count <= area);
    if (num_clues + total_reveal_deductions + mine_count == area) {
      bs_free(&best_bs);
      bs_free(&old_bs);

      /* We have a sufficient set of clues, now remove all the
         deductions and flags for the backpass */
      for (int sq = 0; sq < area; sq++) {
        if (board[sq] & SQ_FLAG_BIT) {
          board[sq] &= ~SQ_FLAG_BIT;
          unset_neighbor_masks(sq, bs, flagged_masks);
        }
        else if (board[sq] & SQ_REVEAL_BIT) {
          board[sq] &= ~SQ_REVEAL_BIT;
          unset_neighbor_masks(sq, bs, revealed_masks);
        }
      }
      for (int i = 0; i < num_clues; i++) {
        int sq = clues[i];
        board[sq] |= SQ_REVEAL_BIT;
        set_neighbor_masks(sq, bs, revealed_masks);
      }

      return num_clues;
    }
  }
}

/* Prune the clueset generated from forward_pass(), by repeatedly
   removing clues until the solver can no longer completely solve the
   board. Also compute deduction statistics for final clueset to gauge
   board difficulty. */
int backward_pass(BoardState *bs, int *clues, int num_clues, DeductionStats *stats, Solver *solver) {
  int w = bs->w;
  int h = bs->h;
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;
  unsigned char *revealed_masks = bs->revealed_masks;

  BoardState old_bs;
  bs_init(&old_bs, w, h, 0);
  bs_copy(&old_bs, bs);
  bs_debug(bs); fprintf(stderr, "\n");

  stats->heuristic_deductions = 0;
  stats->sat_deductions = 0;
  DeductionStats tmp_stats;

  solver_grind(bs, solver, &tmp_stats);
  memcpy(stats, &tmp_stats, sizeof(DeductionStats));
  bs_copy(bs, &old_bs);

  for (int i = 0; i < num_clues; i++) {
    int csq = clues[i];
    board[csq] &= ~SQ_REVEAL_BIT;
    unset_neighbor_masks(csq, bs, revealed_masks);

    solver_grind(bs, solver, &tmp_stats);

    ASSERT(tmp_stats.flag_deductions + tmp_stats.reveal_deductions ==
           tmp_stats.heuristic_deductions + tmp_stats.sat_deductions);

    if (num_clues - 1 + tmp_stats.reveal_deductions + mine_count == area) {
      clues[i] = clues[num_clues - 1];
      num_clues--;
      i--;

      bs_copy(bs, &old_bs);

      board[csq] &= ~SQ_REVEAL_BIT;
      unset_neighbor_masks(csq, bs, revealed_masks);

      bs_debug(bs); fprintf(stderr, "\n");
      bs_copy(&old_bs, bs);
      memcpy(stats, &tmp_stats, sizeof(DeductionStats));
    }
    else {
      bs_copy(bs, &old_bs);
    }
  }

  bs_debug(bs); fprintf(stderr, "\n");
  bs_free(&old_bs);
  return num_clues;
}

/* -----------------------------------------------------------------------------
                                     MAIN
   ----------------------------------------------------------------------------- */

int _compare_int(const void *x, const void *y) {
  int a = *((int *) x);
  int b = *((int *) y);
  return a < b ? -1 : a == b ? 0 : 1;
}

int main(int argc, char **argv) {
  if (argc != 6) {
    fprintf(stderr, "usage: genboard <w> <h> <mines> <board_seed> <solve_seed>\n");
    return 1;
  }

  BoardState bs;
  int w = (int) strtoul(argv[1], NULL, 10);
  int h = (int) strtoul(argv[2], NULL, 10);
  int area = w * h;
  int mine_count = (int) strtoul(argv[3], NULL, 10);
  bs_init(&bs, w, h, mine_count);

  Pcg board_pcg;
  uint64_t board_seed = strtoull(argv[4], NULL, 10);
  board_pcg.state = board_seed;
  board_pcg.inc = 676767676767676767ULL;

  Pcg solve_pcg;
  uint64_t solve_seed = strtoull(argv[5], NULL, 10);
  solve_pcg.state = solve_seed;
  solve_pcg.inc = 676767676767676767ULL;

  int *buf = malloc((bs.area + bs.mine_count) * sizeof(int));

  for (int sq = 0; sq < bs.area; sq++) {
    bs.revealed_masks[sq] = 0;
    bs.flagged_masks[sq] = 0;

    unsigned char imask = 0b11111111;
    int x = sq % bs.w;
    int y = sq / bs.w;
    if (x == 0)
      imask &= 0b01101011;
    else if (x == bs.w - 1)
      imask &= 0b11010110;
    if (y == 0)
      imask &= 0b00011111;
    else if (y == bs.h - 1)
      imask &= 0b11111000;
    bs.interior_masks[sq] = imask;
  }

  place_mines(&bs, buf, &board_pcg);

  Solver solver;
  solver_init_bufs(&solver);

  fprintf(stderr, "FORWARD PASS\n");
  int num_clues;
  int *clues = malloc(area * sizeof(int));
  num_clues = forward_pass(&bs, clues, &solver, &solve_pcg);

  fprintf(stderr, "BACKWARD PASS\n");
  DeductionStats stats;
  num_clues = backward_pass(&bs, clues, num_clues, &stats, &solver);

  qsort(clues, num_clues, sizeof(int), _compare_int);

  printf("{\"w\": %d, \"h\": %d, \"board\": \"", w, h);
  for (int sq = 0; sq < area; sq++) {
    int square = bs.board[sq];
    if (SQ_NO_BITS(square) == SQ_MINE)
      printf("!");
    else
      printf("%d", SQ_NO_BITS(square));
  }
  printf("\", \"reveals\": [");
  for (int i = 0; i < num_clues - 1; i++)
    printf("%d, ", clues[i]);
  printf("%d]", clues[num_clues - 1]);
  float difficulty = (float)stats.sat_deductions / (stats.sat_deductions + stats.heuristic_deductions);
  printf(", \"mines\": %d, \"board_seed\": %" PRIu64 ", \"solve_seed\": %" PRIu64 ", \"difficulty\": %f}\n",
         mine_count, board_seed, solve_seed, difficulty);

  solver_free(&solver);
  bs_free(&bs);
  free(clues);
  free(buf);
}