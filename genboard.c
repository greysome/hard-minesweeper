#include <errno.h>
#include <inttypes.h>
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
  int num_reveals;
  int *reveals;

  /* For each square, store the reveal/flagged/border state of each of
     its 8 neighbors. This will be used for the basic solver
     heuristics (before the SAT solver is invoked). */
  char *revealed_masks;
  char *flagged_masks;
  char *border_masks;
} BoardState;

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
  else if (dir == 4) return sq;
  else if (dir == 5 && x < w-1) return sq + 1;
  else if (dir == 6 && x > 0 && y < h-1) return sq + w - 1;
  else if (dir == 7 && y < h-1) return sq + w;
  else if (dir == 8 && x < w-1 && y < h-1) return sq + w + 1;
  else return -1;
}

void board_debug(BoardState *bs) {
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

void debug_solve(BoardState *bs, Solver *solver) {
  int w = bs->w;
  int area = bs->area;
  int *board = bs->board;

  for (int sq = 0; sq < area; sq++) {
    int square = board[sq];
    if (square & SQ_REVEAL_BIT)
      fprintf(stderr, "\033[34m");
    else if ((solver->vals[sq] & 1) == 1)
      fprintf(stderr, "\033[31m");
    else
      fprintf(stderr, "\033[32m");

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
      for (int dir = 0; dir < 9; dir++) {
        if (dir == 4)
          dir++;
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
      for (int dir = 0; dir < 9; dir++) {
        if (dir == 4)
          dir++;
        int asq = adjacent_square(sq, w, h, dir);
        if (asq == -1)
          continue;
        int asquare = board[asq];
        if (!(asquare & SQ_FLAG_BIT) &&
            !(asquare & SQ_REVEAL_BIT) &&
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
      for (int dir = 0; dir < 9; dir++) {
        if (dir == 4)
          dir++;
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

/* From a given board state (with some reveals and flags), keep making
   deductions and revealing new squares, until no more new deductions
   can be made. */
int solver_grind(BoardState *bs, Solver *solver) {
  int area = bs->area;
  int *board = bs->board;

  int total_deductions = 0;

  /* The board is updated as the solver makes deductions. This
     progress has to be undone at the end. */
  int old_board[area]; /* Sorry, VLAs are too convenient */
  memcpy(old_board, board, area * sizeof(int));

  while (1) {
again:
    /* Find any consistent arrangement of mines in the frontier, given
       the current reveals */
    solver_from_board(bs, solver);
    solver_solve(solver);
    ASSERT(solver->is_sat == 1);

    int frontier[area];
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
        if (slit < 0) {
          ASSERT(SQ_NO_BITS(board[-slit-1]) != SQ_MINE);
          board[-slit-1] |= SQ_REVEAL_BIT;
          total_deductions++;
        }
        else {
          ASSERT(SQ_NO_BITS(board[slit-1]) == SQ_MINE);
          board[slit-1] |= SQ_FLAG_BIT;
        }
        goto again;
      }
    }

    break;
  }

  memcpy(board, old_board, area * sizeof(int));
  return total_deductions;
}

int forward_pass(BoardState *bs, Solver *solver, Pcg *pcg) {
  int w = bs->w;
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;
  int *reveals = bs->reveals;

  int square;
  int num_reveals = 0;
  int next_reveal;

  pcg_next(pcg);
  do {
    next_reveal = pcg_next_upto(pcg, area);
    square = board[next_reveal];
  } while (square == SQ_MINE);

  int x1 = next_reveal % w;
  int y1 = next_reveal / w;
  reveals[num_reveals++] = next_reveal;
  board[next_reveal] |= SQ_REVEAL_BIT;

  while (1) {
    next_reveal = pcg_next_upto(pcg, area);
    square = board[next_reveal];
    if ((square & SQ_REVEAL_BIT) ||
        SQ_NO_BITS(square) == SQ_MINE)
      continue;

    int x2 = next_reveal % w;
    int y2 = next_reveal / w;
    int dx = x1 > x2 ? x1-x2 : x2-x1;
    int dy = y1 > y2 ? y1-y2 : y2-y1;
    int dist = dx + dy;
    if (dist > 3)
      continue;

    reveals[num_reveals++] = next_reveal;
    board[next_reveal] |= SQ_REVEAL_BIT;
    break;
  }

  int frontier2[area];
  int max_deductions;

again:
  max_deductions = -1;
  /* Iterate through all non-mine squares at distance <= 2 from a
     revealed square. We will next reveal the one that results in the
     most solver deductions. */

  board_debug(bs);
  printf("\n");
  int k = get_frontier2(bs, frontier2);

  for (int i = 0; i < k; i++) {
    int sq = frontier2[i];
    square = board[sq];
    if (SQ_NO_BITS(square) == SQ_MINE || (square & SQ_REVEAL_BIT))
      continue;
    board[sq] |= SQ_REVEAL_BIT;
    solver_from_board(bs, solver);
    int deductions = solver_grind(bs, solver);
    if (deductions > max_deductions) {
      max_deductions = deductions;
      next_reveal = sq;
    }
    board[sq] &= ~SQ_REVEAL_BIT;
  }

  if (max_deductions <= 2) {
    /* Solver could make no progress, choose a random square in the
       frontier2 */
    do {
      next_reveal = frontier2[pcg_next_upto(pcg, k)];
      square = board[next_reveal];
    } while (SQ_NO_BITS(square) == SQ_MINE);
  }

  reveals[num_reveals++] = next_reveal;
  board[next_reveal] |= SQ_REVEAL_BIT;

  if (num_reveals + max_deductions + mine_count == area)
    return num_reveals;

  goto again;
}

void backward_pass(BoardState *bs, Solver *solver) {
  int area = bs->area;
  int mine_count = bs->mine_count;
  int *board = bs->board;
  int num_reveals = bs->num_reveals;
  int *reveals = bs->reveals;

  /* Repeatedly remove reveals until the solver can't solve it */
  for (int i = 0; i < num_reveals; i++) {
    int reveal = reveals[i];
    board[reveal] &= ~SQ_REVEAL_BIT;
    int deductions = solver_grind(bs, solver);

    if (num_reveals - 1 + deductions + mine_count == area) {
      reveals[i] = reveals[num_reveals - 1];
      num_reveals--;
      i--;
      board_debug(bs);
      printf("\n");
    }
    else
      board[reveal] |= SQ_REVEAL_BIT;
  }
}

/* -----------------------------------------------------------------------------
                                     MAIN
   ----------------------------------------------------------------------------- */

int main(int argc, char **argv) {
  if (argc != 6) {
    fprintf(stderr, "usage: genboard <w> <h> <mines> <board_seed> <solve_seed>\n");
    return 1;
  }

  BoardState bs;
  bs.w = (int) strtoul(argv[1], NULL, 10);
  bs.h = (int) strtoul(argv[2], NULL, 10);
  bs.area = bs.w * bs.h;
  bs.mine_count = (int) strtoul(argv[3], NULL, 10);

  Pcg board_pcg;
  board_pcg.state = strtoull(argv[4], NULL, 10);
  board_pcg.inc = 676767676767676767ULL;

  Pcg solve_pcg;
  solve_pcg.state = strtoull(argv[5], NULL, 10);
  solve_pcg.inc = 676767676767676767ULL;

  fprintf(stderr, "w=%d h=%d mines=%d board_seed=%" PRIu64 " solve_seed=%" PRIu64 "\n",
          bs.w, bs.h, bs.mine_count, board_pcg.state, solve_pcg.state);

  bs.board = malloc(bs.area * sizeof(int));
  bs.reveals = malloc(bs.area * sizeof(int));
  bs.num_reveals = 0;
  bs.revealed_masks = malloc(bs.area);
  bs.flagged_masks = malloc(bs.area);
  bs.border_masks = malloc(bs.area);
  int *buf = malloc((bs.area + bs.mine_count) * sizeof(int));

  for (int sq = 0; sq < bs.area; sq++) {
    bs.revealed_masks[sq] = 0;
    bs.flagged_masks[sq] = 0;

    char border_mask = 0;
    int x = sq % bs.w;
    int y = sq / bs.w;
    if (x == 0)
      border_mask |= 0b10010100;
    else if (x == bs.w - 1)
      border_mask |= 0b00101001;
    if (y == 0)
      border_mask |= 0b11100000;
    else if (y == bs.h - 1)
      border_mask |= 0b00000111;
    bs.border_masks[sq] = border_mask;
  }

  /* populate bs.board */
  place_mines(&bs, buf, &board_pcg);

  Solver solver;
  solver_init_bufs(&solver);
  /* populate bs.reveals */
  bs.num_reveals = forward_pass(&bs, &solver, &solve_pcg);
  /* prune bs.reveals */
  backward_pass(&bs, &solver);

  board_debug(&bs);
  printf("\n");

  for (int sq = 0; sq < bs.area; sq++) {
    int square = bs.board[sq];
    if (square & SQ_REVEAL_BIT)
      printf("%d", SQ_NO_BITS(square));
    else
      printf(".");
    if (sq % bs.w == bs.w - 1)
      printf("\n");
  }

  solver_free(&solver);
  free(buf);
  free(bs.board);
  free(bs.reveals);
  free(bs.revealed_masks);
  free(bs.flagged_masks);
  free(bs.border_masks);
}