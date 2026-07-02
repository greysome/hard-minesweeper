#!/bin/sh
# Generate multiple reveal sets for the same board.
board_seed=${1:-0}
echo "board seed = ${board_seed}"
for solve_seed in $(seq 1 10); do
    echo "solve seed = ${solve_seed}"
    ./genboard 10 10 44 ${board_seed} ${solve_seed}
done