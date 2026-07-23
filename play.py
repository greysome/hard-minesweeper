#!/usr/bin/env python3
"""Minimal tkinter Minesweeper UI for a JSON-Lines board file.

  python play.py <boards.json>

Each line in the file is one board:

    {
      "w": 5, "h": 5,
      "board":   "!!23!24!5!13!5!1!34!12!21",  // '!' = mine, '0'..'8' = clue
      "reveals": [0, 8, ...],
      "board_seed": 428,
      "solve_seed": 4,
      "difficulty": 0.842
    }

The board picker labels each entry `board=<board_seed> solve=<solve_seed>
diff=<difficulty>` so you can see all three fields without opening it.
Left click reveals; right click flags.
"""

import argparse
import json
import sys
import tkinter as tk
from tkinter import ttk


DIGIT_COLORS = {
    1: '#1976d2', 2: '#388e3c', 3: '#d32f2f', 4: '#7b1fa2',
    5: '#f57c00', 6: '#0097a7', 7: '#212121', 8: '#616161',
}


def neighbors(w, h, i):
    r, c = divmod(i, w)
    for dr in (-1, 0, 1):
        for dc in (-1, 0, 1):
            if dr == 0 and dc == 0:
                continue
            rr, cc = r + dr, c + dc
            if 0 <= rr < h and 0 <= cc < w:
                yield rr * w + cc


def load_specs(path):
    """Parse a JSON-Lines board file. Returns a list of spec dicts, each
    augmented with `mines_bits` (bitmask) and `counts` (list) derived from
    the `board` string.
    """
    specs = []
    with open(path) as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line:
                continue
            try:
                sp = json.loads(line)
            except json.JSONDecodeError as e:
                raise ValueError(f'{path}:{lineno}: invalid JSON: {e}')
            w, h = int(sp['w']), int(sp['h'])
            board = sp['board']
            if len(board) != w * h:
                raise ValueError(
                    f'{path}:{lineno}: board length {len(board)} != w*h {w * h}')
            mines_bits = 0
            counts = [0] * (w * h)
            for i, ch in enumerate(board):
                if ch == '!':
                    mines_bits |= 1 << i
                elif '0' <= ch <= '8':
                    counts[i] = int(ch)
                else:
                    raise ValueError(
                        f'{path}:{lineno}: unknown board char {ch!r} at {i}')
            sp['w'] = w
            sp['h'] = h
            sp['mines_bits'] = mines_bits
            sp['counts'] = counts
            specs.append(sp)
    return specs


def cascade_reveal(w, h, mines, counts, i, revealed, flagged):
    """Reveal cell i and cascade through connected 0-clue cells.

    Assumes i is not a mine (caller enforces this).
    """
    stack = [i]
    while stack:
        j = stack.pop()
        jb = 1 << j
        if revealed & jb:
            continue
        revealed |= jb
        if counts[j] == 0:
            for k in neighbors(w, h, j):
                kb = 1 << k
                if not (revealed & kb) and not (flagged & kb) and not (mines & kb):
                    stack.append(k)
    return revealed


def format_difficulty(d):
    if isinstance(d, float):
        return f'{d:.3f}'
    return '?' if d is None else str(d)


def make_labels(specs):
    return [
        f'board={sp.get("board_seed", "?")}  '
        f'solve={sp.get("solve_seed", "?")}  '
        f'diff={format_difficulty(sp.get("difficulty"))}'
        for sp in specs
    ]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('path', help='JSON-Lines board file')
    args = ap.parse_args()

    try:
        specs = load_specs(args.path)
    except Exception as e:
        print(f'error: {e}', file=sys.stderr)
        sys.exit(1)
    if not specs:
        print(f'no boards found in {args.path}', file=sys.stderr)
        sys.exit(1)
    labels = make_labels(specs)

    root = tk.Tk()
    root.title('Minesweeper')
    root.option_add('*Font', 'TkFixedFont 12')

    # Game state is a plain dict — mutable, closed over by handlers below.
    state = {
        'w': 0, 'h': 0,
        'mines': 0, 'counts': [],
        'revealed': 0, 'flagged': 0,
        'M': 0,
        'over': False,
        'buttons': [],
    }

    bar = ttk.Frame(root, padding=6)
    bar.grid(row=0, column=0, sticky='ew')

    ttk.Label(bar, text='Board:').grid(row=0, column=0)
    picker_var = tk.StringVar(value=labels[0])
    picker = ttk.Combobox(bar, textvariable=picker_var, values=labels,
                          width=44, state='readonly')
    picker.grid(row=0, column=1, padx=(2, 12))

    mines_lbl = ttk.Label(bar, text='Mines: --')
    mines_lbl.grid(row=0, column=2, padx=(0, 12))
    status_lbl = ttk.Label(bar, text='')
    status_lbl.grid(row=0, column=3, sticky='w')

    grid_frame = ttk.Frame(root, padding=6)
    grid_frame.grid(row=1, column=0)

    def refresh(hit=None):
        w = state['w']
        h = state['h']
        mines = state['mines']
        counts = state['counts']
        revealed = state['revealed']
        flagged = state['flagged']
        over = state['over']
        for i in range(w * h):
            btn = state['buttons'][i]
            bit = 1 << i
            is_mine = bool(mines & bit)
            is_rev = bool(revealed & bit)
            is_flag = bool(flagged & bit)
            if is_flag:
                btn.config(text='⚑', fg='#c62828', bg='#bdbdbd', relief='raised')
            elif is_rev:
                if is_mine:
                    bg = '#ff5252' if i == hit else '#ffcdd2'
                    btn.config(text='✸', fg='black', bg=bg, relief='sunken')
                else:
                    n = counts[i]
                    btn.config(text=('' if n == 0 else str(n)),
                               fg=DIGIT_COLORS.get(n, 'black'),
                               bg='#e0e0e0', relief='sunken')
            elif over and is_mine:
                btn.config(text='✸', fg='black', bg='#eeeeee', relief='raised')
            else:
                btn.config(text='', fg='black', bg='#bdbdbd', relief='raised')
        remaining = state['M'] - bin(flagged).count('1')
        mines_lbl.config(text=f'Mines: {remaining}')

    def on_left(i):
        if state['over']:
            return
        bit = 1 << i
        if state['revealed'] & bit or state['flagged'] & bit:
            return
        if state['mines'] & bit:
            state['revealed'] |= bit
            state['over'] = True
            status_lbl.config(text='BOOM. You lose.')
            refresh(hit=i)
            return
        state['revealed'] = cascade_reveal(
            state['w'], state['h'], state['mines'], state['counts'],
            i, state['revealed'], state['flagged'])
        area = state['w'] * state['h']
        safe = ((1 << area) - 1) & ~state['mines']
        if (state['revealed'] & safe) == safe:
            state['over'] = True
            status_lbl.config(text='You win!')
        refresh()

    def on_right(i):
        if state['over']:
            return
        bit = 1 << i
        if state['revealed'] & bit:
            return
        state['flagged'] ^= bit
        refresh()

    def rebuild_grid():
        for w in grid_frame.winfo_children():
            w.destroy()
        state['buttons'] = []
        for r in range(state['h']):
            for c in range(state['w']):
                i = r * state['w'] + c
                btn = tk.Label(grid_frame, text='', width=2, height=1,
                               relief='raised', borderwidth=2,
                               bg='#bdbdbd', fg='black')
                btn.grid(row=r, column=c)
                btn.bind('<Button-1>', lambda e, idx=i: on_left(idx))
                btn.bind('<Button-3>', lambda e, idx=i: on_right(idx))
                state['buttons'].append(btn)

    def load_board():
        try:
            idx = labels.index(picker_var.get())
        except ValueError:
            return
        sp = specs[idx]
        state['w'] = sp['w']
        state['h'] = sp['h']
        state['mines'] = sp['mines_bits']
        state['counts'] = sp['counts']
        state['M'] = bin(state['mines']).count('1')
        state['revealed'] = 0
        state['flagged'] = 0
        state['over'] = False
        for r in sp['reveals']:
            if state['mines'] & (1 << r):
                raise ValueError(
                    f'spec #{idx + 1}: reveal index {r} is a mine')
            state['revealed'] = cascade_reveal(
                state['w'], state['h'], state['mines'], state['counts'],
                r, state['revealed'], state['flagged'])
        status_lbl.config(text='')
        rebuild_grid()
        refresh()

    picker.bind('<<ComboboxSelected>>', lambda _e: load_board())
    ttk.Button(bar, text='Restart', command=load_board).grid(
        row=0, column=4, padx=(12, 0))

    load_board()
    root.mainloop()


if __name__ == '__main__':
    main()
