import sys

try:
  n = int(sys.argv[1])
  k = int(sys.argv[2])
  r = int(sys.argv[3])

except:
  print('Usage: python waerden.py <n> <k> <r>')

else:
  print(f'c Waerden n={n} k={k} r={r}')
  # Don't bother with constraint count since Crocodile and MiniCARD
  # don't strictly require it
  print(f'p cnf+ {n*r} -1')

  negate = lambda x: -x

  for num in range(n):
    vars = range(r * num + 1, r * (num+1) + 1)
    print(' '.join(map(str, vars)), end='')
    print(' <= 1')
    print(' '.join(map(str, map(negate, vars))), end='')
    print(' <= 1')

  for col in range(r):
    for gap in range(1, (n-1)//(k-1) + 1):
      for base in range(n-1 - (k-1)*gap + 1):
        vars = range(base*r + col + 1, (base + col + (k-1)*gap) * r + 2, gap*r)
        print(' '.join(
          map(str, map(negate, vars))
        ), end='')
        print(' >= 1')