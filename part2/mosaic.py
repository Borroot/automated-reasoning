from z3 import *
import random

WIDTH = 6
HEIGHT = 6

grid = [
	[1, 1, 0, 0, 1, 0],
	[1, 0, 1, 0, 0, 0],
	[1, 1, 0, 1, 0, 1],
	[0, 1, 1, 1, 0, 1],
	[0, 0, 1, 1, 1, 1],
	[0, 0, 1, 1, 0, 1],
]
# grid = [[random.randint(0,1) for c in range(WIDTH)] for r in range(HEIGHT)]
value = [[0 for c in range(WIDTH)] for r in range(HEIGHT)]
filled = [[Int("(f {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]

for r in range(HEIGHT):
	for c in range(WIDTH):
		print(grid[r][c], end=' ')
	print()
print()

solver = Solver()
solver.set(':core.minimize', True)

numConstraint = 0

numDifferent = 0
for r in range(HEIGHT):
	for c in range(WIDTH):
		solver.add(0 <= filled[r][c])
		solver.add(filled[r][c] <= 1)

		if grid[r][c] == 0:
			numDifferent += filled[r][c]
		else:
			numDifferent += 1-filled[r][c]

		actual = 0
		for r2 in range(max(r-1,0), min(r+2,HEIGHT)):
			for c2 in range(max(c-1,0), min(c+2,WIDTH)):
				value[r][c] += grid[r2][c2]
				actual += filled[r2][c2]
		solver.assert_and_track(value[r][c] == actual, '{} {} {}'.format(r,c,value[r][c]))

solver.add(0 < numDifferent)
satisfiable = solver.check()
print(satisfiable)
if satisfiable == unsat:
	core = solver.unsat_core()
	print(len(core))
	puzzle = [['.' for c in range(WIDTH)] for r in range(HEIGHT)]
	for entry in core:
		r, c, value = map(int, entry.__str__().split())
		puzzle[r][c] = str(value)
	for r in range(HEIGHT):
		for c in range(WIDTH):
			print(puzzle[r][c], end=' ')
		print()
	print()
	quit()

if satisfiable == sat:
	model = solver.model()
	for r in range(HEIGHT):
		for c in range(WIDTH):
			print(model[filled[r][c]], end=' ')
		print()
	print()
	quit()
