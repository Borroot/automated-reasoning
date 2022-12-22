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

hinted = [[Int("(h {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]
differs = [[Int("(c {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]
filled = [[Int("(f {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]

solver = Optimize()
puzzle = Optimize()

numConstraint = 0

numDifferent = 0
numChanged = 0
numHint = 0
minHint = 0
for r in range(HEIGHT):
	for c in range(WIDTH):
		solver.add(0 <= hinted[r][c])
		solver.add(hinted[r][c] <= 1)
		solver.add(0 <= filled[r][c])
		solver.add(filled[r][c] <= 1)
		solver.add(0 <= differs[r][c])
		solver.add(differs[r][c] <= 1)

		numDifferent = differs[r][c] + numDifferent
		numHint = hinted[r][c] + numHint

		if grid[r][c] == 0:
			numChanged = filled[r][c] + numChanged
		else:
			numChanged = 1 - filled[r][c] + numChanged

		actual = 0
		for r2 in range(max(r-1,0), min(r+2,HEIGHT)):
			for c2 in range(max(c-1,0), min(c+2,WIDTH)):
				value[r][c] = grid[r2][c2] + value[r][c]
				actual = filled[r2][c2] + actual
		solver.add(Or(value[r][c] == actual, hinted[r][c] == 0))
		solver.add(Or(value[r][c] == actual, differs[r][c] == 1))

		puzzle.add(0 <= hinted[r][c])
		puzzle.add(hinted[r][c] <= 1)

solver.minimize(numDifferent)
solver.add(0 < numChanged)

puzzle.minimize(numHint)

minDiffers = 0
while solver.check() == sat:
	solver.push()
	solver.add(numHint <= minHint)
	solver.add(minDiffers <= numDifferent)
	solvable = solver.check()
	if solvable != sat:
		break
	model = solver.model()
	solver.pop()
	print('\033[0;0H')
	print()
	print("number of constraints", numConstraint)
	
	for r in range(HEIGHT):
		for c in range(WIDTH):
			if model[hinted[r][c]].as_long() == 1:
				print('\x1b[42m', end='')
			if model[differs[r][c]].as_long() == 1:
				print('\x1b[41m', end='')
			if model[filled[r][c]].as_long() != grid[r][c]:
				print('\x1b[34m',end='')
			print(model[filled[r][c]], end=' ')
			print('\x1b[0m', end='')
		print()
	print("multiple solutions")

	numDiff = 0
	for r in range(HEIGHT):
		for c in range(WIDTH):
			if grid[r][c] != model[filled[r][c]].as_long():
				numDiff += 1
	print("number different in alternate solution", numDiff, end='      \n')

	clause = 0
	minDiffers = 0
	for r in range(HEIGHT):
		for c in range(WIDTH):
			if model[differs[r][c]].as_long() == 1:
				minDiffers += 1
				clause = hinted[r][c] + clause
	print("number of cases in new Constraint", minDiffers, end='      \n')
	numConstraint += 1
	solver.add(0 < clause)
	solver.push()

	puzzle.add(0 < clause)
	puzzle.push()

	solvable = puzzle.check()
	print(solvable)
	if solvable != sat:
		quit()

	minPuzzle = puzzle.model()
	minHint = 0
	for r in range(HEIGHT):
		for c in range(WIDTH):
			if minPuzzle[hinted[r][c]].as_long() == 1:
				minHint += 1
				print('\x1b[41m', end='')
			print(value[r][c], end=' ')
			print('\x1b[0m', end='')
		print()
	print("number of hints", minHint)
