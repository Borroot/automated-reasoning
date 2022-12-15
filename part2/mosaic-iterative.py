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
contributes = [[Int("(c {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]
filled = [[Int("(f {},{})".format(r,c)) for c in range(WIDTH)] for r in range(HEIGHT)]

solver = Optimize()
puzzle = Optimize()

numConstraint = 0

numContributes = 0
numDifferent = 0
numHint = 0
minHint = 0
for r in range(HEIGHT):
	for c in range(WIDTH):
		solver.add(0 <= hinted[r][c])
		solver.add(hinted[r][c] <= 1)
		solver.add(0 <= filled[r][c])
		solver.add(filled[r][c] <= 1)
		solver.add(0 <= contributes[r][c])
		solver.add(contributes[r][c] <= 1)

		numContributes = contributes[r][c] + numContributes
		numHint = hinted[r][c] + numHint

		if grid[r][c] == 0:
			numDifferent = filled[r][c] + numDifferent
		else:
			numDifferent = 1 - filled[r][c] + numDifferent

		actual = 0
		for r2 in range(max(r-1,0), min(r+2,HEIGHT)):
			for c2 in range(max(c-1,0), min(c+2,WIDTH)):
				value[r][c] = grid[r2][c2] + value[r][c]
				actual = filled[r2][c2] + actual
		solver.add(Or(value[r][c] == actual, hinted[r][c] == 0))
		solver.add(Or(value[r][c] == actual, contributes[r][c] == 1))

		puzzle.add(0 <= hinted[r][c])
		puzzle.add(hinted[r][c] <= 1)

solver.minimize(numContributes)
solver.add(0 < numDifferent)

puzzle.minimize(numHint)

minContributes = 0
while solver.check() == sat:
	solver.push()
	solver.add(numHint <= minHint)
	solver.add(minContributes <= numContributes)
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
			if model[contributes[r][c]].as_long() == 1:
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

	contributions = 0
	minContributes = 0
	for r in range(HEIGHT):
		for c in range(WIDTH):
			if model[contributes[r][c]].as_long() == 1:
				minContributes += 1
				contributions = hinted[r][c] + contributions
	print("number of cases in new Constraint", minContributes, end='      \n')
	numConstraint += 1
	solver.add(0 < contributions)
	solver.push()

	puzzle.add(0 < contributions)
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
