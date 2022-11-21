from z3 import *
import csv

START = 0
TARGET = 1
LAVA = 2
ICE = 3

NORTH = 0
EAST = 1
SOUTH = 2
WEST = 3

optimize = Optimize()
goal = Int('goal')
optimize.minimize(goal)

with open('grid3.csv', mode='r') as file:
	csvFile = csv.reader(file)
	grid = [[int(x) for x in line] for line in csvFile]

height = len(grid)
width = len(grid[0])
numColor = 0
for r in range(height):
	for c in range(width):
		numColor = max(grid[r][c]+1, numColor)

direction = [Int("dir {}".format(i)) for i in range(numColor)]
for i in range(numColor):
	optimize.add(0 <= direction[i])
	optimize.add(direction[i] < 4)

def next(r,c,direction, steps):
	if direction == NORTH:
		return max(r-steps, 0), c
	if direction == EAST:
		return r, min(c+steps, width-1)
	if direction == SOUTH:
		return min(r+steps, height-1), c
	if direction == WEST:
		return r, max(c-steps, 0)


dist = [[Int("dist {} {}".format(r,c)) for c in range(width)] for r in range(height)]
for r in range(height):
	for c in range(width):
		color = grid[r][c]
		if color == TARGET:
			optimize.add(dist[r][c] == 0)
		elif color == LAVA:
			optimize.add(dist[r][c] == goal+1) # practically infinite
		elif color == ICE:
			for dir in range(4):
				next_r, next_c = next(r,c,dir,1)
				optimize.add(Implies(direction[color] == dir,
					                 Or(dist[r][c] == goal+1, # practically infinite
					                 	dist[r][c] >= dist[next_r][next_c]+1
				)))

				next_r, next_c = next(r,c,dir,2)
				optimize.add(Implies(direction[color] == dir,
					                 Or(dist[r][c] == goal+1, # practically infinite
					                 	dist[r][c] >= dist[next_r][next_c]+1
				)))

		else:
			if color == START:
				optimize.add(dist[r][c] <= goal)
			for dir in range(4):
				next_r, next_c = next(r,c,dir,1)
				optimize.add(Implies(direction[color] == dir,
					                 Or(dist[r][c] == goal+1, # practically infinite
					                 	dist[r][c] >= dist[next_r][next_c]+1
				)))

satisfiable = optimize.check()
if satisfiable != sat:
	print(satisfiable)
	print(optimize.unsat_core())
	exit()

model = optimize.model()
print(model[goal])
for i in range(numColor):
	print(i, model[direction[i]])

colors = [
	'\x1b[48;2;0;128;0m',
	'\x1b[48;2;0;0;0m',
	'\x1b[48;2;220;20;60m',
	'\x1b[48;2;255;255;255;30m',
	'\x1b[48;2;238;130;238m',
	'\x1b[48;2;135;206;250m',
	'\x1b[48;2;255;165;0m',
	'\x1b[48;2;0;0;255m',
	'\x1b[48;2;255;192;203m',
	'\x1b[48;2;255;255;0m',
	'\x1b[48;2;0;191;255m',
	'\x1b[48;2;0;128;128m',
	'\x1b[48;2;255;222;173m',
	'\x1b[48;2;184;134;11m',
	'\x1b[48;2;255;160;122m',
]

for r in range(height):
	for c in range(width):
		print(colors[grid[r][c]], end='')
		if model[direction[grid[r][c]]].as_long() == NORTH:
			print('/\\',end='')
		if model[direction[grid[r][c]]].as_long() == EAST:
			print(' >',end='')
		if model[direction[grid[r][c]]].as_long() == SOUTH:
			print('\\/',end='')
		if model[direction[grid[r][c]]].as_long() == WEST:
			print('< ',end='')
		print('\x1b[0m',end='')
	print()
