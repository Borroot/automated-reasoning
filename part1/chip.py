from z3 import *
import random
import colorsys

height = 30
width = 30
minDist = 17.5

power = (3,4)
numPower = 2
components = [
	(4,5),
	(4,6),
	(5,20),
	(6,9),
	(6,10),
	(6,11),
	(7,8),
	(7,12),
	(10,10),
	(10,20),
]

powerVars = []
componentVars = []
allVars = []

solver = Solver();


for i in range(numPower):
	newVars = {};
	newVars['left'] = Int('power {} left'.format(i))
	newVars['top'] = Int('power {} top'.format(i))
	newVars['right'] = Int('power {} right'.format(i))
	newVars['bottom'] = Int('power {} bottom'.format(i))
	solver.add(0 <= newVars['left'])
	solver.add(newVars['right'] <= width)
	solver.add(0 <= newVars['top'])
	solver.add(newVars['bottom'] <= height)
	size = power
	solver.add(Or(And(newVars['right'] - newVars['left'] == size[0],
	                  newVars['bottom'] - newVars['top'] == size[1]),
	              And(newVars['right'] - newVars['left'] == size[1],
	                  newVars['bottom'] - newVars['top'] == size[0])))

	for power in powerVars:
		distant = []
		distant.append((newVars['left'] + newVars['right']) - (power['left'] + power['right']) >= 2 * minDist)
		distant.append((power['left'] + power['right']) - (newVars['left'] + newVars['right']) >= 2 * minDist)
		distant.append((newVars['top'] + newVars['bottom']) - (power['top'] + power['bottom']) >= 2 * minDist)
		distant.append((power['top'] + power['bottom']) - (newVars['top'] + newVars['bottom']) >= 2 * minDist)
		
		solver.add(Or(*distant))

	powerVars.append(newVars)
	allVars.append(newVars)

for i in range(len(components)):
	newVars = {};
	newVars['left'] = Int('component {} left'.format(i))
	newVars['top'] = Int('component {} top'.format(i))
	newVars['right'] = Int('component {} right'.format(i))
	newVars['bottom'] = Int('component {} bottom'.format(i))
	solver.add(0 <= newVars['left'])
	solver.add(newVars['right'] <= width)
	solver.add(0 <= newVars['top'])
	solver.add(newVars['bottom'] <= height)
	size = components[i]
	isVertical = And(newVars['right'] - newVars['left'] == size[0],
	               newVars['bottom'] - newVars['top'] == size[1])
	isHorizontal = And(newVars['right'] - newVars['left'] == size[1],
	                 newVars['bottom'] - newVars['top'] == size[0])
	solver.add(Or(isVertical, isHorizontal))

	touches = []
	for power in powerVars:
		overlaps_y = And(power['top'] < newVars['bottom'],
		                 power['bottom'] > newVars['top'])
		touches.append(And(power['left'] == newVars['right'], overlaps_y))
		touches.append(And(power['right'] == newVars['left'], overlaps_y))

		overlaps_x = And(power['left'] < newVars['right'],
		                 power['right'] > newVars['left'])
		touches.append(And(power['top'] == newVars['bottom'], overlaps_x))
		touches.append(And(power['bottom'] == newVars['top'], overlaps_x))

	solver.add(Or(*touches))

	componentVars.append(newVars)
	allVars.append(newVars)

for i in range(len(allVars)):
	for j in range(i+1, len(allVars)):
		solver.add(Or(allVars[i]['right'] <= allVars[j]['left'],
		              allVars[i]['bottom'] <= allVars[j]['top'],
		              allVars[j]['right'] <= allVars[i]['left'],
		              allVars[j]['bottom'] <= allVars[i]['top']
		))

solvable = solver.check()
print(solvable)
if solvable == sat:
	grid = [['\x1b[40m' for c in range(width)] for r in range(height)]

	model = solver.model()

	# print(model[minDist])

	for i in range(len(allVars)):
		component = allVars[i]
		left = model[component['left']].as_long()
		right = model[component['right']].as_long()
		top = model[component['top']].as_long()
		bottom = model[component['bottom']].as_long()
		
		red,green,blue = colorsys.hsv_to_rgb(float(i)/len(allVars), 1, 1)
		red = int(255*red)
		green = int(255*green)
		blue = int(255*blue)
		color = "\x1b[48;2;{};{};{}m".format(red, green, blue)
		for r in range(top,bottom):
			for c in range(left, right):
				grid[r][c] = color

	for r in range(height):
		for c in range(width):
			print(grid[r][c],end='')
			print('  ',end='')
			print('\x1b[0m',end='')
		print()
