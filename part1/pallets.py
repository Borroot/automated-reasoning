from z3 import *

goods = {};
goods['nuzzle'] = {'weight': 700, 'pallet': 4}
goods['prittle'] = {'weight': 400}
goods['skipple'] = {'weight': 1000, 'pallet': 8}
goods['crottle'] = {'weight': 2500, 'pallet': 10}
goods['dupple'] = {'weight': 200, 'pallet': 20}
distribution = {}
for good in goods.keys():
	distribution[good] = [Int('{} {}'.format(good, truck)) for truck in range(8)]
print(distribution)

solver = Optimize();

for truck in range(8):
	truckWeight = 0
	numPallet = 0
	for good in goods.keys():
		truckWeight += distribution[good][truck] * goods[good]['weight']
		numPallet += distribution[good][truck]
		solver.add(0 <= distribution[good][truck])
	solver.add(truckWeight <= 8000)
	solver.add(numPallet <= 8)

for good in goods.keys():
	numPallet = 0
	for truck in range(8):
		numPallet += distribution[good][truck]
	if (good != 'prittle'):
		solver.add(numPallet == goods[good]['pallet'])
	else:
		solver.maximize(numPallet)

for truck in range(3,8):
	solver.add(distribution['skipple'][truck] == 0)

for truck in range(8):
	solver.add(distribution['nuzzle'][truck] <= 1)
	solver.add(Or(distribution['prittle'][truck] == 0, 
		          distribution['crottle'][truck] == 0))

with open('pallets.smt', 'w') as file:
	print(solver.to_smt(), file=file)

if (solver.check()):
	model = solver.model();
	print('    ', end = '')
	for good in goods.keys():
		print(good[0], end=' ')
	print()

	for truck in range(8):
		print(truck, ": ", end='')
		for good in goods.keys():
			print(model[distribution[good][truck]], end=' ')
		print()
else:
	print('unsat')



