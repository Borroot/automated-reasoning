from z3 import *

NUM_TRUCKS = 8
TRUCK_CAPACITY = 8000
TRUCK_MAX_PALLETS = 8

# Create all the goods with their weight and number of pallets.
goods = {
    'nuzzle':  {'weight': 700,  'pallet': 4},
    'skipple': {'weight': 1000, 'pallet': 8},
    'crottle': {'weight': 2500, 'pallet': 10},
    'dupple':  {'weight': 200,  'pallet': 20},
    'prittle': {'weight': 400},
};

# Create all the z3 variables, an integer for every (good, truck) pair
# representing the amount of that good in the truck.
distribution = {}
for good in goods.keys():
    distribution[good] = [Int('{} {}'.format(good, truck)) for truck in range(NUM_TRUCKS)]

# Create the solver object, we optimize for the number of prittle pallets.
solver = Optimize();

# Make sure that all the trucks do not have more than their max capacity of
# pallets or more than their max capacity of weight.
for truck in range(NUM_TRUCKS):
    truckWeight = 0
    numPallet = 0

    for good in goods.keys():
        truckWeight += distribution[good][truck] * goods[good]['weight']
        numPallet += distribution[good][truck]
        solver.add(0 <= distribution[good][truck])

    solver.add(truckWeight <= TRUCK_CAPACITY)
    solver.add(numPallet <= TRUCK_MAX_PALLETS)

# Make sure that all the pallets for all the goods are distributed over the
# trucks and optimise for the number of prittles.
for good in goods.keys():
    numPallet = sum(distribution[good][truck] for truck in range(NUM_TRUCKS))
    if (good != 'prittle'):
        solver.add(numPallet == goods[good]['pallet'])
    else:
        solver.maximize(numPallet)

# Only three trucks (the first three) have cooling facilities for skipples.
for truck in range(3, NUM_TRUCKS):
    solver.add(distribution['skipple'][truck] == 0)

for truck in range(NUM_TRUCKS):
    # No two pallets of nuzzles may be in the same truck.
    solver.add(distribution['nuzzle'][truck] <= 1)
    # Prittles and crottles are an explosive combination.
    solver.add(Or(distribution['prittle'][truck] == 0,
                  distribution['crottle'][truck] == 0))

# Check if the formula is satisfiable or not.
if solver.check():
    model = solver.model();

# Print the solution in a nice table format.
    print('    ', end = '')
    for good in goods.keys():
        print(good[0], end=' ')
    print()

    for truck in range(NUM_TRUCKS):
        print(truck, ": ", end='')
        for good in goods.keys():
            print(model[distribution[good][truck]], end=' ')
        print()
else:
    print('unsat')
