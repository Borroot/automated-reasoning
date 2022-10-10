from z3 import *

numHouse = 5
coupleSize = 2
numPerson = coupleSize * numHouse
numRound = 5
groupPerRound = 2
numGroup = groupPerRound * numRound
# assume groupPerRound divides numPerson
groupSize = numPerson // groupPerRound
groupsPerHouse = numGroup // numHouse
maxMeetup = 4


inGroup = [[Bool('g{} p{}'.format(group, person))
            for group in range(numGroup)]
            for person in range(numPerson)]
groupHost = [[Bool('g{} h{}'.format(group, house))
              for house in range(numHouse)]
              for group in range(numGroup)]

solver = Solver()

optional = {'A': [], 'B': [], 'C': [], 'D': []}

for group in range(numGroup):
	# At most 5 people in each group
	visitors = [inGroup[person][group]
	            for person in range(numPerson)]
	solver.add(AtMost(*visitors,groupSize))

	for house in range(numHouse):
		# The hosts are present in the group they host
		hosts = [inGroup[person][group] for person in range(coupleSize*house, coupleSize*(house+1))]
		solver.add(Implies(groupHost[group][house], And(*hosts)))

		# If a couple does not host, they are not in the same group
		optional['C'].append(Implies(Not(groupHost[group][house]), AtMost(*hosts,1)))

	# Each group is hosted by exactly one house
	solver.add(AtLeast(*groupHost[group],1))
	solver.add(AtMost(*groupHost[group],1))

for person in range(numPerson):
	# Each person visits at least one group each round
	for round in range(numRound):
		groups = inGroup[person][groupPerRound*round:groupPerRound*(round+1)]
		solver.add(AtLeast(*groups, 1))

	for other in range(person+1, numPerson):
		# Everyone meets each-other at most maxMeetup times
		meetups = [And(inGroup[person][group], inGroup[other][group]) for group in range(numGroup)]
		solver.add(AtMost(*meetups, maxMeetup))

		# Every two people meet each-other at least once
		optional['A'].append(AtLeast(*meetups, 1))
		# Every two people meet each-other at most three times
		optional['B'].append(AtMost(*meetups, 3))

	for house in range(numHouse):
		if person // coupleSize == house:
			continue
		# Everyone is at most once a guest at another house
		hosted = [And(inGroup[person][group], groupHost[group][house]) for group in range(numGroup)]
		optional['D'].append(AtMost(*hosted, 1))

for house in range(numHouse):
	# Everyone hosts at least groupsPerHouse times
	groups = [groupHost[group][house] for group in range(numGroup)]
	solver.add(AtLeast(*groups, groupsPerHouse))

def printModel(model):
	for round in range(numRound):
		for group in range(groupPerRound*round,groupPerRound*(round+1)):
			if group != groupPerRound*round:
				print('<>',end=' ')
			for person in range(numPerson):
				if is_true(model[groupHost[group][person//coupleSize]]):
					print('\x1b[32m', end='')
				if is_true(model[inGroup[person][group]]):
					print(person, end=' ')
				print('\x1b[0m',end='')
		print()

reqs = ['A', 'B', 'C', 'D']
subsets = [[]]
for req in reqs:
	subsets = [subset for subset in subsets] + [subset + [req] for subset in subsets]
for subset in subsets:
	print('with requirements {}'.format(', '.join(subset)))
	if 'A' in subset and 'B' in subset:
		print('unknown')
		continue
	solver.push()
	for req in subset:
		solver.add(And(*optional[req]))
	solvable = solver.check()
	if solvable != sat:
		print(solvable)
	else:
		printModel(solver.model())
	solver.pop()
