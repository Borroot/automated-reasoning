from z3 import *
import functools
import itertools
import sys

class Term:
	""" The base class for terms """
	def toString(self, print_index=True) -> str:
		pass

	def print(self) -> None:
		print(self.toString())
		return

	def subterms(self):
		return [self]

	def __eq__(self, other):
		return self.toString() == other.toString()

	def __lt__(self, other):
		return self.toString() < other.toString()

	def __hash__(self):
		return self.toString().__hash__()

	def __str__(self):
		return self.toString()

	def __repr__(self):
		return self.toString()


class Function(Term):
	"""A class representing a function term with its arguments"""
	name : str
	args : list[Term]

	def __init__(self, name : str, *args : list[Term]):
		self.name = name
		self.args = args

	def toString(self, print_index=True) -> str:
		argStrings = [arg.toString(print_index) for arg in self.args]
		return self.name + '(' + ', '.join(argStrings) + ')'

	def subterms(self):
		terms = [self]
		for arg in self.args:
			terms += arg.subterms()
		return terms


class Variable(Term):
	"""A class representing a variable."""
	name : str
	index : int

	def __init__(self, name : str, index : int):
		self.name = name
		self.index = index

	def toString(self, print_index=True) -> str:
		if print_index:
			return self.name + '{' + str(self.index) + '}'
		else:
			return self.name

	def subterms(self):
		return [self]


def parse_at_pos(string : str, index : int, pos : int) -> (Term, int):
	while pos < len(string) and not string[pos].isalpha():
		pos += 1
	name = ""
	while pos < len(string) and string[pos].isalpha():
		name += string[pos]
		pos += 1
	if pos == len(string) or string[pos] != '(':
		return Variable(name, index), pos
	args = []
	while pos < len(string) and string[pos] != ')':
		arg, pos = parse_at_pos(string, index, pos)
		args.append(arg)
	return Function(name, *args), pos+1


def parse(string : str, index : int) -> Term:
	t, _pos = parse_at_pos(string, index, 0)
	return t


class Comparison:
	"""A class representing an inequality."""
	lhs : Term
	rhs : Term

	def __init__(self, lhs : Term, rhs : Term):
		self.lhs = lhs
		self.rhs = rhs

	def subterms(self):
		"""Returns the unique subterms of the lhs and rhs in sorted order."""
		return sorted(list(set(self.lhs.subterms()))), sorted(list(set(self.rhs.subterms())))

	def toString(self):
		return self.lhs.toString() + ' > ' + self.rhs.toString()

	def print(self):
		print(self.toString())


uid = 0  # used to generate unique variable names
def parse_inequality(string : str) -> Comparison:
	global uid
	lhs, rhs = string.split('>')
	lhs = parse(lhs, uid)
	rhs = parse(rhs, uid)
	uid += 1
	return Comparison(lhs, rhs)


# Parse the inequalities
inequalities = list(map(parse_inequality, [
	'c(x,y,u,v) > b(f(x,y),b(u,u,u),g(v,b(x,y,u)))',
	'b(f(x,y),g(x,y),f(x,g(z,u))) > b(f(x,z),y,g(g(g(y,x),x),x))',
	'h(g(x,g(u,z)),c(x,y,x,z)) > f(d(x,z),u)',
	'h(d(f(x,y),g(u,v)),f(x,y)) > f(c(u,x,v,y),g(y,x))',
	'f(b(x,y,z),u) > h(u,f(x,h(y,x)))',
	'b(a(x,y,z),y,x) > c(x,x,y,x)',
]))

# Create the solver and minimize the unsat core for unsat examples
solver = Solver()
solver.set(':core.minimize', True)

# Generate all the unique subterms
subterms = []
for ineq in inequalities:
	subterms += ineq.lhs.subterms()
	subterms += ineq.rhs.subterms()
subterms = sorted(list(set(subterms)))

# Generate all the unique functions
functions = [term.name for term in subterms if isinstance(term, Function)]
functions = sorted(list(set(functions)))

# Generate the function ordering variables
fun_ge = {f : {g : Bool(f + '|>=' + g) for g in functions} for f in functions}
fun_gt = {f : {g : Bool(f + '|>' + g) for g in functions} for f in functions}
fun_eq = {f : {g : Bool(f + '=' + g) for g in functions} for f in functions}

# Generate the function ordering constraints
for f in functions:
	for g in functions:
		if f <= g:
			solver.add(Or(fun_ge[f][g], fun_ge[g][f]))
			solver.add(fun_eq[f][g] == And(fun_ge[f][g], fun_ge[g][f]))
		for h in functions:
			solver.add(Implies(And(fun_ge[f][g], fun_ge[g][h]), fun_ge[f][h]))
		solver.add(fun_gt[f][g] == And(fun_ge[f][g], Not(fun_ge[g][f])))
	solver.add(fun_ge[f][f])

# Generate the term ordering variables
symbols = ['>', '>~', '~', '>a', '>b', '>c', '~a', '~b']

# Generate a term compare variable for each pair of terms and each symbol
# term_compare[symbol][s][t] is the variable representing s symbol t
term_compare = {}
for symbol in symbols:
	term_compare[symbol] = {}
	for ineq in inequalities:
		left_terms, right_terms = ineq.subterms()
		for s in left_terms:
			term_compare[symbol][s] = {}
			for t in right_terms:
				term_compare[symbol][s][t] = Bool(s.toString() + symbol + t.toString())

# The total number of comparisons made with >, used to simplify the proof
compares = []

for ineq in inequalities:
	left_terms, right_terms = ineq.subterms()
	for s in left_terms:
		for t in right_terms:
			compares.append(term_compare['>'][s][t])

			# Set constraint 1
			solver.add(term_compare['>~'][s][t] == Or(term_compare['>'][s][t], term_compare['~'][s][t]))

			if isinstance(s, Variable):
				solver.add(Not(term_compare['>'][s][t]))

			if isinstance(s, Function):
				# Set constraint 2
				solver.add(term_compare['>'][s][t] == Or(term_compare['>a'][s][t], term_compare['>b'][s][t], term_compare['>c'][s][t]))

				# Set constraint 2a
				solver.add(term_compare['>a'][s][t] == Or(*[term_compare['>~'][si][t] for si in s.args]))

				if isinstance(t, Function):
					# Set constraint 2b
					solver.add(term_compare['>b'][s][t] == And(fun_gt[s.name][t.name], *[term_compare['>'][s][ti] for ti in t.args]))

					# Generate all the functions phi and EQ
					conditions = []
					n = len(s.args)
					m = len(t.args)
					for phi in itertools.product(range(n), repeat=m):
						# e.g. phi = [0,1,0,2]
						for eq in itertools.product([True,False], repeat=n):
							# e.g. eq = [True, False, True]
							valid = not all(eq)
							for i in range(m):
								if eq[phi[i]] and 1 < phi.count(phi[i]):
									valid = False
							for i in range(n):
								if i not in phi and eq[i]:
									valid = False

							if not valid:
								continue

							condition = []
							for i in range(m):
								if eq[phi[i]]:
									condition.append(term_compare['~'][s.args[phi[i]]][t.args[i]])
								else:
									condition.append(term_compare['>'][s.args[phi[i]]][t.args[i]])
							conditions.append(And(*condition))

					# Set constraint 2c
					solver.add(term_compare['>c'][s][t] == And(fun_eq[s.name][t.name], Or(*conditions)))
				else:
					solver.add(Not(term_compare['>b'][s][t]))
					solver.add(Not(term_compare['>c'][s][t]))

			# Set constraint 3
			solver.add(term_compare['~'][s][t] == Or(term_compare['~a'][s][t], term_compare['~b'][s][t]))

			if isinstance(s, Variable) and isinstance(t, Variable) and s.name == t.name and s.index == t.index:
				# Set constraint 3a
				solver.add(term_compare['~a'][s][t])
			else:
				solver.add(Not(term_compare['~a'][s][t]))

			if isinstance(s, Function) and isinstance(t,Function) and len(s.args) == len(t.args):
				lhs = s.args
				conditions = []
				for rhs in itertools.permutations(t.args):
					conditions.append(And(*[term_compare['~'][lhs[i]][rhs[i]] for i in range(len(lhs))]))
				# Set constraint 3b
				solver.add(term_compare['~b'][s][t] == And(fun_eq[s.name][t.name], Or(*conditions)))
			else:
				solver.add(Not(term_compare['~b'][s][t]))

	solver.add(term_compare['>'][ineq.lhs][ineq.rhs])

# Do a binairy search trying to minimize the final proof
low = 0
high = len(compares)
while low + 1 < high:
	middle = (low + high) // 2
	solver.push()
	solver.add(AtMost(*compares, middle))
	satisfiable = solver.check()
	if satisfiable == sat:
		high = middle
	else:
		low = middle
	solver.pop()
solver.add(AtMost(*compares, high))

# Get another solution by uncommenting this
# solver.add(Not(fun_gt['h']['d']))

satisfiable = solver.check()
if satisfiable != sat:
	print("not satisfiable")
	print(solver.unsat_core())
	quit()

model = solver.model()

# Print the function order
comparator = lambda x,y : int(is_true(model[fun_gt[x][y]])) - int(is_true(model[fun_gt[y][x]]))
functions = sorted(functions, key=functools.cmp_to_key(comparator), reverse = True)
prev = functions[0]
first = True
for f in functions:
	if is_true(model[fun_eq[prev][f]]) and not first:
		print(' = ', end='')
	elif not first:
		print(' > ', end='')
	print(f, end='')
	prev = f
	first = False
print()

# Print all the inquality realations between terms
# for index, ineq in enumerate(inequalities):
# 	for s in sorted(list(set(ineq.lhs.subterms()))):
# 		for t in sorted(list(set(ineq.rhs.subterms()))):
# 			if is_true(model[term_compare['>'][s][t]]):
# 				print(index+1, ':', s.toString(False), '>', t.toString(False))
