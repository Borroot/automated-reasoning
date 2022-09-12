from z3 import *

x = Bool("x")
y = Bool("y")

solver = Solver()

solver.add(And(x, Not(y)))
solver.add(Not(y))

print(solver.check())
print("x =", solver.model()[x])
print("y =", solver.model()[y])
