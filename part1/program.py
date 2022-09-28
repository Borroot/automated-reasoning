from collections import namedtuple
from z3 import *

loops = 10

Vars = namedtuple("Vars", list("abc"))
v = Vars(
        *[[Int("{}{}".format(v, i)) for i in range(loops + 1)] for v in "ab"],
        [Bool("c{}".format(i)) for i in range(loops)]
)

solver = Solver()

# initialise all the variables to 1
solver.add(v.a[0] == 1)
solver.add(v.b[0] == 1)

# increase i with 1 every iteration
for it in range(1, loops + 1):
    solver.add(Implies(v.c[it - 1], And(
        v.a[it] == v.a[it - 1] + 2 * v.b[it - 1],
        v.b[it] == v.b[it - 1] + it
    )))
    solver.add(Implies(Not(v.c[it - 1]), And(
        v.b[it] == v.a[it - 1] + v.b[it - 1],
        v.a[it] == v.a[it - 1] + it
    )))

# simulate just to be sure of correctness
def simulate(decisions, n):
    a = 1
    b = 1
    for i in range(1, loops + 1):
        if decisions[i - 1]:
            a = a + 2 * b
            b = b + i
        else:
            b = a + b
            a = a + i
    return b == 700 + n

# check final condition
for n in range(1, 11):
    solver.push()

    solver.add(v.b[loops] == 700 + n)
    solvable = solver.check()

    print("n =", n, "is", solvable, end="")
    if solvable == sat:
        print(" -> crash", end=" ")
        decisions = [is_true(solver.model()[v.c[i]]) for i in range(loops)]
        if simulate(decisions, n): print("verified")
        else: print("WRONG")
    else:
        print()

    solver.pop()
