#!/usr/bin/env python3

from z3 import *

x = Int('x')
y = Int('y')
solve(x > 2, y < 10, x + 2*y == 7)

a = Bool('a')
b = Bool('b')

solve(a,b)

t = ["toto_%d" % i for i in range(10)]
print(t)
