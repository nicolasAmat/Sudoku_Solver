#!/usr/bin/env python3

from z3 import *

N = 9
S = 3

grid = [\
	[-1, 3, 1, -1, -1, -1, -1, 4, 6],\
	[-1, -1, 4, 6, -1, -1, -1, 9, 5],\
	[-1, -1, -1, -1, -1, 8, -1, -1, 7],\
	[-1, -1, -1, 1, -1, -1, -1, -1, 4],\
	[-1, -1, -1, 2, -1, 9, -1, -1 ,-1],\
	[9, -1, -1, -1, -1, 3, -1, -1, -1],\
	[4, -1, -1, 5, -1, -1, -1, -1, -1],\
	[3, 8, -1, -1, -1, 1, 4, -1, -1],\
	[2, 6, -1, -1, -1, -1, 7, 5, -1]\
      ]

s = Solver()

literals = [\
		   [\
		   [Bool("{}:{}:{}".format(i, j, value)) for value in range(N)]\
		   for j in range(N)]\
           for i in range(N)]

for i in range(N):
	for j in range(N):
		s.add(Or(literals[i][j]))

for value in range(N):
	for i in range(N):
		for j in range(N):
			for j_ in range(N):
				if j != j_:
					s.add(Or(Not(literals[i][j][value]), Not(literals[i][j_][value])))

	for j in range(N):
		for i in range(N):
			for i_ in range(N):
				if i != i_:
					s.add(Or(Not(literals[i][j][value]), Not(literals[i_][j][value])))

	for square_i in range(S):
		for square_j in range(S):
			for i in range(S):
				for i_ in range(S):
					for j in range(S):
						for j_ in range(S):
							if i != i_ and j != j_:
								s.add(Or(Not(literals[square_i * S + i][square_j * S + j][value]), Not(literals[square_i * S + i_][square_j * S + j_][value])))

for i in range(N):
	for j in range(N):
		if grid[i][j] != -1:
			s.add(literals[i][j][grid[i][j] - 1])

if (not s.check()):
	print(s.check())
	exit(0)

m = s.model()

for i in range(N):
	for j in range(N):
		if grid[i][j] == -1:
			for value, literal in enumerate(literals[i][j]):
				if m.evaluate(literal):
					grid[i][j] = value + 1

for i in range(N):
	print("{} {} {} {} {} {} {} {} {}".format(grid[i][0], grid[i][1], grid[i][2], grid[i][3], grid[i][4], grid[i][5], grid[i][6], grid[i][7], grid[i][8]))



