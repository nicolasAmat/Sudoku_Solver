#!/usr/bin/env python3

import sys
from math import sqrt
from z3 import Solver, Bool, Not, Or 

class SodukuSolver:

	def __init__(self, filename):
		self.grid = []
		self.n = 0
		self.s = 0
		self.solver = Solver()
		self.parseFile(filename)
		self.checkGrid()

	def parseFile(self, filename):
		try:
			with open(filename, 'r') as file:
				for l in file.readlines():
					self.grid.append(l.replace('\n', '').split('|'))
			file.close()

		except FileNotFoundError as e:
			exit(e)

	def checkGrid(self):
		self.n = len(self.grid)
		for line in self.grid:
			if len(line) != self.n:
				exit("Grid not valid!")
		self.s = int(sqrt(self.n))

	def solveGrid(self):
		literals = [\
			[\
			[Bool("{}:{}:{}".format(i, j, value)) for value in range(self.n)]\
			for j in range(self.n)]\
			for i in range(self.n)]

		for i in range(self.n):
			for j in range(self.n):
				self.solver.add(Or(literals[i][j]))

		for value in range(self.n):
			for i in range(self.n):
				for j in range(self.n):
					for j_ in range(self.n):
						if j != j_:
							self.solver.add(Or(Not(literals[i][j][value]), Not(literals[i][j_][value])))

			for j in range(self.n):
				for i in range(self.n):
					for i_ in range(self.n):
						if i != i_:
							self.solver.add(Or(Not(literals[i][j][value]), Not(literals[i_][j][value])))

			for square_i in range(self.s):
				for square_j in range(self.s):
					for i in range(self.s):
						for i_ in range(self.s):
							for j in range(self.s):
								for j_ in range(self.s):
									if i != i_ and j != j_:
										self.solver.add(Or(Not(literals[square_i * self.s + i][square_j * self.s + j][value]), Not(literals[square_i * self.s + i_][square_j * self.s + j_][value])))

		for i in range(self.n):
			for j in range(self.n):
				if self.grid[i][j] != '.':
					self.solver.add(literals[i][j][int(self.grid[i][j]) - 1])

		if (not self.solver.check()):
			exit(0)

		m = self.solver.model()

		for i in range(self.n):
			for j in range(self.n):
				if self.grid[i][j] == ".":
					for value, literal in enumerate(literals[i][j]):
						if m.evaluate(literal):
							self.grid[i][j] = value + 1
							
	def printGrid(self):
		for line in self.grid:
			print("|", end = '')
			for element in line:
				print(element, end = '|')
			print()
		print()


if __name__=='__main__':
	if (len(sys.argv) == 1):
		exit("File missing: ./sodoku <path_to_file>")
	solver = SodukuSolver(sys.argv[1])
	solver.printGrid()
	solver.solveGrid()
	solver.printGrid()


