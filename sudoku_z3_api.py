#!/usr/bin/env python3

"""
SAT/SMT Solving Project

Sudoku Solver using z3 API

MoSIG HECS

Student:  Nicolas AMAT
Profesor: David MONNIAUX
"""

import sys
from z3 import Solver, Bool, Not, Or, unsat

class SodukuSolver:
	"""
	Sudoku Solver using z3 API
	"""

	def __init__(self, filename):
		# Grid size
		self.n = 9
		self.s = 3

		# Grid initialization
		self.grid = [[0 for j in range(self.n)] for i in range(self.n)]
		
		# Z3 solver instanciation
		self.solver = Solver()

		# Parse input file
		self.parseFile(filename)

	def parseFile(self, filename):
		"""
		Parse Sudoku grid
		"""
		try:
			with open(filename, 'r') as file:
				for l in file.readlines():
					value_indexed = l.replace('(', '').replace(')', '').replace('\n', '').split(',')
					self.grid[int(value_indexed[0]) - 1][int(value_indexed[1]) - 1] = int(value_indexed[2])
			file.close()

		except FileNotFoundError as e:
			exit(e)


	def solveGrid(self):
		"""
		Solve Sudoku grid
		- Add constraints using Z3 API
		- Solve using Z3 API
		- Fill Sudoku grid
		"""

		# Declare literals
		literals = [\
			[\
			[Bool("{}:{}:{}".format(i, j, value)) for value in range(self.n)]\
			for j in range(self.n)]\
			for i in range(self.n)]

		# Add constraints on cases
		for i in range(self.n):
			for j in range(self.n):
				self.solver.add(Or(literals[i][j]))

		for value in range(self.n):
			# Add constraints on rows
			for i in range(self.n):
				for j in range(self.n):
					for j_ in range(self.n):
						if j != j_:
							self.solver.add(Or(Not(literals[i][j][value]), Not(literals[i][j_][value])))

			# Add constraints on columns
			for j in range(self.n):
				for i in range(self.n):
					for i_ in range(self.n):
						if i != i_:
							self.solver.add(Or(Not(literals[i][j][value]), Not(literals[i_][j][value])))

			# Add constraints on squares
			for square_i in range(self.s):
				for square_j in range(self.s):
					for i in range(self.s):
						for i_ in range(self.s):
							for j in range(self.s):
								for j_ in range(self.s):
									if i != i_ and j != j_:
										self.solver.add(Or(Not(literals[square_i * self.s + i][square_j * self.s + j][value]), Not(literals[square_i * self.s + i_][square_j * self.s + j_][value])))

		# Add constraints on known values from the input grid
		for i in range(self.n):
			for j in range(self.n):
				if self.grid[i][j] != 0:
					self.solver.add(literals[i][j][self.grid[i][j] - 1])

		# Check if grid is solvable, otherwise exit
		if (self.solver.check() == unsat):
			solved = False
			exit("Grid unsolvable!")
		else:
			solved = True

			# Get the model
			m = self.solver.model()

			# Fill the grid from the model
			for i in range(self.n):
				for j in range(self.n):
					if self.grid[i][j] == 0:
						for value, literal in enumerate(literals[i][j]):
							if m.evaluate(literal):
								self.grid[i][j] = value + 1

		return solved
	
	def printGrid(self):
		"""
		Print Sudoku grid
		"""
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

	print("Initial grid:\n")
	solver.printGrid()
	if (solver.solveGrid()):
		print("Solved grid:\n")
		solver.printGrid()


