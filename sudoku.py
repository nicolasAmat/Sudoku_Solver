#!/usr/bin/env python3

"""
SAT/SMT Solving Project

MoSIG HECS

Student:  Nicolas AMAT
Profesor: David MONNIAUX
"""

import sys
import os
import subprocess
from z3 import Solver, Bool, Not, Or 

class SudokuSolver:
	"""
	Sudoku Solver using Z3
	"""
	
	def __init__(self, filename):
		self.smt_filename = "{}.smt".format(filename)
		self.smt = open(self.smt_filename, 'w')
		
		self.grid = [[0 for _ in range(9)] for _ in range(9)]
		self.n = 9
		self.s = 3

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
		- Write SMTlib file
		- Solve using Z3
		- Fill Sudoku grid
		"""

		# Create names of literals
		literals = [\
			[\
			["_{}_{}_{}_".format(i, j, value) for value in range(self.n)]\
			for j in range(self.n)]\
			for i in range(self.n)]

		# Declare literals
		for line in literals:
			for case in line:
				for value in case:
					self.smt.write("(declare-const {} Bool)\n".format(value))
		
		# Add constaints on cases
		for line in literals:
			for case in line:
				values = ""
				for value in case:
					values += value + " "
				self.smt.write("(assert (or {}))\n".format(values))

		for value in range(self.n):
			# Add constraints on lines
			for i in range(self.n):
				for j in range(self.n):
					for j_ in range(self.n):
						if j != j_:
							self.smt.write("(assert (or (not {}) (not {})))\n".format(literals[i][j][value], literals[i][j_][value]))

			# Add constraints on columns
			for j in range(self.n):
				for i in range(self.n):
					for i_ in range(self.n):
						if i != i_:
							self.smt.write("(assert (or (not {}) (not {})))\n".format(literals[i][j][value], literals[i_][j][value]))

			# Add constraints on squares
			for square_i in range(self.s):
				for square_j in range(self.s):
					for i in range(self.s):
						for i_ in range(self.s):
							for j in range(self.s):
								for j_ in range(self.s):
									if i != i_ and j != j_:
										self.smt.write("(assert (or (not {}) (not {})))\n".format(literals[square_i * self.s + i][square_j * self.s + j][value], literals[square_i * self.s + i_][square_j * self.s + j_][value]))

		# Add constraints on predifined values
		for i in range(self.n):
			for j in range(self.n):
				if self.grid[i][j] != 0:
					self.smt.write("(assert {})\n".format(literals[i][j][self.grid[i][j] - 1]))

		# Check satisfiability
		self.smt.write("(check-sat)")
		# Get model
		self.smt.write("(get-model)")

		self.smt.close()
		
		# Run Z3
		smt_result = subprocess.run(['z3', self.smt_filename], capture_output=True, text=True).stdout.split('\n')
		
		os.remove(self.smt_filename)

		# Exit if grid unsolvable
		if (smt_result[0] != 'sat'):
			exit("Grid unsolvable!")

		# Parse the model and fill the grid
		for line in range(2, len(smt_result), 2):
			evaluation = smt_result[line + 1].replace(' ', '').replace(')', '')
			if (evaluation == "true"):
				literal = smt_result[line].split('_')
				self.grid[int(literal[1])][int(literal[2])] = int(literal[3]) + 1 

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
	
	solver = SudokuSolver(sys.argv[1])
	
	solver.printGrid()
	solver.solveGrid()
	solver.printGrid()
