#!/usr/bin/env python3

"""
SAT/SMT Solving Project

Sudoku Solver using SMTlib2

MoSIG HECS

Student:  Nicolas AMAT
Profesor: David MONNIAUX
"""

import sys
import os
import subprocess

class SudokuSolver:
	"""
	Sudoku Solver using z3
	"""
	
	def __init__(self, filename):
		# Create SMTlib file
		self.smt_filename = "{}.smt2".format(filename)
		self.smt = open(self.smt_filename, 'w')
		
		# Grid size
		self.n = 9
		self.s = 3

		# Grid initialization
		self.grid = [[0 for j in range(self.n)] for i in range(self.n)]

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
		- Write constraints in SMTlib2 file
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
		for i in range(self.n):
			for j in range(self.n):
				for value in range(self.n):
					self.smt.write("(declare-const {} Bool)\n".format(literals[i][j][value]))
		
		# Add constaints on cases
		for i in range(self.n):
			for j in range(self.n):
				values = ""
				for value in range(self.n):
					values += literals[i][j][value] + " "
				self.smt.write("(assert (or {}))\n".format(values))

		for value in range(self.n):
			# Add constraints on rows
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

		# Add constraints on known values from the input grid
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
		proc = subprocess.Popen(['z3', '-smt2', self.smt_filename], stdout=subprocess.PIPE)

		# Check if grid is solvable
		if (proc.stdout.readline().decode('utf-8').strip() != 'sat'):
			solved = False
			print("Grid unsolvable!")

		else:
			solved = True

			# Read the model
			proc.stdout.readline()

			# Parse the model and fill the grid
			while(True):
				literal = proc.stdout.readline().decode('utf-8').strip().split('_')
				evaluation =  proc.stdout.readline().decode('utf-8').strip().replace(' ', '').replace(')', '')
				if (len(literal) == 0 or evaluation == '') and proc.poll() is not None:
					break
				if (evaluation == "true"):
					self.grid[int(literal[1])][int(literal[2])] = int(literal[3]) + 1 

		proc.poll()
		os.remove(self.smt_filename)

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
	
	solver = SudokuSolver(sys.argv[1])
	
	print("Initial grid:\n")
	solver.printGrid()
	if (solver.solveGrid()):
		print("Solved grid:\n")
		solver.printGrid()
