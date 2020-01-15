#!/usr/bin/env python3

"""
SAT/SMT Solving Project

MoSIG HECS

Sudoku Solver using a custom DPLL solver

Student:  Nicolas AMAT
Professor: David MONNIAUX
"""

import sys
from collections import deque

class SudokuSolver:
	"""
	Sudoku Solver using DPLL
	"""
	
	def __init__(self, filename):
		# Grid initialization
		self.grid = [[[] for _ in range(9)] for _ in range(9)]
		self.initial_values = []
		
		# Grid size 
		self.n = 9
		self.s = 3

		# Parse input grid
		self.parseFile(filename)

	def parseFile(self, filename):
		"""
		Parse Sudoku grid
		"""
		try:
			with open(filename, 'r') as file:
				for l in file.readlines():
					value_indexed = l.replace('(', '').replace(')', '').replace('\n', '').split(',')
					i, j, val = int(value_indexed[0]) - 1, int(value_indexed[1]) - 1, int(value_indexed[2]) 
					self.initial_values.append((i, j, val))
					self.grid[i][j].append(val)
			file.close()

		except FileNotFoundError as e:
			exit(e)

	def addToBacktrack(self, i, j, value, backtrack):
		"""
		Add a suppressed value at case (i, j) into the backtrack dictionary
		"""
		if (i, j) in backtrack:
			backtrack[(i, j)].append(value)
		else:
			backtrack[(i,j)] = [value]

	def propagate(self, i, j, value, backtrack=None):
		"""
		Propagate a value at case (i, j) on the grid:
		- Remove other possible choices on this case
		- Propagate the value on the row
		- Propagate the value on the column
		- Propagate the value on the square
		- Add the supressed values in a dictionary (for backtracking)
		- Contradiction: if a case has no possible values return False
		- Recursive propagation: if a case has only one possible value, call this method on the case
		"""
		# Remove other possible values of the case
		if len(self.grid[i][j]) != 1:
			for element in self.grid[i][j]:
				if element != value:
					self.grid[i][j].remove(element)
					self.addToBacktrack(i, j, element, backtrack)

		# Line and column propagation
		for offset in range(9):
			# Line propagation
			if offset != j:
				if value in self.grid[i][offset]:
					# Remove the value and add it to the dictionary
					self.grid[i][offset].remove(value)
					if backtrack:
						self.addToBacktrack(i, offset, value ,backtrack)
					# Contradiction
					if len(self.grid[i][offset]) == 0:
						return False
					# Recursive propagation
					if len(self.grid[i][offset]) == 1:
						if (not self.propagate(i, offset, self.grid[i][offset][0], backtrack)):
							return False

			# Column propagation
			if offset != i:
				if value in self.grid[offset][j]:
					# Remove the value and add it to the dictionary
					self.grid[offset][j].remove(value)
					if backtrack:
						self.addToBacktrack(offset, j, value, backtrack)
					# Contradiction
					if len(self.grid[offset][j]) == 0:
						return False
					# Recursive propagation
					if len(self.grid[offset][j]) == 1:
						if (not self.propagate(offset, j, self.grid[offset][j][0], backtrack)):
							return False
		
		# Square propagation
		square_i = i // 3
		square_j = j // 3
		for offset_i in range(square_i * 3, square_i * 3 + 3):
			for offset_j in range(square_j * 3, square_j * 3 + 3):
				if offset_i != i and offset_j != j:
					if value in self.grid[offset_i][offset_j]:
						# Remove the value and add it to the dictionary
						self.grid[offset_i][offset_j].remove(value)
						if backtrack:
							self.addToBacktrack(offset_i, offset_j, value, backtrack)
						# Contradiction
						if len(self.grid[offset_i][offset_j]) == 0:
							return False
						# Recursive propagation
						if len(self.grid[offset_i][offset_j]) == 1:
							if (not self.propagate(offset_i, offset_j, self.grid[offset_i][offset_j][0], backtrack)):
								return False

		return True

	def choiceHeuristic(self):
		"""
		Find a case with a minimum of possible choices and select a value in this case
		"""
		min_variables = 10
		choice = (-1, -1, 0)

		for i in range(9):
			for j in range(9):
				# If the case does not contain any value, the grid is unsolvable
				if not len(self.grid[i][j]):
					exit("Grid unsolvable!")
				
				# Check if the case is a good candidate
				if len(self.grid[i][j]) != 1 and len(self.grid[i][j]) < min_variables:
					min_variables = len(self.grid[i][j])
					choice = (i, j, self.grid[i][j][0])
					# If the case contains only two values, stop here (impossible to find a better case)
					if (min_variables == 2):
						return choice

		return choice

	def findChoice(self, i, j, choices):
		"""
		Find a choice not already done for a giving cell
		"""
		for element in self.grid[i][j]:
			if element not in choices:
				choice = (i, j, element)
				return choice

		return (-1, -1, 0)

	def restore(self, backtrack):
		"""
		Restore a set of decisions
		"""
		for index, values in backtrack.items():
			for element in values:
				self.grid[index[0]][index[1]].append(element)

	def solveGrid(self):
		"""
		Solve Sudoku grid
		- Write SMTlib file
		- Solve using Z3
		- Fill Sudoku grid
		"""
		# Grid initialization
		for i in range(9):
			for j in range(9):
				if len(self.grid[i][j]) == 0:
					self.grid[i][j] = [val for val in range(1, 10)]

		# Propagate initial values
		for case in self.initial_values:
			self.propagate(case[0], case[1], case[2])

		# Data initialization for backtracking
		# Queue of past choices
		queue_choices = deque()
		# Queue of suppressed values
		queue_backtracks = deque()
		# Dictionary of the choices already made for each case
		choices_per_cells = dict()

		# Do a first choice
		choice = self.choiceHeuristic() 
		
		# While grid is not solved
		while(choice[2] != 0):

			# Initialization of dictionary containing the future suppressed variables for the current choice
			backtrack = dict()

			# Choice propagation
			i, j, value = choice[0], choice[1], choice[2]
			result = self.propagate(i, j, value, backtrack)
			
			# Update backtracking data
			queue_backtracks.append(backtrack)
			queue_choices.append((i, j, value))
			if (i, j) not in choices_per_cells:
				choices_per_cells[(i, j)] = [value]
			else:
				choices_per_cells[(i, j)].append(value)
			
			# Check if the past choice led to a contradiction
			if (result):
				# No contraction: make a new choice
				choice = self.choiceHeuristic()
			else:
				# Contradiction: backtrack
				find_one = False
				# While an other choice is not found continue backtracking
				while (queue_choices and not find_one):
					# Backtrack the last choice
					# Get the previous choice
					old_choice = queue_choices.pop()
					# Restore the previous suppressed values
					old_propagation = queue_backtracks.pop()
					self.restore(old_propagation)
					# Make a new choice on the case
					choice = self.findChoice(old_choice[0], old_choice[1], choices_per_cells[(old_choice[0], old_choice[1])])
					# Check if a new choice on this case was possible
					if choice[2] == 0:
						# Choice was not possible, delete the choices already made on this case and continue backtrackring
						del choices_per_cells[(old_choice[0],old_choice[1])]
					else:
						# New choice found, stop backtracking
						find_one = True

				# All possible exploration done, grid is unsolvable
				if not find_one:
					exit("Grid unsolvable!")
	
	def printGrid(self):
		"""
		Print Sudoku grid
		"""
		for line in self.grid:
			print("|", end = '')
			for element in line:
				if (len(element) == 1):
					print(element[0], end = '|')
				else:
					print('0', end = '|')
			print()
		print()


if __name__=='__main__':

	if (len(sys.argv) == 1):
		exit("File missing: ./sodoku <path_to_file>")
	
	solver = SudokuSolver(sys.argv[1])
	
	print("Initial grid:\n")
	solver.printGrid()
	solver.solveGrid()
	print("Solved grid:\n")
	solver.printGrid()
