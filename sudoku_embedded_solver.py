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
from collections import deque

class SudokuSolver:
	"""
	Sudoku Solver using DPLL
	"""
	
	def __init__(self, filename):
		self.smt_filename = "{}.smt".format(filename)
		self.smt = open(self.smt_filename, 'w')
		
		self.grid = [[[] for _ in range(9)] for _ in range(9)]
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
					self.grid[int(value_indexed[0]) - 1][int(value_indexed[1]) - 1].append(int(value_indexed[2]))
			file.close()

		except FileNotFoundError as e:
			exit(e)

	def addToBacktrack(self, i, j, value, backtrack):
		if (i, j) in backtrack:
			backtrack[(i, j)].append(value)
		else:
			backtrack[(i,j)] = [value]

	def propagate(self, i, j, value, backtrack):

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
					self.grid[i][offset].remove(value)
					self.addToBacktrack(i, offset, value ,backtrack)
					if len(self.grid[i][offset]) == 0:
						return False
					if len(self.grid[i][offset]) == 1:
						if (not self.propagate(i, offset, self.grid[i][offset][0], backtrack)):
							return False

			# Column propagation
			if offset != i:
				if value in self.grid[offset][j]:
					self.grid[offset][j].remove(value)
					self.addToBacktrack(offset, j, value, backtrack)
					if len(self.grid[offset][j]) == 0:
						return False
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
						self.grid[offset_i][offset_j].remove(value)
						self.addToBacktrack(offset_i, offset_j, value, backtrack)
						if len(self.grid[offset_i][offset_j]) == 0:
							return False
						if len(self.grid[offset_i][offset_j]) == 1:
							if (not self.propagate(offset_i, offset_j, self.grid[offset_i][offset_j][0], backtrack)):
								return False

		return True

	def choiceHeuristic(self):
		min_variables = 10
		choice = (-1, -1, 0)

		for i in range(9):
			for j in range(9):
				if len(self.grid[i][j]) != 1 and len(self.grid[i][j]) < min_variables:
					min_variables = len(self.grid[i][j])
					choice = (i, j, self.grid[i][j][0])
		return choice

	def findChoice(self, i, j, choices):
		for element in self.grid[i][j]:
			if element not in choices:
				choice = (i, j, element)
				return choice
		return (-1, -1, 0)

	def restore(self, backtrack):
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
		#Initialise
		for i in range(9):
			for j in range(9):
				if len(self.grid[i][j]) == 0:
					self.grid[i][j] = [val for val in range(1, 10)]

		initial_backtrack = dict()

		for i in range(9):
			for j in range(9):
				if len(self.grid[i][j]) == 1:
					self.propagate(i, j, self.grid[i][j][0], initial_backtrack)

		queue_backtracks = deque()
		queue_choices = deque()
		choices_per_cells = dict()

		choice = self.choiceHeuristic() 
		
		while(choice[2] != 0):
			backtrack = dict()
			i, j, value = choice[0], choice[1], choice[2]
			result = self.propagate(i, j, value, backtrack)
			
			queue_backtracks.append(backtrack)
			queue_choices.append((i, j, value))

			if (i, j) not in choices_per_cells:
				choices_per_cells[(i, j)] = [value]
			else:
				choices_per_cells[(i, j)].append(value)
			
			if (result):
				choice = self.choiceHeuristic()
			else:
				find_one = False
				while (queue_choices and not find_one):
					old_choice = queue_choices.pop()
					old_propagation = queue_backtracks.pop()
					self.restore(old_propagation)
					choice = self.findChoice(old_choice[0], old_choice[1], choices_per_cells[(old_choice[0], old_choice[1])])
					if choice[2] == 0:
						del choices_per_cells[(old_choice[0],old_choice[1])]
					else:
						find_one = True

				if not find_one:
					choice = self.choiceHeuristic()

	
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
					print(' ', end = '|')
			print()
		print()


if __name__=='__main__':

	if (len(sys.argv) == 1):
		exit("File missing: ./sodoku <path_to_file>")
	
	solver = SudokuSolver(sys.argv[1])
	
	solver.printGrid()
	solver.solveGrid()
	solver.printGrid()
