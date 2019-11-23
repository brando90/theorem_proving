import unittest
import sys

def split_iterative(list_pairs):
	unsplitted_list1 = []
	unsplitted_list2 = []
	for i in range(len(list_pairs)):
		##get elements
		pair = list_pairs[i]
		current_head_list1 = pair[0]
		current_head_list2 = pair[1]
		## append to new lists
		unsplitted_list1.append(current_head_list1)
		unsplitted_list2.append(current_head_list2)
	return unsplitted_list1, unsplitted_list2

def split(list_pairs):
	'''
	Takes a list of pairs and produces to lists.

	e.g. [(1,2),(3,4)]=>[1,3],[2,4]
	'''
	## base case
	if len(list_pairs) <= 0:
		return ([],[])
	## extract current pair head
	pair = list_pairs[0]
	first_element = pair[0]
	second_element = pair[1]
	## recurse
	first_new_list = [first_element] + split(list_pairs[1:])[0]
	second_new_list = [second_element] + split(list_pairs[1:])[1]
	return (first_new_list, second_new_list)

## tests

class TestStringMethods(unittest.TestCase):

	def test_iterative(self):
		test_list = [(1,2),(3,4)]
		answer_lists = [1,3], [2,4]
		answer_potential = split_iterative(test_list)
		self.assertEqual(answer_potential,answer_lists)

	def test_recursive(self):
		test_list = [(1,2),(3,4)]
		answer_lists = [1,3], [2,4]
		answer_potential = split(test_list)
		self.assertEqual(answer_potential,answer_lists)

if __name__ == '__main__':
	unittest.main()
