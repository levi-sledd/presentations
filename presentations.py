### This file contains auxiliary functions for the manipulation of words, for the
### purpose of working with finitely presented groups.
### 
### For ease of writing, in this file we let ' denote "inverse."
### 
### The first goal is to create a program that enumerates all finitely presented 
### groups in shortlex order (up to a certain number), but in a "smart" way, avoiding
### presentations that generate isomorphic groups whenever possible. Note that it's 
### asking too much to enumerate all finitely presented groups without any isomorphic
### entries at all, since even the problem of determining whether a finite 
### presentation represents the trivial group is undecidable in general.  So we can 
### only catch "obviously isomorphic" entries--presentations that are redundant for 
### some trivial reason.
###
### So the goal is that the enumeration should:
###      1.  not include finitely presented groups that are obviously isomorphic to 
###          finitely presented groups that precede it in the list.  In particular, 
###          for each presentation:
###              a. each relation is "cyclically minimal," in the sense that it is
###                 first in shortLex order among all of its cyclic shifts and
###                 their inverses.
###              b. the list of relations is itself arranged in shortLex order.
###              c. each relation is freely and cyclically reduced.
###              d. no relations are included that make a generator obviously
###                 redundant.  In particular:
###                  i. no relations are of the form xw where x is a generator
###                     and w is a word not containing x or x'.           
###      2.  be built in an "on-line" way.  That is, instead of building a presentation
###          and then excluding it from the list because it's obviously isomorphic to a
###          previous one, wherever possible the program recognizes when a presentation
###          is going to be redundant and immediately stops building it and moves on to
###          the next one.
###
### Convention: we think of "the set of all generators" as being indexed by/indentified with
### the integers, where the negative of a number is identified with the inverse of its
### corresponding generator.  The integer 0 represents the group identity element 1.
### So generators are integers, and alphabets and words are lists of integers.
### For example, as a word [1, 2, -1, -2] = aba'b' or (x_1)(x_2)(x_1)'(x_2)', and as an
### alphabet [1, 2, -1, -2] = {a, b, a', b'} or {x_1, x_2, (x_1)', (x_2)'}.
###
### No error handling yet, assumptions about input are in the comments.

import copy

## Building the functions on lists that will eventually be turned into Word methods.

# Assumes n is a positive integer.
# Creates a symmetrized generating set with n generators and without the identity.
# Order matters here since we'll use this to enumerate words in shortLex order.
def standardAlphabet(n):
    alphabet = []
    for i in range(1, n+1):
        alphabet.extend([i, -i])
    return alphabet


# Assumes n is an integer such that |n| < len(list).
# Returns the cyclic shift of a list, rotated left by n (or right
# by -n, if n is negative).  
def cyclicShiftLeft(list, n=1):
    return list[n:] + list[:n]


# Returns a list of cyclic shifts of a list.
# Stops if a nontrivial shift of list is equal to list itself, in order
# to exclude redundant shifts of periodic lists.
def cyclicShifts(list):
    shifts = [list]
    for i in range(1, len(list)):
        if cyclicShiftLeft(list, i) == list:
            break
        shifts.append(cyclicShiftLeft(list, i))
    return(shifts)


# Assumes list is a list of numbers.  
# Returns the negatives of the numbers in the original list, in reverse order.
def inverse(list):
    inverse = []
    for i in range(1, len(list)+1):
        inverse.append(-list[len(list)-i])
    return inverse


# Assumes list is a list of numbers.  
# Returns the list of cyclic shifts and "inverses" of cyclic shifts of list.
def inverseCyclicShifts(list):
    shiftsAndInverses = []
    for shift in cyclicShifts(list):
        shiftsAndInverses.append(shift)
        shiftsAndInverses.append(inverse(shift))
    return shiftsAndInverses


# Assumes list is a list of numbers.
# Returns True if and only if no two successive numbers in list are negatives
# of each other, where the first element of list is considered to succeed the
# last element.
def isCyclicallyReduced(list):
    for i in range(len(list)):
        if list[i-1] == -list[i]:
            return False
    return True


# Assumes: 
#   - each element of list0 and list1 is a member of alphabet.
#   - alphabet does not have any repeated elements.
# Returns True if and only if list0 STRICTLY precedes list1 in shortLex order,
# where elements are ordered according to alphabet.
def shortLexPrecedes(list0, list1, alphabet):
    if list1 == []:
        return False
    elif list0 ==  []:
        return True
    elif list0[0] != list1[0]:
        return alphabet.index(list0[0]) < alphabet.index(list1[0])
    else:
        return shortLexPrecedes(list0[1:], list1[1:], alphabet)


# Assumes:
#   - every element of list is an element of alphabet.
#   - alphabet contains no repeated elements.
# Returns True if and only if list is shortLex least among all its
# cyclic shifts and their "inverses".
def isCyclicInverselyMinimal(list, alphabet):
    for shift in inverseCyclicShifts(list):
        if shortLexPrecedes(shift, list, alphabet):
            return False
    return True


# Assumes:
#   - every element of list is also an element of alphabet.
#   - alphabet contains no repeated elements.
# Returns the "odometer" successor of list: if the list
# is the lexicographically greatest possible list of that length
# according to alphabet, the odometer rolls over and its successor
# is the lexicographically-least list of the same length.
def odometerSuccessor(list, alphabet):
    if list == []:
        return []
    elif list[-1] != alphabet[-1]:
        return list[:len(list)-1] + [alphabet[alphabet.index(list[-1])+1]]
    else:
        return odometerSuccessor(list[:len(list)-1], alphabet) + [alphabet[0]]


# Assumes:
#   - every element of list is also an element of alphabet.
#   - alphabet contains no repeated elements.
# Returns the shortLex successor of list over alphabet.
def shortLexSuccessor(list, alphabet):
    if list == []:
        return [alphabet[0]]
    else:
        isAllLastLetter = True
        for i in range(len(list)):
            if list[i] != alphabet[-1]:
                isAllLastLetter = False
        if isAllLastLetter:
            return [alphabet[0]] + odometerSuccessor(list, alphabet)
        else:
            return odometerSuccessor(list, alphabet)


# Assumes k and n are positive integers.
# Returns the list of non-decreasing lists of positive integers
# whose sum is n.
def nondecreasingPartitionsStartingWith(k, n):
    partitions = []
    if k == n:
        partitions.append([n])
    elif k < n:
        for i in range(k, n-k+1):
            for smallerPartition in nondecreasingPartitionsStartingWith(i, n-k):
                partitions.append([k] + smallerPartition)
    return partitions


# Assumes n is a positive integer.
# Returns the list of non-decreasing lists of positive integers
# whose sum is n.
def nondecreasingPartitions(n):
    partitions = []
    for i in range(1, n+1):
        partitions = partitions + nondecreasingPartitionsStartingWith(i, n)
    return partitions


# Ad-hoc auxiliary function
# Assumes list is a list of numbers.
# Returns the list of nonzero absolute values of elements of list.
def positiveWithoutDuplicates(list):
    positives = []
    for number in list:
        if number != 0 and abs(number) not in positives:
            positives.append(abs(number))
    return positives


class Word:
    def __init__(self, alphabet, integerList):
        self.alphabet = alphabet
        self.asIntegerList = integerList

    # Assumes that all elements of alphabet are in range(-26, 27).
    def __str__(self):
        wordString = ''
        for integer in self.asIntegerList:
            if integer > 0:
                wordString = wordString + chr(96 + integer)
            elif integer == 0:
                wordString = wordString + "1"
            else:
                wordString = wordString + chr(96 - integer) + "'"
        return wordString
            
    # Assumes that all elements of alphabet are in range(-26, 27).
    def __repr__(self):
        wordString = ''
        for integer in self.asIntegerList:
            if integer > 0:
                wordString = wordString + chr(96 + integer)
            elif integer == 0:
                wordString = wordString + "1"
            else:
                wordString = wordString + chr(96 - integer) + "'"
        return wordString

    def cyclicShiftLeft(self, n=1):
        return Word(self.alphabet, cyclicShiftLeft(self.asIntegerList, n))

    def cyclicShifts(self):
        shifts = []
        for shiftedIntegerList in cyclicShifts(self.asIntegerList):
            shifts.append(Word(self.alphabet, shiftedIntegerList))
        return shifts


class Presentation:
    def __init__(self, generators, relations):
        self.generators = generators
        self.relations = relations

    # Assumes that all elements of generators are in range(-26, 27).
    def __str__(self):
        presentationString = '<'
        hasPositiveGenerators = False
        for positiveGenerator in positiveWithoutDuplicates(self.generators):
            presentationString += chr(96 + positiveGenerator) + ", "
        if presentationString[-2] == ',':
            presentationString = presentationString[:-2]
        presentationString += " | "
        for relation in self.relations:
            presentationString += str(relation) + ", "
        if presentationString[-2] == ',':
            presentationString = presentationString[:-2]
        presentationString +=">"
        return presentationString
        
    # Assumes that all elements of generators are in range(-26, 27).
    def __repr__(self):
        presentationString = '<'
        hasPositiveGenerators = False
        for positiveGenerator in positiveWithoutDuplicates(self.generators):
            presentationString += chr(96 + positiveGenerator) + ", "
        if presentationString[-2] == ',':
            presentationString = presentationString[:-2]
        presentationString += " | "
        for relation in self.relations:
            presentationString += str(relation) + ", "
        if presentationString[-2] == ',':
            presentationString = presentationString[:-2]
        presentationString +=">"
        return presentationString

# Assumes k and n are natural numbers.
# Returns a list of presentations with k generators and combined relation
# length of n.  For each partition of n, it lists all words of length n
# and then breaks them into multiple words following the partition.
# It's the "stupid" way of enumerating presentations because it doesn't
# weed out obviously redundant presentations, either before or after
# generating them.
# After this is done, a slightly smarter (but still stupid) enumeration
# can be built that uses this basic scheme, but doesn't add a presentation
# to the list unless it passes a series of checks that ensures it's not
# equivalent to a previous presentation in an obvious way.
def stupidEnumeratePresentations(k, n):
    pass


def main():
    # for i in range(3):
    #     print(standardAlphabet(i))
    # # []
    # # [1, -1]
    # # [1, -1, 2, -2]

    # list = [1, 2, 3, 4]

    # print(cyclicShiftLeft(list))
    # print(cyclicShiftLeft(list, 2))
    # print(cyclicShiftLeft(list, 3))
    # print(cyclicShiftLeft([]))
    # print(cyclicShiftLeft(list, -1))
    # print(cyclicShiftLeft(list, 5))
    # # [2, 3, 4, 1]
    # # [1, 2, 3, 4]
    # # [3, 4, 1, 2]
    # # [4, 1, 2, 3]
    # # []
    # # [4, 1, 2, 3]

    # print(cyclicShifts(list))
    # print(cyclicShifts([1, 1, 1]))
    # print(cyclicShifts([1, 0, 1, 0]))

    # print(inverse(list))

    # print(inverseCyclicShifts([1, 1, 1]))
    # print(inverseCyclicShifts([1, 0, 1, 0]))
    # print(inverseCyclicShifts(list))

    # print(isCyclicallyReduced([1, 2, -1]))
    # print(isCyclicallyReduced([1, 2, 1]))
    # # False
    # # True

    # alphabet = standardAlphabet(2)
    # print(shortLexPrecedes([1, -2, 2], [1, -2, 2, 1], alphabet))
    # print(shortLexPrecedes([1, -2, 2, 1], [1, -2, 2], alphabet))
    # print(shortLexPrecedes([1, -2, 2, 1], [1, -2, 2, 2], alphabet))
    # print(shortLexPrecedes([1, -2, 2, 1], [1, -2, 2, 1], alphabet))
    # # True
    # # False
    # # True
    # # False

    # print(isCyclicInverselyMinimal([1, 2, -2], alphabet))
    # print(isCyclicInverselyMinimal([-1, 2, -2], alphabet))
    # print(isCyclicInverselyMinimal([2, -1, 2], alphabet))
    # print(isCyclicInverselyMinimal([1, 1], alphabet))
    # # True
    # # False
    # # False
    # # True

    list = [0, 0, 0]
    alphabet = [0, 1]

    # for i in range(20):
    #     print(list)
    #     list = odometerSuccessor(list, alphabet)

    # list = []
    # for i in range(20):
    #     print(list)
    #     list = shortLexSuccessor(list, alphabet)

    # print(nondecreasingPartitionsStartingWith(4, 5))
    # print(nondecreasingPartitionsStartingWith(2, 4))
    # print(nondecreasingPartitionsStartingWith(1, 4))
    # # []
    # # [[2, 2]]
    # # [[1, 1, 1, 1], [1, 1, 2], [1, 3]]

    # print(nondecreasingPartitionsStartingWith(1, 6))
    # # [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 3]
    # #  [1, 1, 2, 2], [1, 1, 4], [1, 2, 3], [1, 5]]

    # print(nondecreasingPartitions(5))
    # # [[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 3], [1, 2, 2]
    # #  [1, 4], [2, 3], [5]]

    # word0 = Word([0, 1, -1, 2, -2], [0, 1, 2, -1, -2])
    # # print(word0)
    # # # 1aba'b'

    word1 = Word(standardAlphabet(3), [1, -2, 3, 1])
    # print([word0, word1])
    # # [1aba'b', ab'ca]

    word2 = Word(standardAlphabet(3), [3, 1, 2, 2, 3])
    word3 = Word(standardAlphabet(3), [1, 2, 3])

    # presentation0 = Presentation(standardAlphabet(3), [word1])
    # presentation1 = Presentation(standardAlphabet(3), [])
    # presentation2 = Presentation(standardAlphabet(3), [word1, word2, word3])
    # print(presentation0)
    # print([presentation0, presentation1, presentation2])
    # # <a, b, c | ab'ca>
    # # [<a, b, c, | a'ca>, <a, b, c | >, <a, b, c | a'ca, cabbc, abc>]

    # print(word2.cyclicShiftLeft())
    # print(word2.cyclicShiftLeft(2))
    # # abbcc
    # # bbcca

    print(word2.cyclicShifts())
    # [cabbc, abbcc, bbcca, bccab, ccabb]



main()
