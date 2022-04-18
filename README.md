# Automatic Verification
This repository contains all the projects I completed for the Computer-aided
Program Verification class I took at the Formal Methods in Computer Science
master's degree taught at Universidad Complutense de Madrid, where we learned
about Dafny and LiquidHaskell. Next, I will briefly explain what was done in
each session.

## [Session 1](/Session1)
Introductory session. Introduction to Dafny: writing predicates, functions and
methods and specification of methods.

## [Session 2](/Session2)
Proving correctness of some mathematical functions.

## [Session 3](/Session3)
Proved some mathematical lemmas using induction.

## [Session 4](/Session4)
Verification of some methods on arrays and sequences.

## [Session 5](/Session5)
Verification of methods for summing the elements of arrays, sequences and
multisets.

## [Session 6](/Session6)
Verification of some methods on arrays.

## [Session 7](/Session7)
Verification of Binary Search, BubbleSort and SelectionSort.

## [Session 8](/Session8)
Verified InsertionSort and MergeSort.

## [Session 9](/Session9)
Verified QuickSort.

## [Session 10](/Session10)
Verified an improved version of QuickSort.

## [Session 11](/Session11)
Lists implemented as an algebraic data type.

## [Session 12](/Session12)
Verification of MergeSort on lists implemented as an algebraic data type.

## [Session 13](/Session13)
Verification of the algebraic data types of Binary Search Trees and Skew Heaps
implemented as trees.

## [Session 14](/Session14)
Verification of the algebraic data type of AVL Trees.

## [Session 15](/Session15)
Verification of lists as a class.

## [Session 16](/Session16)
Verification of Williams Heap implemented as a class.

## [Session 17](/Session17)
Verified methods using abstract classes (not caring about implementation
details).

## [Session 18](/Session18)
Introduction to LiquidHaskell and Liquid Types.

## [Session 19](/Session19)
Measures, verification of data types and a simple example of verification of
Skew Heaps.

## [Session20](/Session20)
Exercises from the 7th chapter of the [Liquid Haskell's tutorial](http://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_07_Measure_Int.html)
on Numeric Measures.

# Usage

## Dafny
In my case I used Dafny as a [Visual Studio Code extension](https://github.com/dafny-lang/ide-vscode)
that checks that your code is correctly verified everytime you save. You may
also use Dafny as a [CLI program](https://github.com/dafny-lang/dafny#try-dafny).

## LiquidHaskell
To check that the Haskell files are verified with LiquidHaskell (i.e., that
functions' types are correctly refined with Liquid Types) you just simply have
to locate in the desired folder (say, `SessionX`) and run `stack build`, that
is:
```console
you@you:~$ cd SessionX
you@you:~/SessionX$ stack build
```

If everything is correct you may see an output line that starts with
`**** LIQUID: SAFE`.
