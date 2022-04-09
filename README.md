# Automatic Verification
This repository contains all the projects I completed for the Computer-aided
Program Verification class I took at the Formal Methods in Computer Science
master's degree taught at Universidad Complutense de Madrid, where we were
taught Dafny and LiquidHaskell. Next, I will briefly explain what was done in
each session.

## [Session 1](/Session1)
Introductory session. Introduction to Dafny: writing predicates, functions and
methods and specification of methods.

## [Session 2](/Session2)

## [Session 3](/Session3)

## [Session 4](/Session4)

## [Session 5](/Session5)

## [Session 6](/Session6)

## [Session 7](/Session7)

## [Session 8](/Session8)

## [Session 9](/Session9)

## [Session 10](/Session10)

## [Session 11](/Session11)

## [Session 12](/Session12)

## [Session 13](/Session13)

## [Session 14](/Session14)

## [Session 15](/Session15)

## [Session 16](/Session16)

## [Session 17](/Session17)

## [Session 18](/Session18)
Introduction to LiquidHaskell and Liquid Types.

## [Session 19](/Session19)
Measures, verification of data types and simple example of verification of Skew
Heaps.

# Usage

## Dafny
In my case I used Dafny as a [Visual Studio Code extension](https://github.com/dafny-lang/ide-vscode)
that checks that your code is correctly verified everytime you save. You may
also use Dafny as a [CLI program](https://github.com/dafny-lang/dafny#try-dafny).

## LiquidHaskell
To check that the Haskell files are verified with LiquidHaskell (i.e., that
functions' types are correctly refined with Liquid Types) you just simply have
to locate in the desired folder (say `SessionX`) and run `stack build`, that is
```console
you@you:~$ cd SessionX
you@you:~/SessionX$ stack build
```

If everything is correct you may see an output line that starts with
`**** LIQUID: SAFE`.