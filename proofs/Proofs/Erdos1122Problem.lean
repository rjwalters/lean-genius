/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8942450f-e396-4846-97d7-20d51ef5dc57

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  Erdős Problem #1122

  Source: https://erdosproblems.com/1122
  Status: SOLVED
  

  Statement:
  Forum
  Favourites
  Tags
  More
   Go
   Go
  Dual View
  Random Solved
  Random Open
  
  Let $f:\mathbb{N}\to \mathbb{R}$ be an additive function (i.e. $f(ab)=f(a)+f(b)$ whenever $(a,b)=1$). Let\[A=\{ n \geq 1: f(n+1)< f(n)\}.\]If $\lvert A\cap [1,X]\rvert =o(X)$ then must $f(n)=c\log n$ for some $c\in \mathbb{R}$?
  
  
  
  Erd\H{o}s proved that $f(n)=c\log n$ for some $c\in\mathbb{R}$ if $A$ is empty, or if $f(n+1)-f(n)=o(1)$.
  
  Partial progress was made by Mangerel \cite{Ma22}, who ...

  Tags: 

  TODO: Implement proof
-/

import Mathlib


-- Placeholder theorem
-- Replace with actual statement and proof
theorem erdos_1122 : True := by
  trivial

-- sorry marker for tracking
#check erdos_1122