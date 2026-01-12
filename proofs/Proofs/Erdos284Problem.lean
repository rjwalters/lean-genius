/-
  Erdős Problem #284

  Source: https://erdosproblems.com/284
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
  
  Let $f(k)$ be the maximal value of $n_1$ such that there exist $n_1<n_2<\cdots <n_k$ with\[1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.\]Is it true that\[f(k)=(1+o(1))\frac{k}{e-1}?\]
  
  
  
  The upper bound $f(k) \leq (1+o(1))\frac{k}{e-1}$ is trivial since for any $u\geq 1$ we have\[\sum_{u\leq n\leq eu}\frac{1}{n}=1+o(1),\]and hence if $f(k)=u$ then we must have $k\geq (e-1-o(1))u$.
  
  Essentially sol...

  Tags: 

  TODO: Implement proof
-/

import Mathlib

-- Placeholder theorem
-- Replace with actual statement and proof
theorem erdos_284 : True := by
  trivial

-- sorry marker for tracking
#check erdos_284
