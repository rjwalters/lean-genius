/-
  Erdős Problem #85

  Source: https://erdosproblems.com/85
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
  
  Let $n\geq 4$ and $f(n)$ be minimal such that every graph on $n$ vertices with minimal degree $\geq f(n)$ contains a $C_4$. Is it true that, for all large $n$, $f(n+1)\geq f(n)$?
  
  
  
  The function $f(n)$ is a reformulation of the Ramsey number $R(C_4,K_{1,n})$, in that\[R(C_4,K_{1,n})=\min\{ m : f(m)\leq m-n\}\]and\[f(n)=\min\{ m : m\geq R(C_4, K_{1,n-m})\}.\]The behaviour of this Ramsey number m...

  Tags: 

  TODO: Implement proof
-/

import Mathlib

-- Placeholder theorem
-- Replace with actual statement and proof
theorem erdos_85 : True := by
  trivial

-- sorry marker for tracking
#check erdos_85
