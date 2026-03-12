# Goemans-Williamson 0.878-Approximation for MaxCut

## Source
Gallery proof: `randomized-maxcut` (open question #1)

## Problem Statement
Can we formalize the Goemans-Williamson 0.878-approximation for MaxCut using semidefinite programming in Lean 4?

## Mathematical Context
The randomized MaxCut algorithm achieves a 1/2-approximation by randomly partitioning vertices. The Goemans-Williamson (1995) algorithm improves this to ~0.878 using semidefinite programming (SDP) relaxation and random hyperplane rounding. This was a breakthrough in approximation algorithms.

## Key Components
1. **SDP relaxation**: Relax discrete ±1 variables to unit vectors in Rⁿ
2. **Hyperplane rounding**: Choose random hyperplane to partition vectors
3. **Approximation ratio**: Show E[cut] ≥ 0.878 · OPT via arccos inequality
4. **The key inequality**: 2/π · arccos(vᵢ·vⱼ) ≥ 0.878 · (1 - vᵢ·vⱼ)/2

## Suggested Approach
1. Define the SDP relaxation for MaxCut
2. Formalize the hyperplane rounding scheme
3. Prove the approximation guarantee using the arccos inequality
4. Connect to the existing randomized MaxCut formalization

## Tractability
Challenging — requires formalizing SDP basics and the arccos inequality. The existing randomized MaxCut proof provides a foundation.

## Category
Extension of randomized MaxCut proof
