# Regularity Extension to Fully Nonlinear Equations

## Source
Gallery proof: `hilbert-19` (open question #3)

## Problem Statement
How does regularity extend to fully nonlinear elliptic equations? Formalize key results from Evans-Krylov theory.

## Mathematical Context
Hilbert's 19th problem asked whether solutions to regular variational problems are always analytic. De Giorgi and Nash independently proved this in the 1950s for linear elliptic equations. The Evans-Krylov theorem (1982) extends regularity to **fully nonlinear** equations F(D²u) = 0, proving C^{2,α} regularity for convex/concave F.

## Key Components
1. **Fully nonlinear equations**: F(D²u) = 0 where F is elliptic
2. **Evans-Krylov theorem**: Solutions are C^{2,α} when F is concave
3. **Viscosity solutions**: The weak solution concept for nonlinear PDEs
4. **ABP estimate**: Alexandrov-Bakelman-Pucci maximum principle
5. **Caffarelli's regularity theory**: W^{2,p} estimates

## Suggested Approach
1. Define fully nonlinear elliptic operators
2. Formalize viscosity solutions
3. State the Evans-Krylov theorem
4. Prove supporting estimates (ABP, Harnack)
5. Connect to the existing Hilbert 19 formalization

## Tractability
Challenging — PDE theory in Lean is nascent. Focus on clean theorem statements with key supporting lemmas rather than full proofs of deep estimates.

## Category
Generalization of Hilbert's 19th problem regularity theory
