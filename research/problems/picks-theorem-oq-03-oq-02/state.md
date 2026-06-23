# Research State: picks-theorem-oq-03-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
Answered the OQ "is the h*-vector determined by the face lattice?" — NO. Reeve
tetrahedra T_h = conv{(0,0,0),(1,0,0),(0,1,0),(1,1,h)} share the face lattice
(f-vector (4,6,4,1), L(1)=4) but have distinct h*-vectors (1,0,h−1,0). Directly
ties to the parent Pick's theorem (Reeve = the 3D Pick obstruction).

## Active Approach
Build-free ORIENT (Docker + Aristotle down). Durable exact verifier
`verify_hstar_not_combinatorial.py` (all checks pass).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Lean ACT Docker-gated, and Ehrhart theory is absent from Mathlib (no
  Ehrhart/hStarVector); a general formalization is a multi-file build.

## Next Action
ACT (next Docker session): a LIGHT refutation — define L_{T_h} for the concrete
Reeve family (closed form / decide), compute h*(T_h)=(1,0,h−1,0), prove
h*(T_1) ≠ h*(T_2) alongside a face-lattice isomorphism T_1 ≅ T_2. Avoid building
general Ehrhart theory.
