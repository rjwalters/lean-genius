# Knowledge Base: dissection-of-cubes-oq-04

**Problem**: Dehn Invariants for Platonic Solids: Cube Isolation
**Last Updated**: 2026-04-24
**Status**: COMPLETE (axiomCount 2→1; sole remaining axiom is tmul_infinite_order_ne_zero)

---

## Problem Understanding

Prove that among the five Platonic solids, only the cube has zero Dehn invariant.
Dihedral angles:
- Cube: π/2 (rational multiple of π → D=0)
- Tetrahedron: arccos(1/3)   — proved irrational in OQ02
- Octahedron:  arccos(-1/3)  — proved irrational in OQ02OQ02
- Dodecahedron: arccos(-1/√5) — proved irrational in OQ04 via Chebyshev mod-5
- Icosahedron: arccos(-√5/3) — proved irrational in OQ04 this session via coupled ℤ[√5] sequences

---

## Session 2026-04-24 (Session 1) — Complete: Proved icoAngle_irrational

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Fixed all 3 sorries in `DissectionOfCubesOQ04Aristotle.lean` using the
  `tmul_infinite_order_ne_zero` pattern (routine: unfold edgeTerm, mul_ne_zero, *_infinite_order)
- Proved `icoAngle_irrational` from scratch — converting from `axiom` to a proved `theorem`
- Reduced axiomCount from 2 to 1 (only tmul_infinite_order_ne_zero remains)

### Key Findings

- **Chebyshev ℤ[√5] approach**: For cos(icoAngle) = -√5/3, define
  f_n = A_n + B_n·√5 = 3^n·2cos(n·icoAngle) with integer recurrence:
    A_{n+2} = -10·B_{n+1} - 9·A_n
    B_{n+2} =  -2·A_{n+1} - 9·B_n
  Initial values: (A_0,B_0)=(2,0), (A_1,B_1)=(0,-2)

- **Mod-3 invariant**: ¬3|A_{2k} and ¬3|B_{2k+1} for all k.
  Key tactic: `IsCoprime.dvd_of_dvd_mul_left` to extract divisibility from coprime factor.

- **Inductive structure**: Need both halves of the invariant simultaneously in each step.
  The successor case proves ¬3|A_{2k+2} first (intermediate `have hA_new`), then uses it
  for ¬3|B_{2k+3}. A naive `refine ⟨?_, ?_⟩` then second case fails since `hA_new` not in scope.

- **Connection theorem** `icoSeqAB_eq_cos` proved by simultaneous induction on (n, n+1) pairs
  to avoid needing the n-2 value at step n.

- **Key tactic for algebra**: `linear_combination 2 * ((icoSeqAB (m+1)).2 : ℝ) * hsq`
  where `hsq : Real.sqrt 5 ^ 2 = 5` closes the LHS identity in icoSeqAB_eq_cos.

- **Parity contradiction**: `Nat.even_or_odd N` splits into even/odd.
  Even (N=2k): apply icoSeqAB_ndvd k for A_{2k}, contradicting 3|A_N.
  Odd (N=2k+1): B_N = 0 (from √5 irrationality) → 3|0 = 3|B_{2k+1}, contradicts ndvd.

- **√5 irrationality**: `Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)` — no extra imports.

### Files Modified

- `proofs/Proofs/DissectionOfCubesOQ04Aristotle.lean` — 3 sorries → proved
- `proofs/Proofs/DissectionOfCubesOQ04.lean` — axiom → proved theorem; Part IV-B added (~150 new lines)
- `src/data/proofs/dissection-of-cubes-oq-04/meta.json` — axiomCount 2→1, lineCount 432→581, theoremCount 15→22
- `src/data/research/problems/dissection-of-cubes-oq-04.json` — insights, builtItems, progressSummary

### Next Steps (for future sessions)

1. **tmul_infinite_order_ne_zero** (OQ02OQ02): ℝ flat over ℤ → only remaining axiom.
   Check if `Module.Flat` in Mathlib now covers `ℝ` as `ℤ`-module.
2. **Cross-solid comparison**: Can we show D(tetrahedron) ≠ D(icosahedron)?
   (Not just both nonzero, but D-values in different equivalence classes)

---

## Insights

1. The Chebyshev ℤ[√5] argument mirrors the Niven/ℤ argument for arccos(1/3)/π but in a
   quadratic extension. The mod-prime invariant becomes mod-3 on paired integer sequences.
2. `IsCoprime.dvd_of_dvd_mul_left` extracts divisibility from coprime-factor products.
3. Simultaneous induction on (n, n+1) pairs avoids needing the n-2 base case explicitly.
4. `linear_combination` with `sq_sqrt` closes ring-like identities involving √5^2 = 5.
5. `Nat.Prime.irrational_sqrt` works directly for proving √5 irrational.
6. In paired induction, prove the first component first as a named `have` before `refine ⟨?_, ?_⟩`.

---

## Dead Ends

- Direct `norm_num` for mod-3 invariant inductive step — doesn't handle the symbolic case.
- Separate `rcases Nat.even_or_odd` without precomputing B_N=0 first — causes circular reasoning.
