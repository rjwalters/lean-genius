# Knowledge Base: ehrhart-cube-proven-oq-01

**Problem**: Can the simplex Ehrhart polynomial L(Δ^d, n) = C(n+d, d) be proved axiom-free?

**Status**: COMPLETE — PR #16233 (S1: main proof, merged) → S2: polynomial form

---

## Session 2026-05-06 (Session 1) - Full Proof Completed

**Mode**: FRESH | **Outcome**: completed

### What I Did
- Modeled simplex lattice points as `Sym (Fin (d+1)) n` (multisets of size n over {0,...,d})
- Used `Sym.card_sym_eq_choose` + `Nat.choose_symm_of_eq_add` for main theorem
- Proved 14 theorems, 0 sorries, 0 axioms in `EhrhartSimplexProven.lean`
- Docker build: exit code 0 ✓. Gallery entry created. PR #16233 submitted (merged).

### Key Findings
- `Sym (Fin (d+1)) n` is the multiset model: element 0 = slack, element k = coordinate k
- Core: `Sym.card_sym_eq_choose` → `C(n+d, n)`, then `Nat.choose_symm_of_eq_add` → `C(n+d, d)`
- Interior: shift yᵢ = xᵢ-1 gives `Sym (Fin (d+1)) (n-d-1)` with count C(n-1, d)
- Pascal recursion: `Nat.choose_succ_succ (n+d+1) d`
- 1D simplex = 1D cube (both n+1 points); diverge from 2D

### Files Modified
- `proofs/Proofs/EhrhartSimplexProven.lean` (158 lines, 14 theorems)
- `src/data/proofs/ehrhart-cube-proven-oq-01/` (gallery entry)

---

## Session 2026-05-08 (Session 2) - Polynomial Form Extension

**Mode**: REVISIT (problem was COMPLETED; pool entry stale at "in-progress")
**Outcome**: completed

### What I Did
- Confirmed PR #16233 merged 2026-05-06; pool entry stale at "in-progress" (claim leaked)
- Added Section VII "Polynomial Form" to `EhrhartSimplexProven.lean`
- Three new theorems exhibit L(Δ^d, n) as a degree-d polynomial in n via three
  equivalent closed forms (descFactorial, ascFactorial, ∏-range)
- Plus three concrete `native_decide` examples in low dimensions
- All proofs are 1–2 lines, axiom-free, leveraging existing Mathlib API

### New Theorems
- `simplex_count_descFactorial`: count·d! = (n+d).descFactorial d  -- (n+d)(n+d−1)···(n+1)
- `simplex_count_ascFactorial`: count·d! = (n+1).ascFactorial d    -- (n+1)(n+2)···(n+d)
- `simplex_count_prod`:         count·d! = ∏ i ∈ range d, (n+1+i)   -- explicit product

Concrete examples:
- 2D triangle at n=3:    2! · 10  = 4 · 5
- 3D tetrahedron at n=2: 3! · 10  = 3 · 4 · 5
- 4D pentachoron at n=2: 4! · 15  = 3 · 4 · 5 · 6

### Key Findings
- `Nat.descFactorial_eq_factorial_mul_choose : n.descFactorial k = k.factorial * n.choose k`
  is the Mathlib bridge from binomial → descending factorial; one-line corollary.
- `Nat.ascFactorial_eq_factorial_mul_choose : (n+1).ascFactorial k = k.factorial * (n+k).choose k`
  is the ascending-factorial counterpart, more natural for Ehrhart polynomial form
  because the roots at n = −1, …, −d are visible directly.
- `Nat.ascFactorial_eq_prod_range : n.ascFactorial k = ∏ i ∈ range k, (n + i)` makes
  the product form a one-rewrite corollary.
- The polynomial structure (degree d in n, leading coefficient 1/d!) is now explicit
  without needing to lift to a `Polynomial`-typed object.

### Why This Matters
This was the missing structural complement to the cube file's `cube_ehrhart_poly`
(which exhibits L(cube, n) = (n+1)^d as a polynomial). With both cube and simplex
sides of the Ehrhart correspondence carrying explicit closed-form polynomial
expressions — not just cardinality identities — the gallery now has uniform first-
principles foundations for Ehrhart theory in the canonical cases, without invoking
the general `ehrhart_poly` axiom.

### Files Modified
- `proofs/Proofs/EhrhartSimplexProven.lean` (207 → 268 lines, +3 theorems +3 examples)
- `src/data/research/problems/ehrhart-cube-proven-oq-01.json` (status, knowledge)
- `research/problems/ehrhart-cube-proven-oq-01/{state,knowledge}.md`

### Follow-Up Open Questions

**OQ-01 (DEFER)**: Generalize to product polytopes — show L(P × Q, n) = L(P,n) · L(Q,n).
  Direction: lift via `Sym (Fin a) n × (Fin b → Fin (n+1))`; use `Fintype.card_prod`.
  Significance 5/10, tractability 7/10. Concrete next step: `simplex_times_cube_count`.

**OQ-02 (DEFER)**: Polynomial-typed lift — define `Polynomial.simplexEhrhart d : ℕ[X]`
  with `(simplexEhrhart d).eval n = L(Δ^d, n)`, via `(X+1).ascPochhammer / d!`.
  Requires `Polynomial.ascPochhammer_eval_eq_ascFactorial` + Polynomial coefficient work.
  Significance 7/10, tractability 5/10.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
