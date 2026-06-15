# ORIENT — Min-max scaffolding for Cauchy interlacing

**Author**: researcher-11, 2026-06-15 (iter 2, ORIENT phase)
**Status**: orientation only — no Lean shipped this iteration. Both proof
backends down (Docker build pool saturated at 3 concurrent `lean-build`
containers on the 7.65 GiB VM; Aristotle MCP `prove` → `Resource not found`).
This memo is a build-free deliverable that pins the Mathlib surface and the
proof decomposition so the next session (or Aristotle, when it returns) can go
straight to formalization.

## 1. What the theorem says (one-step interlacing)

Let `A : Matrix (Fin n) (Fin n) ℂ` be Hermitian with eigenvalues sorted
`λ₀ ≤ λ₁ ≤ ⋯ ≤ λ_{n-1}`, and let `B` be the principal `(n-1)×(n-1)` submatrix
obtained by deleting row/column `i`, with sorted eigenvalues
`μ₀ ≤ ⋯ ≤ μ_{n-2}`. Then for every `k` with `0 ≤ k ≤ n-2`:

```
λ_k ≤ μ_k ≤ λ_{k+1}.
```

This is the codimension-one case. The "delete `m` rows/cols" generalization
(`λ_k ≤ μ_k ≤ λ_{k+m}`) is a stretch goal and should NOT be attempted before
the one-step case lands.

## 2. The real obstacle is NOT the mathematics — it is missing Mathlib scaffolding

The math is classical (Courant–Fischer min-max + a dimension count). The
formalization gap, confirmed against the pinned tree, is:

1. **No sorted eigenvalue function.** `Matrix.IsHermitian.eigenvalues` returns
   eigenvalues indexed by the matrix's own index type and is **not** sorted.
   Interlacing is a statement about the *sorted* spectrum, so step 0 of any
   formalization is producing a monotone enumeration. Two routes:
   - reindex via a sorting permutation (`Tuple.sort` / `MonovaryOn` machinery),
     proving the reindexed tuple is `Monotone`; or
   - **(recommended)** state the theorem abstractly over *any* monotone tuple
     that enumerates the eigenvalue multiset, decoupling the interlacing
     inequality from the sorting bookkeeping. The sorting lemma then becomes an
     independent, separately-checkable obligation.

   > **VERIFY before relying on this**: confirm in the pinned Mathlib that
   > `Matrix.IsHermitian.eigenvalues` is unsorted and that no
   > `…sorted_eigenvalues` helper already exists. This claim is from prior
   > survey notes, not re-checked against the pin this iteration (host `.lake`
   > is an ELOOP symlink, so no local Mathlib grep was possible).

2. **No k-th Courant–Fischer min-max.** Mathlib's
   `Mathlib.Analysis.InnerProductSpace.Rayleigh` packages only the **extreme**
   eigenvalues via `iSup`/`iInf` of the Rayleigh quotient
   (`⨆ x, ⟪T x, x⟫ / ‖x‖²` = top eigenvalue, and the `iInf` dual). There is no
   `λ_k = ⨅_{dim S = k+1} ⨆_{x ∈ S} R(x)` statement. **This lemma is the
   keystone** and is independently reusable (Weyl inequalities, eigenvalue
   monotonicity under perturbation, Lidskii). Building it is the bulk of the
   work and is itself a worthwhile standalone contribution.

## 3. Proof decomposition (Courant–Fischer route, Approach A)

Once the min-max lemma exists, interlacing is short. Write
`R_A(x) = ⟪A x, x⟫ / ‖x‖²` for the Rayleigh quotient and identify `B` with the
restriction of `A` to the coordinate hyperplane `H_i = {x : x i = 0}`
(`dim H_i = n-1`). Then `R_B = R_A` restricted to `H_i`.

**Lower bound `λ_k ≤ μ_k`** (min over (k+1)-dim subspaces of a max):
```
μ_k = ⨅_{S ⊆ H_i, dim S = k+1} ⨆_{x ∈ S} R_A(x)
    ≥ ⨅_{S ⊆ ℂⁿ, dim S = k+1} ⨆_{x ∈ S} R_A(x) = λ_k,
```
because restricting the feasible subspaces to those inside `H_i` shrinks the
domain of the outer `⨅`, hence raises (or keeps) the infimum.

**Upper bound `μ_k ≤ λ_{k+1}`** (dual max-min form, the dimension count):
```
λ_{k+1} = ⨆_{dim S = k+1} ⨅_{x ∈ S} R_A(x)   -- dual Courant–Fischer
```
For any `(k+2)`-dim subspace `S ⊆ ℂⁿ`, `S ∩ H_i` has dimension `≥ k+1` (a
`(k+2)`-dim space meets a codimension-1 hyperplane in `≥ k+1` dims). Feeding
`S ∩ H_i` into `B`'s min-max gives `μ_k ≤ λ_{k+1}`. **Key lemma 2** is exactly
this `dim (S ∩ H_i) ≥ dim S - 1` fact — in Mathlib,
`Submodule.finrank_sup_add_finrank_inf_eq` /
`Submodule.finrank_le` give the inequality; the codim-1 input is
`finrank H_i = n - 1`.

## 4. Extreme cases are reachable TODAY from existing Rayleigh API

Before the general min-max lands, the boundary cases are provable from what
Mathlib already has and make good first PRs / good Aristotle targets:

- `k = 0` lower bound `λ₀ ≤ μ₀`: both are `iInf` Rayleigh quotients; `H_i ⊆ ℂⁿ`
  shrinks the domain ⇒ `iInf` over the smaller set is `≥`. Uses only the
  extreme-eigenvalue Rayleigh characterization.
- `k = n-2` upper bound `μ_{n-2} ≤ λ_{n-1}`: dual, both are `iSup` Rayleigh
  quotients over `H_i ⊆ ℂⁿ`.

These two pin down the endpoints of the interlacing chain without the k-th
min-max lemma and exercise the `H_i` restriction plumbing that the general case
needs anyway.

## 5. Proposed Lean statement (DRAFT — not yet build-checked)

Stated abstractly over monotone enumerations to decouple from the sorting
obligation (route 1-recommended above). **This has not been run through the
compiler** (Docker pool full); treat as a target to lift into
`proofs/Proofs/CauchyInterlacing.lean` after an API spot-check.

```lean
import Mathlib

open Matrix

/-- One-step Cauchy interlacing. `lamA`/`lamB` are monotone enumerations of the
sorted eigenvalues of `A` and of its principal submatrix `B = A.submatrix …`
(row/col `i` deleted). Stated abstractly over the sorted tuples; the link
"`lamA` is the sorted spectrum of `A`" is a separate obligation. -/
theorem cauchy_interlacing
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hA : A.IsHermitian)
    (i : Fin (n+1))
    (lamA : Fin (n+1) → ℝ) (lamB : Fin n → ℝ)
    (hlamA : Monotone lamA) (hlamB : Monotone lamB)
    (hA_spec : -- lamA enumerates A's eigenvalues, sorted
      sorry)
    (hB_spec : -- lamB enumerates (A deleting row/col i)'s eigenvalues, sorted
      sorry)
    (k : Fin n) :
    lamA k.castSucc ≤ lamB k ∧ lamB k ≤ lamA k.succ := by
  sorry
```

The two `hA_spec`/`hB_spec` `sorry`s are placeholders for the spectral linkage;
they must be replaced with concrete `Matrix.IsHermitian.eigenvalues`-based
statements once the sorted-enumeration helper (§2.1) is chosen. **Do not** ship
this file claiming verification until it compiles via
`./proofs/scripts/docker-build.sh Proofs.CauchyInterlacing`.

## 6. Recommended next actions (in order)

1. **API spot-check** (build-free, ~minutes once a tree is greppable): confirm
   the exact signatures of `Matrix.IsHermitian.eigenvalues`, the Rayleigh
   `iSup`/`iInf` lemmas, and whether any sorted-spectrum or min-max helper
   already exists. Update §2 accordingly.
2. **Formalize the two extreme cases** (§4) — smallest viable first PR; pure
   Rayleigh-quotient domain-restriction, no new min-max lemma. Good Aristotle
   job when the backend returns.
3. **Build the k-th Courant–Fischer min-max lemma** (§2.2) — the keystone;
   land it as its own contribution.
4. **Assemble interlacing** from the min-max lemma + the `dim (S ∩ H_i)` count
   (§3).

## 7. Honesty / scope notes

- Nothing here is machine-checked. No `.lean` shipped this iteration.
- The Mathlib-absence claims (no sorted eigenvalues, no k-th min-max) are
  carried from prior survey notes and are flagged for re-verification, not
  asserted as freshly confirmed.
- This is a genuine multi-session problem: the realistic unit of progress is
  one of the four steps in §6, not the whole theorem.
