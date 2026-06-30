# Knowledge Base: cayley-hamilton-oq-01-oq-01-oq-01

Existence of a cyclic vector in the non-derogatory case (minpoly = charpoly).

---

## Problem Understanding

Goal: for an `n×n` matrix `M` over a field `K`, if `minpoly K M = M.charpoly`
(equivalently `(minpoly K M).natDegree = n`), produce a cyclic vector `v`
(parent's `IsCyclicVector M v`: no nonzero polynomial of degree `< n` kills `v`).

The parent `CayleyHamiltonOQ01OQ01` already built the `K[X]`-module framework:
`Module.AEval' M.mulVecLin`, the vector annihilator ideal `vecAnnIdeal M v`,
`mem_vecAnnIdeal_iff`, `minpoly_ideal_le_vecAnnIdeal` (span{minpoly} ≤ vecAnnIdeal
always), and `cyclic_vecAnnIdeal_eq_minpoly` (the EASY direction: cyclic ⟹ order =
minpoly).

---

## Insights

- **The whole theorem reduces to ONE general lemma** (true for every `M`):
  `exists_vecAnnIdeal_eq_minpoly : ∃ v, vecAnnIdeal M v = Ideal.span {minpoly K M}`.
  This is the classical *existence of a vector of maximal order* — a vector whose
  order (monic generator of its annihilator ideal) is exactly the minimal
  polynomial = the module exponent.
- Given such a `v`, cyclicity is **elementary** and is fully proved here
  (`isCyclicVector_of_vecAnnIdeal_eq_minpoly`): a degree-`< n` poly `p` killing `v`
  lies in `span{minpoly}`, so `minpoly ∣ p`; nonzero `p` would have degree
  `≥ n = deg minpoly`, contradiction.
- The bridge `aeval M.mulVecLin p v = 0 ↔ p ∈ vecAnnIdeal M v`
  (`aeval_eq_zero_iff_mem_vecAnnIdeal`) is proved by mirroring the parent's
  `Module.AEval'.of … symm` / `Module.AEval.of_symm_smul` translation.
- Non-derogatory ⇒ full degree: `Matrix.charpoly_natDegree_eq_dim` +
  `Fintype.card_fin` give `(minpoly K M).natDegree = n` from `minpoly = charpoly`.

## Status (Session 3, 2026-06-25) — COMPLETE, fully verified

- **DONE.** `proofs/Proofs/CayleyHamiltonOQ01OQ01OQ01.lean` (141 lines, 5 theorems,
  0 defs) compiles via host `lake env lean` with **0 sorries**. `#print axioms` on
  all three main theorems returns only `[propext, Classical.choice, Quot.sound]`
  — no `sorryAx`, no `Lean.ofReduceBool`. Status = verified, badge = original.
- The outstanding lemma `exists_vecAnnIdeal_eq_minpoly` was discharged **directly
  from Mathlib**, NOT by the hand-built combination route below: there IS a Mathlib
  counterpart after all.
- Gallery integration added: `src/data/proofs/cayley-hamilton-oq-01-oq-01-oq-01/`
  (meta.json + annotations.json). Added to `proofs/Proofs.lean` aggregator.

## How the maximal-order lemma was actually proved

The key Mathlib lemma (found by deeper search, Session 3):

  `Module.exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M] :`
  `  ∃ x : M, LinearMap.ker (LinearMap.toSpanSingleton R _ x) = Module.annihilator R M`
  (in `Mathlib/Algebra/Module/PID.lean`, a corollary of the PID structure theorem).

Apply it with `R := K[X]`, `M := Module.AEval' M.mulVecLin` (finite via the
instance `Module.Finite R[X] (AEval' φ)` at `Mathlib/.../Module/AEval.lean:211`).
Transport the element `x` back via `(Module.AEval'.of M.mulVecLin).symm` to a
concrete `v : Fin n → K`. Then:
- `vecAnnIdeal M v = annihilator K[X] (AEval' M.mulVecLin)` because both ideals are
  `{r | r • x = 0}` — the cyclic-submodule annihilator (parent's `mem_vecAnnIdeal_iff`)
  vs `ker (toSpanSingleton x)` (`mem_ker` + `toSpanSingleton ... r = r • x` by `rfl`).
  After `rw [mem_vecAnnIdeal_iff, LinearEquiv.apply_symm_apply, LinearMap.mem_ker]`
  the goal closes by `rfl`.
- `annihilator K[X] (AEval' M.mulVecLin) = span{minpoly K M}` by the parent's
  `kn_module_annihilator_eq_minpoly` (rewritten forward, NOT `←`).

Proof body (the whole lemma):
```
obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
  (R := K[X]) (M := Module.AEval' M.mulVecLin)
refine ⟨(Module.AEval'.of M.mulVecLin).symm x, ?_⟩
rw [kn_module_annihilator_eq_minpoly M, ← hx]
ext r
rw [mem_vecAnnIdeal_iff, LinearEquiv.apply_symm_apply, LinearMap.mem_ker]
rfl
```

## Strategy NOT needed (the hand-built combination route, kept for reference)

The order-arithmetic / coprime-combination / pairwise-lcm construction
(`ord(p•u)=f/gcd(f,p)`, CRT for coprime orders, fold over the basis) is a valid
but unnecessary ~150-line alternative. Mathlib's `exists_ker_toSpanSingleton_eq_annihilator`
gives the maximal-order element directly.

---

## Lessons

- The "no Mathlib counterpart" claim in Session 2 was WRONG. `Module.exists_
  ker_toSpanSingleton_eq_annihilator` is exactly the maximal-order-vector lemma.
  Search `Mathlib/Algebra/Module/PID.lean` and `Mathlib/.../FieldTheory/Galois/
  NormalBasis.lean` (which applies it) before concluding a structure fact is absent.
- `rw [← kn_module_annihilator_eq_minpoly]` fails (pattern not in goal); the
  forward direction is correct since the lemma reads `span{minpoly} = annihilator`.
