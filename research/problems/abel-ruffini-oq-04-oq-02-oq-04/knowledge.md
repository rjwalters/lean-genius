# Knowledge Base: abel-ruffini-oq-04-oq-02-oq-04

**OQ**: the parent `solvable_iff_le_four` classifies `Sₙ` (solvable ⟺ n ≤ 4).
Extend the *paradigm* to other infinite families — dihedral `Dₙ` (solvable for
all n) and `GL₂(𝔽_q)` (not solvable once `|𝔽_q| ≥ 4`).
**Parent**: `abel-ruffini-oq-04-oq-02` ("S₂,S₃,S₄ Are Solvable: Complete
Classification"); Lean `Proofs/AbelRuffiniOQ04OQ02.lean`.

---

## Problem Understanding (S1 ORIENT, researcher-6, 2026-06-15)

Two clean, decidable extensions of the classification paradigm. Both verified by
the durable derived-series cert `verify_solvable_families.py` (decides `IsSolvable`
the definitional way: derived series `D₀=G`, `D_{k+1}=⟨[x,y]⟩`, solvable ⟺ some
`D_k = {1}`). All checks exit 0:

- **Dihedral `Dₙ` is solvable for every n**, with **derived length ≤ 2**
  (verified n=3..8). Structural reason: the rotation subgroup `R ≅ Cₙ` is cyclic
  (abelian ⇒ solvable) and normal of index 2, with quotient `Dₙ/R ≅ C₂` (abelian).
  So `Dₙ` is a cyclic-by-`C₂` extension — `[Dₙ,Dₙ] ≤ R` is abelian, hence
  `D⁽²⁾ = 1`.
- **`GL₂(𝔽_q)` solvability has a sharp boundary at `|𝔽_q| ≥ 4`** (verified on prime
  fields): `GL₂(𝔽₂)≅S₃` and `GL₂(𝔽₃)` (order 48) are **solvable** (derived lengths
  2 and 4); `GL₂(𝔽₅)` (order 480) is **NOT solvable** — its derived series
  stabilizes at the perfect core `SL₂(𝔽₅)` (order 120), because `PSL₂(𝔽₅) ≅ A₅` is
  simple non-abelian. (Boundary `q=4`: `PSL₂(𝔽₄) ≅ A₅` too, so `GL₂(𝔽₄)` is also
  non-solvable; not computed in the cert to avoid `GF(4)` arithmetic, but it makes
  the `|F| ≥ 4` threshold exact.)

---

## Mathlib inventory + formalization path (surveyed 2026-06-15, master + pin v4.26.0)

`Mathlib/GroupTheory/Solvable.lean` provides the full API. Confirmed bearers:
- `IsSolvable` (derived series eventually trivial); `isSolvable_of_comm`,
  `CommGroup.isSolvable` (abelian ⇒ solvable).
- `subgroup_solvable_of_solvable` (`:142`) — subgroup of solvable is solvable
  (⇒ contrapositive: a non-solvable subgroup ⇒ ambient non-solvable).
- `solvable_of_solvable_injective` (`:138`), `solvable_of_surjective` (`:145`),
  `solvable_quotient_of_solvable` (`:148`), `solvable_of_ker_le_range` (`:125`,
  the **extension lemma** — solvable-by-solvable is solvable).
- `Equiv.Perm.fin_5_not_solvable` (`:230`) and
  `Equiv.Perm.not_solvable (X) (5 ≤ #X)` (`:242`) — the non-solvability bearer
  (via `not_solvable_of_mem_derivedSeries`, `:224`).

**Dihedral side (Lean-tractable, ~80–150 LOC).** Mathlib has `DihedralGroup` but
**no `IsSolvable (DihedralGroup n)`** (`search/code` → 0 hits) — a genuine gap, and
an easy one. Two routes: (a) the rotation map `r : ZMod n → DihedralGroup n` is an
injective hom onto a normal index-2 subgroup; combine `CommGroup.isSolvable` on the
cyclic kernel with the `C₂` quotient via `solvable_of_ker_le_range`. (b) Show
`commutator (DihedralGroup n)` is abelian (it is `⟨r²⟩`) and apply the
derived-length-2 criterion. This is a clean, buildable contribution.

**GL side (BLOCKED for general `n,q`).** The clean Lean route for `q ≥ 4`:
`A₅ ↪ PSL₂(𝔽_q) ↪`-quotient, or `SL₂(𝔽_q) ≤ GL₂(𝔽_q)` with `SL₂` non-solvable, then
`subgroup_solvable_of_solvable` contrapositive. The blocker is the **simplicity of
`PSL₂(𝔽_q)`** (or non-solvability of `SL₂(𝔽_q)`), which Mathlib does **not** have
in usable form. A small-case alternative mirrors the cert: a `native_decide` oracle
that `GL₂(𝔽₅)` (concretely, `Matrix (Fin 2) (Fin 2) (ZMod 5)` units) is non-solvable
— but the derived-series `decide` over 480 elements may be heavy; the parent's
`Equiv.Perm.not_solvable` + an explicit `A₅ ↪ GL₂(𝔽₄)` embedding is the more
principled (if longer) path.

## Recommended ACT
Ship the **dihedral solvability** theorem first (`IsSolvable (DihedralGroup n)` for
all n) — it is a real, self-contained, ~100-LOC Mathlib-bearer-backed result and a
genuine upstream-worthy gap. Defer the GL non-solvability (needs `PSL₂` simplicity,
≫500 LOC) or land only the explicit `GL₂(𝔽₅)` small-case via the cert's
obstruction core.

## Dead Ends
- Treating `|𝔽_q| ≥ 4` as `q ≥ 4` *prime*: prime fields with ≥4 elements start at
  `q=5`; the `q=4` case needs `GF(4)` (a non-prime field) and `PSL₂(𝔽₄) ≅ A₅`. The
  threshold is about field *size*, not primality.

## Links
- Parent: [[abel-ruffini-oq-04-oq-02]] (S₂,S₃,S₄ solvable classification).
- Sibling galois/solvability survey vein:
  [[project-researcher-6-20260615-abelruffini-galois-oq040-mapapi-gap]].
