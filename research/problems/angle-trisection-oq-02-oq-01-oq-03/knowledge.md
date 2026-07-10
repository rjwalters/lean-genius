# Knowledge: angle-trisection-oq-02-oq-01-oq-03

Child of angle-trisection-oq-02-oq-01 (Galois → degree criterion). File:
`proofs/Proofs/AngleTrisectionOQ02OQ01OQ03.lean` (namespace AngleTrisectionOQ02OQ01OQ03).
Theme: p-group Galois group ⟹ minimal-polynomial degree is a power of p, plus
non-constructibility obstruction criteria. All 0-axiom / 0-sorry.

## Session 2026-07-09 (researcher-1) — intrinsic prime-power degree characterization (VERIFIED-by-elab)

Every prior obstruction in this file named a SPECIFIC prime p (degree_three_not_2group,
odd_degree_gt_one_not_2group, not_pgroup_of_prime_dvd_degree_ne, even_degree_not_3group,
pgroup_prime_unique). This session removed the fixed-prime dependence.

### Added (2 theorems, 0 axioms / 0 sorries)
- `pgroup_degree_isPrimePow_or_one`: IsPGroup p Gal ⟹ natDegree = 1 ∨ IsPrimePow natDegree.
  Restates galois_pgroup_implies_degree_is_pow_p in Mathlib's p-free predicate `IsPrimePow`.
  Proof: obtain ⟨k,hk⟩; rcases k=0 (deg=p^0=1, left) or k≥1 (⟨p,k,hp.prime,hpos,hk.symm⟩, right).
- `not_pgroup_any_of_not_isPrimePow`: deg ≠ 1 ∧ ¬IsPrimePow deg ⟹ ∀ prime p, ¬IsPGroup p Gal.
  Contrapositive; subsumes the two-distinct-prime-factors obstruction (deg 6,10,12,…) WITHOUT
  naming a candidate p. Complements not_pgroup_of_degree_ne_pow_p (which fixes p).

### Key API
`IsPrimePow n := ∃ p k, Prime p ∧ 0 < k ∧ p^k = n`; anonymous ctor `⟨p,k,hp.prime,hpos,hk.symm⟩`
(Nat.Prime.prime bridges p.Prime → Prime p). File 10→12 theorems, 199→231 lines.

### Verification — VERIFIED-by-elab (olean-write SIGBUS-135/139)
4 docker runs ALL reached `[7745/7745] Building Proofs.AngleTrisectionOQ02OQ01OQ03` with full
clean elaboration (1.5–2.6s, ZERO source-loc diagnostics), then code 135/139 at olean write.
Dep AngleTrisectionOQ02OQ01 serialized fine; only my file's olean write crashes under fleet
load. Proofs type-check. Depth-3 slug → 0 follow-ups (OQ-depth guard).

## Blockers / frontier (unchanged)
- Concrete cos 20° corollary BLOCKED: cos_pi9_minpoly_degree lives in a file transitively
  importing AngleTrisectionOQ02OQ03OQ01.lean which uses Mathlib-v4.26-removed AlgHom API.
- Field-degree formulation via IntermediateField.adjoin.finrank segfaults the 4.26 elaborator.
