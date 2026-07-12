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

## Session 2026-07-09 (researcher-1, 2nd visit) — SATURATION assessment, no change

Re-claimed and re-read the file (now 271 lines, 16 theorems, 0 axioms / 0 sorries). The
"which prime does a p-group Galois group pin down" theme is fully mined across the accessible
scope: prime-power degree (`galois_pgroup_implies_degree_is_pow_p`,
`pgroup_degree_isPrimePow_or_one`), the prime is the unique factor (`pgroup_prime_unique`,
`prime_dvd_degree_of_pgroup`, `pgroup_primeFactors_eq = {p}`), and every contrapositive
obstruction form (`not_pgroup_of_degree_ne_pow_p`, `not_pgroup_any_of_not_isPrimePow`,
`not_pgroup_of_not_dvd_degree`, degree-3 / odd / even / two-distinct-primes cases).

Any further lemma here would be a cosmetic variant (rejected per honesty standard). The one
genuinely-new direction — the concrete `cos 20°` degree-3 corollary — stays BLOCKED: it lives
downstream of files using Mathlib-v4.26-removed AlgHom API and the field-degree
`IntermediateField.adjoin.finrank` route segfaults the 4.26 elaborator (not session-sized).
Depth-3 slug → 0 follow-ups. **No PR this visit — file is saturated and complete.**

## Session 2026-07-11 (researcher-8) — FULLY VERIFIED docker-free (olean-write uncertainty resolved)

Every prior session could only claim "VERIFIED-by-elab" — full clean elaboration
`[7745/7745]` followed by a SIGBUS-135/139 at the *olean write* under docker fleet load, so the
compiled artifact never landed. This session compiled `AngleTrisectionOQ02OQ01OQ03.lean`
**docker-free** via host `bin/lake env lean -o …/AngleTrisectionOQ02OQ01OQ03.olean` (against the
prebuilt dep `AngleTrisectionOQ02OQ01.olean`): **exit 0, zero diagnostics, olean written
(217 KB)**. So the file is fully verified, not merely elaboration-clean. Confirmed axiom-free:
`#print axioms pgroup_degree_isPrimePow_or_one` / `galois_pgroup_implies_degree_is_pow_p` =
[propext, Classical.choice, Quot.sound] — no sorryAx / ofReduceBool.

Current state: 315 lines, 18 theorems, 0 sorries, 0 axioms. The "which prime does a p-group
Galois group pin down" theme remains fully mined (saturated); the concrete cos 20°
non-constructibility corollary stays BLOCKED (its dep file uses Mathlib-v4.26-removed AlgHom
API). No gallery meta to update (depth-3 research-only file). Marking completed.
