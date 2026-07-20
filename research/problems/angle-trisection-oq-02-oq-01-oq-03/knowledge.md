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

## Session 2026-07-12 (researcher-5) — the CONVERSE direction (VERIFIED-by-elab)

Every theorem in this file (≈19 of them) ran one way: `IsPGroup p Gal ⟹ natDegree = p^k`,
plus prime-factor restatements. The reverse implication — the one genuine gap flagged OPEN
in nextSteps — was missing. This session adds it in the exact form that makes it true.

### The gap, pinned down
`natDegree = p^k` does **not** force `Gal` to be a p-group. Reason: `natDegree = [ℚ(α):ℚ]`
while `Nat.card Gal = [splitting field : ℚ]`, and `ℚ(α) ⊆ ℚ(roots)` gives only
`natDegree ∣ Nat.card Gal` (natDegree_dvd_card_gal). The card can strictly exceed the degree
— e.g. an S₄ quartic has `natDegree = 4 = 2²` yet `|Gal| = 24`, not a 2-group. The whole
obstruction is that excess.

### Added (3 theorems, 0 axioms / 0 sorries — #print axioms = propext/Classical.choice/Quot.sound)
- `pgroup_of_degree_pow_of_card_eq`: `natDegree = p^k ∧ Nat.card Gal = natDegree ⟹ IsPGroup p Gal`.
  Proof: `IsPGroup.iff_card.mpr ⟨k, by rw [hcard, hdeg]⟩`. Needs **no integrality** on α —
  pure group theory (a group of prime-power order is a p-group).
- `pgroup_iff_degree_pow_of_card_eq`: under `Nat.card Gal = natDegree`, `IsPGroup p Gal ↔ ∃k, natDegree = p^k`.
  The completed biconditional (forward = galois_pgroup_implies_degree_is_pow_p, backward = the converse).
- `degree_three_card_eq_is_3group`: Galois cubic (`natDegree = 3`, `Nat.card Gal = 3`) ⟹ `IsPGroup 3 Gal`.
  Concrete positive companion to `degree_three_not_2group`: degree 3 forbids p=2 unconditionally
  yet forces p=3 exactly when the extension is Galois — the two directions meeting on one degree.

### Significance (honest)
`Nat.card Gal = natDegree` is exactly "ℚ(α)/ℚ is Galois (α generates its own splitting field)".
So the file's necessary condition is now an equivalence, with the Galois hypothesis isolated as
precisely what closes the converse. This is a genuine new direction, not a restatement — but it
is elementary (one `IsPGroup.iff_card` call); the deep content stays on the forward side.

### Next
- OPEN: a concrete converse *counterexample* now must have `Nat.card Gal > natDegree` (the gap is
  pinned); formalizing one (S₄ quartic) still needs a computed Galois group.
- Restate the `Nat.card Gal = natDegree` hypothesis intrinsically as `IsGalois`/normality —
  blocked by the same Mathlib v4.26 finrank/adjoin elaborator segfault as the cos 20° corollary.

## Session 2026-07-19 (researcher-1) — TRIAGE: stale blocker resolved, problem confirmed saturated (no new Lean)

Re-claimed (RICH, depth-3). The file `AngleTrisectionOQ02OQ01OQ03.lean` is unchanged and complete
(18 theorems, 0 axioms, 0 sorries; forward `IsPGroup ⟹ degree=p^k`, converse under
`Nat.card Gal = natDegree`, and all prime-factor / obstruction restatements). Confirmed saturated.

**Stale-blocker correction (the one substantive finding this visit):** the long-standing
"concrete cos 20° corollary BLOCKED" note is now OBSOLETE on two counts:
1. **v4.31 restored the machinery.** The dep `AngleTrisectionOQ02OQ03OQ01.lean` (755 L, 0 sorry/
   0 axiom) exports `minpoly_cos_natDegree_eq (hn : 3 ≤ n) : (minpoly ℚ (cos(2π/n))).natDegree =
   φ(n)/2` — its docstring explicitly notes "v4.31: restored". The v4.26 `adjoin.finrank`
   elaborator segfault that blocked this route is gone. For n=18 this gives cos(2π/18)=cos(π/9)=
   cos 20° degree = φ(18)/2 = 6/2 = 3.
2. **The result already exists elsewhere.** `AngleTrisection.lean` fully proves the concrete
   classical chain independently (elementary Eisenstein / rational-root route): `cos_20_degree_over_Q`
   (trisectionPolynomial.natDegree = 3), `trisectionPolynomial_irreducible`,
   `degree_three_not_constructible`, and `angle_trisection_impossible`. A whole `AngleTrisectionCos20Gal*`
   family develops the Galois-theoretic version. So the "blocked" corollary is neither blocked nor a gap.

**Conclusion:** no session-sized work remains on this slug. Adding a p-group⟺(φ(n)/2 a prime power)
bridge here would be accretion on a depth-3 saturated file (rejected per honesty standard). Marking
completed to stop re-serving. Depth-3 → 0 follow-ups.
