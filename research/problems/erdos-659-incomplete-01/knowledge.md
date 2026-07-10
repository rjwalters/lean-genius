# Knowledge: erdos-659-incomplete-01

## Session 2026-07-09 (researcher-3) — representability = norm of ℤ[√-2]; the "1 sorry" is a STALE FALSE POSITIVE

**Finding (integrity):** the problem title "Point Configurations with Few Distances (1 sorry)"
and the overview "Sorries: 1" are STALE/FALSE. All five Erdős-659 files are genuinely
sorry-free: `grep -nE '\bsorry\b'` matches only docstring occurrences of "sorry-free"
(Problem/OQ01/OQ01OQ02/OQ05) and "`sorry`-free" (OQ06). The real sorry was resolved on
2026-06-25 (researcher-10, `fourPointProperty_from_avoiding_configs`). The problem sits at its
axiomatized terminus: the only remaining assumptions are the deep Landau density axioms
(`moreeOsburnWorks` in Problem.lean; `uniform_landau_lower_bound`, `moreeosburn_upper_bound`
in OQ01.lean), genuinely out of reach in Mathlib 4.26 (no analytic density machinery).

**Added (Erdos659OQ05.lean):** `isRepresented_iff_isNorm` —
`IsRepresented n ↔ ∃ z : ℤ√(-2), Zsqrtd.norm z = n`. This identifies the integers represented
by `Q(x,y) = x²+2y²` with the *image of the norm map* on `ℤ[√-2]`, i.e. the conceptual reason
`isRepresented_mul` holds (`Zsqrtd.norm` is a monoid homomorphism → its image is
multiplicatively closed). Upgrades the coordinate-level composition law `Q_mul` to the
`Set.range Zsqrtd.norm` characterization. 1 theorem, 0 axioms, 0 sorries.

Proof: forward `rintro ⟨x,y,rfl⟩ ⇒ ⟨⟨x,y⟩, Q_eq_zsqrtd_norm x y⟩`; reverse
`rintro ⟨z,rfl⟩ ⇒ ⟨z.re, z.im, (Q_eq_zsqrtd_norm z.re z.im).symm⟩` (Zsqrtd structure eta:
`z` defeq `⟨z.re, z.im⟩`).

BUILD: UNVERIFIED. Docker fails fleet-wide at the image-build step (containerd meta.db I/O
error, operator-level corruption). High elaboration confidence — uses only the verified
`Q_eq_zsqrtd_norm` and structure eta. OQ05 counts: lineCount 125→142, theoremCount 9→10.

---

# Knowledge: erdos-659-incomplete-01

## Overview

Initial knowledge for problem `erdos-659-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-659` — Erdős Problem #659: Point Configurations with Few Distances
- Sorries: 1, Axioms: 1
- Tags: erdos, combinatorial-geometry, distance-problems, lattices

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-659/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos659`)

## Session 2026-06-25 (researcher-10)

### What was done
- Resolved the dangling sorry in `fourPointProperty_from_avoiding_configs`.
- Added verified lemmas `latticeDistSq_symm`, `latticeDistSq_nonneg`,
  `latticeDistSq_eq_zero_iff` (positive-definiteness of `x²+2y²`).
- Fixed five floating `/-- -/` doc-comments that prevented the file from
  parsing.
- meta.json: sorries 1→0, theoremCount 2→5, lineCount 220→280. Status
  remains `axiomatized` (badge `axiom`) — 1 axiom `moreeOsburnWorks`.

### Verified (lake env lean, EXIT 0)
- 0 sorries, 1 axiom.
- `#print axioms`: `fourPointProperty_from_avoiding_configs` and
  `latticeDistSq_eq_zero_iff` depend only on propext/Classical.choice/Quot.sound.
  `erdos_659` additionally depends on `moreeOsburnWorks` (as expected).

### Honest assessment
- The completion is modest: the deep content (Landau's theorem) stays
  axiomatized. Value added = removing a *false-as-stated* sorry and making
  its hypotheses sound, plus real (if small) verified algebra on the
  defining form.

## Session 2026-07-04 (researcher-8)

### Added (verified, no axioms/sorries)
- `repr_mul_identity`: `(a²+2b²)(c²+2d²) = (ac+2bd)² + 2(ad−bc)²` (composition
  identity for discriminant −8; norm form of ℤ[√-2]).
- `representable_mul`: representable set closed under multiplication.
- `one/two/three_representable`: 1, 2, 3 are representable.

### Status
- Still 0 sorries, 1 axiom (`moreeOsburnWorks`). Docker build EXIT 0.
- theoremCount 5→10, lineCount 280→322 (meta.json synced).

### Note on metric subtlety (for future work)
`isConfiguration` characterizations (`{a, a√2}`, `{a, a√3}`, `{a, aφ}`) implicitly
assume the *Euclidean* metric, but Lean's default `dist` on `ℝ × ℝ` is the sup/
Chebyshev metric. Sharpening those predicates properly requires switching to
`EuclideanSpace ℝ (Fin 2)` — a substantial refactor, deferred.

## Session 2026-07-08 (researcher-3) — Fix false, load-bearing axiom (card = n)

**Mode**: FRESH (claimed erdos-659-incomplete-01) · **Outcome**: soundness fix + partial axiom elimination

### The defect
`Erdos659Problem.lean` axiom `moreeOsburnWorks` asserted, for `S = moreeOsburnLattice n`,
that `S.card = n`. But the construction truncates to a box of side `k = Nat.sqrt(n/4)`, so
`S.card = (2k+1)²`, which is NOT `n` for almost all `n` (n=2,3 → 1 point; n=4 → 9 points).
This is a **false axiom** — a latent unsoundness — and it was **load-bearing**: the headline
`erdos_659` extracted `.1` from it to claim the family has exactly `n` points. (Same failure
mode as the pythagorean `r2_average_order` false axiom found earlier.)

### Why a naive "exactly n points" fix fails
Forcing `card = n` by taking an n-point subset of the box does NOT rescue the theorem: the
distinct-distance bound `≤ n/√(log n)` is what makes the result nontrivial, and a subset's
distance count bounds by the *box's* size `M ≥ n`, giving `M/√log M ≥ n/√log n` (wrong
direction). A collinear "n points on a line" fix is worse — it has ~n distances, violating the
few-distances bound. The √(log) saving is intrinsic to the genuine 2-D box.

### The fix (honest reindex by box side)
- Reindexed the family by the **box side `k`**: `moreeOsburnLattice k = (latticeBox k).image latticePoint`.
- Added `latticePoint_injective` (√2 ≠ 0 ⇒ `(a,b√2)` determines `(a,b)`) and
  `moreeOsburnLattice_card : card = (2k+1)²` — both **axiom-free** (`#print axioms`:
  only propext/Classical/Quot). The cardinality is now a *theorem*, removed from the axiom.
- `moreeOsburnWorks` now asserts only the two genuinely-deep facts (4-point property; distinct
  distances `≤ m/√(log m)` in the set's own size `m`) — TRUE and not Mathlib-reducible.
- `erdos_659` restated honestly: family is *arbitrarily large* (`∀N, ∃k, N ≤ card`, since
  `(2k+1)²→∞`), each with the 4-point property and `≤ card/√(log card)` distances. Depends only
  on `moreeOsburnWorks` (+ foundational). Still 1 axiom, 0 sorries — but the axiom is now sound.

### Verification
- `lake env lean` (4.26.0, main-repo cache): EXIT 0, no errors/warnings.
- `#print axioms`: `latticePoint_injective`, `moreeOsburnLattice_card` clean;
  `erdos_659` = [propext, Classical.choice, moreeOsburnWorks, Quot.sound] (no sorryAx/ofReduceBool).
- meta.json synced: leanFile lineCount 387→421, theoremCount 16→18 (axiomCount stays 1),
  section line refs + assumptions text updated.

### Key names
`Int.card_Icc` (`#(Icc a b)=(b+1-a).toNat`), `Finset.card_product`, `Finset.card_image_of_injective`,
`Nat.le_self_pow (hn:n≠0) m : m ≤ m^n`, `mul_right_cancel₀`.

## Session 2026-07-09 (researcher-7) — OQ01 axiom elimination + build repair (3→2 axioms)

**Mode**: AXIOM HUNT. Claimed `erdos-659-incomplete-01`; parent `Erdos659Problem.lean` at
terminus (1 deep axiom `moreeOsburnWorks`). Highest-value available work in the family:
`Erdos659OQ01.lean` carried **3 axioms**, one of which — `ndiv_sqrt_log_tendsto_infty`
(`Tendsto (fun n => n/√(log n)) atTop atTop`) — was **mislabeled**: it is a routine analytic
limit, NOT part of Landau's theorem.

**Done (VERIFIED, docker `[1931/1931]` green):**
- **Discharged `ndiv_sqrt_log_tendsto_infty` as a theorem** (axiom-free). Proof: for n≥2,
  `Real.log_le_sub_one_of_pos` ⇒ log n ≤ n ⇒ `Real.sqrt_le_sqrt` ⇒ √(log n) ≤ √n ⇒
  n/√(log n) ≥ n/√n = √n; and √n → ∞ (via `tendsto_atTop_atTop`, pick N = max 2 (⌈b⌉₊²+1),
  `Real.sqrt_sq`+`Nat.le_ceil` give b ≤ √n). OQ01 axiomCount **3→2**.
- **Build repair** (file had NOT compiled against current pin — broken since a Mathlib bump):
  - `import Mathlib.Analysis.Asymptotics.Asymptotics` no longer exists → split into Defs/Lemmas;
    changed to `import Mathlib.Analysis.Asymptotics.Lemmas`.
  - `isLittleO_iff` binder changed to **strict-implicit** `⦃c⦄` → `hcontra (c/2) (half_pos …)`
    became `hcontra (half_pos hc_pos)` (c inferred as c/2 from the `0 < c/2` proof).
  - Final contradiction `linarith` failed: `(c·n₀)/√L` and `n₀/√L` are distinct nonlinear
    atoms. Fixed by `set D := n₀/√L`, rewriting lower bound to `c·D` (via `ring`:
    `c*n₀/√L = c*(n₀/√L)`), then `nlinarith [mul_pos (half_pos hc_pos) hDpos, …]`.

**Verification:** `#print axioms ndiv_sqrt_log_tendsto_infty` = {propext, Classical.choice,
Quot.sound}; `no_improvement_possible` depends only on `uniform_landau_lower_bound` (+foundational).
meta.json synced: axiomCount 3→2, theoremCount 3→4, lineCount 207→251, assumptions + axioms-section
summary updated. Remaining 2 axioms (`uniform_landau_lower_bound`, `moreeosburn_upper_bound`) are the
genuinely-deep Landau bounds — out of session scope.

**Gotchas:** persistent SIGBUS-135 flakes + one corrupt dep `Data/List/Pairwise.ir` invalid-header
→ `docker-repair-cache.sh` (force cache get) then default-32GB build went green (reduced 24576 kept
135-flaking). Default memory beat reduced here.

## Session 2026-07-09 (researcher-1) — first lemmas for the counting function B₂ (VERIFIED green)

The counting function `B2(N) = (representable_x2_2y2 ∩ Set.Icc 1 N).ncard` (Landau's
∼c·N/√log N) was DEFINED but had NO lemmas. Added the two elementary unconditional facts:
- `B2_mono {N M} (h: N≤M) : B2 N ≤ B2 M` — `Set.ncard_le_ncard (Set.inter_subset_inter
  subset_rfl (Set.Icc_subset_Icc_right h)) ((Set.finite_Icc 1 M).inter_of_right _)`.
- `one_le_B2 {N} (hN: 1≤N) : 1 ≤ B2 N` — 1=1²+2·0² ∈ rep ∩ Icc 1 N ⟹ ncard>0 via
  `(Set.ncard_pos hfin).mpr ⟨1,hmem⟩` + omega.

Pure finiteness bookkeeping, 0 new axioms (independent of moreeOsburnWorks). Docker
**VERIFIED green** `✔ Built Proofs.Erdos659Problem (4.3s)` (3058 jobs, confirmed twice).
File 21→23 theorems, 482→511 lines (gallery meta leanFile synced). Reusable ncard API:
Set.ncard_le_ncard, Set.finite_Icc, Set.Finite.inter_of_right, Set.ncard_pos, Set.mem_Icc,
Set.Icc_subset_Icc_right, Set.inter_subset_inter subset_rfl.

Terminus unchanged: deep arithmetic characterization (primes ≡5,7 mod8 to even powers) =
axiom moreeOsburnWorks (Landau disc −8); representability elementary theory now essentially
complete (closure mul/pow/sq/2^k, mod-8 necessity, 35-counterexample, B₂ basics).
