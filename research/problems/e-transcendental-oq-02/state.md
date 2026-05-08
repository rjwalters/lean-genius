# Current State

**Phase**: ACT — `rational_digits_eventually_periodic` axiom eliminated;
1 tractable axiom remains, 1 is the main open conjecture
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 10, researcher-1)
**Iteration**: 10

## Current Focus

Session 10 closed **Layer 3** — the cast bridge from `nthDigit` to
integer residues — and used it to discharge the
`rational_digits_eventually_periodic` axiom. **AxiomCount: 3 → 2.**

Three new private lemmas + one new theorem (replacing the axiom) added to
`proofs/Proofs/ETranscendentalOQ02.lean` (~75 lines, 427 → 502):

* `floor_pow_rat_eq_ediv` — ℝ→ℚ→ℤ cast bridge:
  `⌊b^n · (q : ℝ)⌋ = (q.num · b^n) / q.den` via `Rat.floor_cast` +
  `Rat.floor_int_div_nat_eq_div`.
* `nthDigit_succ_via_residue` — digit at position `n+1` is determined by
  the integer residue `(q.num · b^n) % q.den`. Proof: Euclidean
  decomposition `b · X = b · (X%q) + (b · (X/q)) · q` plus
  `Int.add_mul_ediv_right` + `Int.add_mul_emod_self_left`.
* `nthDigit_succ_eq_of_emod_eq` — equal residues at `n, m` ⇒ equal digits
  at `n+1, m+1` (one-line composition).
* `theorem rational_digits_eventually_periodic` — composes Layers 1+2+3,
  with `ZMod.intCast_eq_intCast_iff'` bridging ZMod equality to integer
  residue equality. Pre-period grows by `+1` due to off-by-one shift.

The previously-axiomatized signature is preserved (with `_hb : 2 ≤ b`
unused — the proof works for any base).

Earlier session context (Session 9 closed Layer 2; Session 8 closed
Layer 1; Session 3 produced the recipe).

Earlier session context (Session 3 produced the recipe):
- Surveys Mathlib 4.26 API for "fintype ⇒ eventually periodic" (named lemma is
  missing; must be assembled from `Fintype.exists_ne_map_eq_of_card_lt` +
  iterated `Function.iterate_add_apply`).
- Corrects a subtle error in the naive pigeonhole approach (bare pigeonhole
  gives `f(i)=f(j)` but NOT `f(i+k)=f(j+k)`; the iterate form
  `g^[i] x₀ = g^[j] x₀` ⇒ `g^[i+k] x₀ = g^[j+k] x₀` is what's actually needed).
- Decomposes the proof into 3 independently-buildable layers totaling ~150–200
  lines:
  - Layer 1 (~30–40 lines): `eventually_periodic_iterate` general lemma.
  - Layer 2 (~30–50 lines): `ratResidue` definition + ZMod q bridge.
  - Layer 3 (~50–80 lines): `nthDigit_rat_eq_residue` cast-bridge.
- Identifies that `n ↦ b^n · p mod q` IS the orbit of `(· * b) : ZMod q → ZMod q`,
  making the iterate-form pigeonhole the right abstraction (not the bare pigeonhole
  that the original axiom docstring sketched).

Session 3 made no `.lean` edits and did not run a Docker build — recipe-only
deliverable, following the konigsberg-oq-01-oq-02 Session 7 precedent.

## Active Approach

The current Lean entry establishes the framework:
- Definitions: `nthDigit`, `IsNormalInBase`, `IsAbsolutelyNormal`.
- 28 theorems: includes `e_floor`, `e_floor_10..1000000000`, `e_digit1..9`
  (proves first 9 decimal digits 2.718281828 from `Real.exp_one_gt_d9` /
  `Real.exp_one_lt_d9`), `e_normal_implies_uniform_decimal_digits`,
  `periodic_has_missing_ktuple` (orbit cardinality).

Two remaining axioms (per `proofs/Proofs/ETranscendentalOQ02.lean`):
- ~~`rational_digits_eventually_periodic`~~ — **PROVED 2026-05-08 (Session 10).**
  Discharged via Layer 1 (orbit pigeonhole on ZMod q.den) + Layer 2
  (residue sequence ratResidue) + Layer 3 (cast bridge from nthDigit to
  integer residue). Now a `theorem` rather than an `axiom`.
- `normal_imp_irrational` (next target, ~50 lines) — now reduces directly
  to (proved) `rational_digits_eventually_periodic` +
  `periodic_has_missing_ktuple` + `Tendsto` frequency contradiction.
  No new axioms needed.
- `e_absolutely_normal` — the **main open conjecture**. Genuinely
  open as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a self-cycle
  symlink, so my Docker build attempts hung on `mathlib: cloning` for 14+ min.
  Closing axioms requires careful Mathlib API alignment that's risky without
  fast feedback. Future iterations may need to copy file to main repo and
  build there.

## Next Action

**ACT (Session 11)** — discharge `normal_imp_irrational`. Now that
`rational_digits_eventually_periodic` is a theorem, this should reduce to:

1. Take rational `x = q : ℚ`. Apply (proved) `rational_digits_eventually_periodic`
   to get `T, N₀`.
2. Pick `k` with `b^k > T`. Apply `periodic_has_missing_ktuple` (proved
   2026-05-04) to get a missing `k`-tuple `s₀`.
3. The frequency of `s₀` after position `N₀` is `0` (string never appears),
   so its `count(s₀, N) ≤ N₀`, hence `count/N → 0`.
4. `IsNormalInBase b q` requires `count/N → b^(-k) > 0`. Contradiction.

Expected effort: ~50 lines of `Tendsto` + cast manipulation. No new
axioms. Likely 1 focused session.

After this: only `e_absolutely_normal` (the genuinely-open conjecture)
remains axiomatized.

## Attempt Counts

- Total attempts: 5 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (#17016, 2026-05-08); Session 10 = Layer 3 + axiom discharge,
  researcher-1, 2026-05-08).
- Current approach attempts: 1 (Layer 3 closed first try, pending CI
  verification)
- Approaches tried: 1 successful for `rational_digits_eventually_periodic`
  (3-layer composition: Layer 1 + Layer 2 + Layer 3); 1 successful for
  `periodic_has_missing_ktuple` (orbit cardinality, Session 1.6, archived
  in `knowledge.md`).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:209` — `rational_digits_eventually_periodic`
- `proofs/Proofs/ETranscendentalOQ02.lean:261` — `normal_imp_irrational`
- `proofs/Proofs/ETranscendentalOQ02.lean:271` — `e_absolutely_normal`
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata (correct as of 2026-05-04)
