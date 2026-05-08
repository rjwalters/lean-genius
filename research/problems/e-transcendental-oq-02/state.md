# Current State

**Phase**: ACT — gallery entry built; 2 axioms tractable, 1 is the main open conjecture
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 3, researcher-11)
**Iteration**: 3

## Current Focus

Session 3 produced a **3-layer proof recipe** for the next-axiom-to-discharge
`rational_digits_eventually_periodic` (see `knowledge.md` heading "Session
2026-05-08 (Session 3) — Recipe for `rational_digits_eventually_periodic`").

The recipe:
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

Three remaining axioms (per `proofs/Proofs/ETranscendentalOQ02.lean`):
- `rational_digits_eventually_periodic` (line 209) — tractable. **Session 3 (2026-05-08)**
  produced a refined 3-layer recipe; see `knowledge.md`. Note: naive pigeonhole
  alone gives `f(i)=f(j)` but NOT periodic propagation. Use the iterate form
  `(· * b) : ZMod q.den → ZMod q.den` orbit pigeonhole instead.
- `normal_imp_irrational` (line 261) — derives from axiom 1 +
  `periodic_has_missing_ktuple` (already proved). Discharging axiom 1 first
  then proving 2 is the natural sequence.
- `e_absolutely_normal` (line 271) — the **main open conjecture**. Genuinely
  open as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a self-cycle
  symlink, so my Docker build attempts hung on `mathlib: cloning` for 14+ min.
  Closing axioms requires careful Mathlib API alignment that's risky without
  fast feedback. Future iterations may need to copy file to main repo and
  build there.

## Next Action

**ACT** — apply Session 3 recipe (`knowledge.md`) Layer 1: prove
`eventually_periodic_iterate` (a fintype-orbit pigeonhole lemma) as a
self-contained ~30–40 line lemma. It is the most reusable artifact and a
clean Mathlib contribution candidate (no module-specific dependencies).

Subsequent sessions: Layer 2 (~30–50 lines, ratResidue ZMod bridge) and
Layer 3 (~50–80 lines, nthDigit ↔ residue cast-bridge) — see
`knowledge.md` for the worked sketches.

## Attempt Counts

- Total attempts: 2 (Session 1 = entry built 2026-05-04; Session 1.5 = digit
  extension + axiomCount 4→3 via `periodic_has_missing_ktuple`; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe-only 2026-05-08).
- Current approach attempts: 0 (recipe stage; no proof attempted yet)
- Approaches tried: 0 for the rational-digits axiom; 1 successful approach
  for `periodic_has_missing_ktuple` (orbit cardinality, archived in
  `knowledge.md`).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:209` — `rational_digits_eventually_periodic`
- `proofs/Proofs/ETranscendentalOQ02.lean:261` — `normal_imp_irrational`
- `proofs/Proofs/ETranscendentalOQ02.lean:271` — `e_absolutely_normal`
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata (correct as of 2026-05-04)
