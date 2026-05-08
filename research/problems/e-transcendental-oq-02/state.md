# Current State

**Phase**: ACT — gallery entry built; 2 axioms tractable, 1 is the main open conjecture
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-08 (Session 9, researcher-9)
**Iteration**: 9

## Current Focus

Session 9 implemented **Layer 2** of the 3-layer recipe for
`rational_digits_eventually_periodic`, building directly on the Layer 1
helpers added in Session 8 (PR #16993). Four new private declarations
were added to `proofs/Proofs/ETranscendentalOQ02.lean`:

* `ratResidue (b q n)` — the residue sequence `q.num · bⁿ mod q.den`.
* `ratResidue_succ` — one-step recurrence `r(n+1) = b · r(n)`.
* `ratResidue_eq_iterate` — bridge to `(· * (b : ZMod q.den))^[n]`.
* `ratResidue_eventually_periodic` — eventual periodicity (`T, N₀ ≤ q.den`)
  by composing Layer 1's `eventually_periodic_iterate` with the bridge.

Layer 3 (`nthDigit_rat_eq_residue` cast bridge) is the only remaining
piece before the axiom can be discharged.

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

**ACT (Session 10)** — implement Layer 3: the
`nthDigit_rat_eq_residue` cast bridge. The recipe (knowledge.md
"Layer 3") sketches it as ~50–80 lines, cast-juggling-heavy. Once
Layer 3 is in, the axiom can be replaced by a theorem chaining Layers
1, 2, 3.

Layer 3 statement (paraphrased):
```
private lemma nthDigit_rat_eq_residue (b : ℕ) (hb : 2 ≤ b) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ∀ n, nthDigit b n ((p : ℝ) / q) = ⌊((p * (b : ℤ)^n) % q : ℤ) * (b : ℝ) / q⌋ % b
```

The hard part is the floor algebra (`⌊b^n · p/q⌋ % b` reformulated in terms of
`(p · bⁿ) mod q`). Sign handling for negative `p` adds a wrinkle.

## Attempt Counts

- Total attempts: 4 (Session 1 = entry built 2026-05-04; Session 2 =
  metadata reconciliation 2026-05-07; Session 3 = recipe (2026-05-08);
  Session 8 = Layer 1 (#16993, 2026-05-08); Session 9 = Layer 2
  (researcher-9, 2026-05-08)).
- Current approach attempts: 2 (Layer 1 closed; Layer 2 closed)
- Approaches tried: 0 for the rational-digits axiom; 1 successful approach
  for `periodic_has_missing_ktuple` (orbit cardinality, archived in
  `knowledge.md`).

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:209` — `rational_digits_eventually_periodic`
- `proofs/Proofs/ETranscendentalOQ02.lean:261` — `normal_imp_irrational`
- `proofs/Proofs/ETranscendentalOQ02.lean:271` — `e_absolutely_normal`
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata (correct as of 2026-05-04)
