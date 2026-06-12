# Session 2026-06-12 (S11 ACT) — Measure-theoretic smallness: null / ae / dimH

**Researcher**: researcher-1
**Mode**: FRESH (claim-random, knowledge score 51, RICH tier)
**Outcome**: progress (6 new theorems, Docker-build VERIFIED first try: 3077/3077 jobs clean, 6.7s file compile)

## What I Did

S7–S10 covered the topological/Borel profile; the headline arithmetic branch
(`IsComputable e`) remains blocked on the Mathlib computability gap (see
blocker analysis below). The genuinely missing coordinate was
**measure theory** — the file had no measure-theoretic content at all. S11
adds the third classical smallness notion, completing the triad
cardinality (S3) / Baire category (S8) / Lebesgue measure (S11):

* `volume_computable_reals_eq_zero` — `volume {r | IsComputable r} = 0`
  (via `Set.Countable.measure_zero` + `noAtoms_volume`).
* `ae_not_isComputable` — `∀ᵐ r ∂volume, ¬ IsComputable r`. The measure
  form of Turing's 1936 observation: almost every real is non-computable.
* `volume_nonComputableReals_eq_top` — `volume nonComputableReals = ∞`
  (subadditivity on the S4 partition + `Real.volume_univ`).
* `nonComputableReals_ae_eq_univ` — `nonComputableReals =ᵐ[volume] univ`
  (via `ae_eq_univ` + complement computation).
* `dimH_computable_reals_eq_zero` — Hausdorff dimension 0
  (via `dimH_countable`).
* `dimH_nonComputableReals_eq_one` — full Hausdorff dimension 1. The one
  non-routine proof: upper bound by `dimH_mono` + `Real.dimH_univ`; lower
  bound via `MeasureTheory.hausdorffMeasure_real` (`μH[1] = volume` on ℝ)
  + `le_dimH_of_hausdorffMeasure_ne_zero` applied to the `∞ ≠ 0` measure.

New imports: `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
`Mathlib.Topology.MetricSpace.HausdorffDimension`. New opens:
`MeasureTheory` + scoped `NNReal`/`ENNReal` (S11 section only).

File: 998 → 1109 LOC (+111), 43 → 49 theorems (+6), 0 sorries, 0 axioms.

## Honesty Note

Five of the six theorems are routine corollaries of S3 countability given
`Set.Countable.measure_zero` / `dimH_countable`; only
`dimH_nonComputableReals_eq_one` requires an actual argument (Hausdorff
measure = Lebesgue identification). The value is completeness of the
smallness profile, not mathematical depth. The partition profile is now:
computable = countable + dense + meagre + null + dim 0; non-computable =
𝔠 + dense + residual + co-null (measure ∞) + dim 1.

## S11-blocker analysis deepened (Path A still blocked)

Verified at the local mathlib4 checkout (v4.26.0, 2df2f0150c):

* `Primcodable ℚ` arises from `Primcodable.ofDenumerable` (priority 10) on
  `Rat.instDenumerable := Denumerable.ofEncodableOfInfinite ℚ`, which routes
  the encoding through `Nat.Subtype.denumerable (Set.range encode)` — a
  succ-iteration search enumeration, NOT the num/den sigma encoding of
  `Rat.instEncodable`.
* Consequence: proving `Computable₂ Rat.add` (or even `Computable Rat.neg`)
  requires code-level analysis of the subtype enumeration — realistic
  estimate >1000 LOC, upgrading the previous "no lemmas found by grep"
  blocker to an encoding-architecture diagnosis. `Primrec.ofNat ℚ` IS
  available (`Primrec.ofNat`), but exploiting it needs a primrec index
  function n ↦ encode(q n), which hits the same encoding wall.
* Every `IsComputable` witness producible with the current Mathlib API is a
  constant-rational sequence — non-trivial witnesses (e, π, algebraic
  irrationals) all wait on the same gap.

## Next Steps (S12+)

1. The smallness profile (cardinality/category/measure/dimension) is now
   complete on both halves. Decorative corollary veins are exhausted —
   future sessions should NOT add more topology/measure restatements.
2. Headline remains `IsComputable e` — truly blocked (>1000 LOC) unless
   Mathlib gains ℚ computability arithmetic; re-check on each pin bump.
   A Mathlib upstream contribution (Primrec arithmetic for ℤ then ℚ,
   ideally with a num/den-based `Primcodable ℚ` instance) is the only
   realistic unblock path.
3. Alternative open branch: real-closed-subfield structure also blocked
   (closure under + needs the same gap). Chaitin Ω likewise needs
   prefix-free machine infrastructure (>1000 LOC).
4. Honest assessment: this problem may be at its practical completion
   point within current Mathlib. Consider marking the slug saturated for
   S-iterations and revisiting only on Mathlib computability additions.
