/-
# Shannon AWGN water-filling, oq-03-oq-01 — the wideband ceiling is the supremum

Source: `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean` (namespace
`ShannonWaterFilling`), which proves for `n` identical parallel Gaussian channels
of noise `c > 0` sharing a total power `P`:

* `rate_equalNoise_le_wideband` — every finite `n` is capped: `(n/2)·log(1+P/(n·c)) ≤ P/(2c)`;
* `rate_equalNoise_tendsto_wideband` — the rates converge up to that cap:
  `(n/2)·log(1+P/(n·c)) → P/(2c)` as `n → ∞`.

This file upgrades that *tendsto + ceiling* pair to the explicit **least-upper-bound**
statement: `P/(2c)` is the supremum over the channel count `n` of the equal-noise rates,

    `⨆ n, (n/2)·log(1 + P/(n·c)) = P/(2c)`   (for `P ≥ 0`, `c > 0`).

The proof needs neither differentiability nor monotonicity in `n`: the ceiling makes
`P/(2c)` an upper bound (so the family is bounded above and the `⨆` is a genuine LUB),
while the wideband limit forces the supremum up to `P/(2c)` — the limit of a sequence
lying below `P/(2c)` cannot leave any room below the supremum.  Together with the
per-`n` ceiling this shows Shannon's infinite-bandwidth AWGN capacity `P/(2c)` is
*attained in the limit and never exceeded* — the sharp supremum, not merely a limit.

All results are axiom-free / sorry-free.

Tags: information-theory, shannon, awgn, water-filling, capacity, supremum, wideband
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01EqualNoise

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open scoped BigOperators
open Filter Topology

/-! ## The per-`n` wideband ceiling, stated for the sequence `n : ℕ`

`rate_equalNoise_le_wideband` bounds `(Fintype.card ι / 2)·log(1 + P/(card·c))`.
The natural-number restatement `rate_equalNoise_seq_le_wideband`, including the
degenerate `n = 0` case (where the rate is `0`), now lives upstream in
`ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean` (imported above) so it lines up
with the sequence used in `rate_equalNoise_tendsto_wideband`; we reuse it directly
below rather than redeclaring it here. -/

/-! ## The supremum over the channel count -/

/-- **The wideband ceiling is the supremum of the equal-noise rates.**  For `c > 0`
and `P ≥ 0`,

    `⨆ n : ℕ, (n/2)·log(1 + P/(n·c)) = P/(2c)`.

This is the explicit least-upper-bound form of the wideband limit: `P/(2c)` is not
merely the `n → ∞` limit of the equal-noise rates but their exact supremum over all
channel counts.  `≤` is the per-`n` ceiling `rate_equalNoise_seq_le_wideband`
(bounding the whole family by `P/(2c)`); `≥` is the wideband limit
`rate_equalNoise_tendsto_wideband` (`P/(2c) = lim` and every term is `≤ ⨆`, so the
limit cannot exceed the supremum).  No monotonicity or differentiability in `n` is
needed. -/
theorem rate_equalNoise_iSup_eq_wideband {c : ℝ} (hc : 0 < c) {P : ℝ} (hP : 0 ≤ P) :
    ⨆ n : ℕ, (n : ℝ) / 2 * Real.log (1 + P / (n * c)) = P / (2 * c) := by
  set R : ℕ → ℝ := fun n => (n : ℝ) / 2 * Real.log (1 + P / (n * c)) with hR
  have hceil : ∀ n, R n ≤ P / (2 * c) := fun n =>
    rate_equalNoise_seq_le_wideband hc hP n
  have hbdd : BddAbove (Set.range R) :=
    ⟨P / (2 * c), by rintro _ ⟨n, rfl⟩; exact hceil n⟩
  have htend : Filter.Tendsto R Filter.atTop (nhds (P / (2 * c))) :=
    rate_equalNoise_tendsto_wideband hc P
  refine le_antisymm (ciSup_le hceil) ?_
  exact le_of_tendsto htend (Filter.Eventually.of_forall (fun n => le_ciSup hbdd n))

end ShannonWaterFilling
