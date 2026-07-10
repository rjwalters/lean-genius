/-
Erdős Problem #1014 OQ-03: the *concrete* off-diagonal Ramsey increment for k = 3.

The companion files `Erdos1014OQ03.lean` and `Erdos1014OQ03LogIncrement.lean` prove
the **increment–ratio bridge** for an *abstract* positive sequence `R`:

  (R(l+1) − R(l))/R(l) → 0   ⟺   R(l+1)/R(l) → 1   ⟺   log R(l+1) − log R(l) → 0.

They deliberately abstract over arbitrary sequences and never touch the actual
Ramsey number, so the honest increment consequence `Δ_l(k) = o(R(k,l))` is only
stated *schematically*. This file supplies the missing instantiation for the one
case where Erdős #1014 is an unconditional theorem, `k = 3`.

The parent file `Erdos1014Problem.lean` proves `R3_ratio_convergence`,
`R(3,l+1)/R(3,l) → 1`, **not** from the open conjecture `erdos_1014_conjecture` but
from the established Shearer/Kim lower bound `R(3,l) ≥ c·l²/log l` together with the
recurrence increment bound `R(3,l+1) − R(3,l) ≤ l + 1`. Feeding that unconditional
ratio-convergence through the abstract bridge yields the concrete, honest increment
statements collected here:

  * `ramsey3_increment_div_tendsto_zero` : `Δ_l(3)/R(3,l) → 0`, i.e.
    `Δ_l(3) = R(3,l+1) − R(3,l) = o(R(3,l))`;
  * `ramsey3_log_increment_tendsto_zero` : `log R(3,l+1) − log R(3,l) → 0`
    (asymptotic *log-flatness* of the k = 3 Ramsey number).

Neither statement asserts the full asymptotic formula `Δ_l(3) ~ g(l)` (conjecturally
`~ c·l/log l`), which remains OPEN: the increment's `~`-class is not determined by
that of `R(3,·)` alone (see the cautionary note in `Erdos1014OQ03.lean`).

Verified, 0 axioms, 0 sorries, no `native_decide`. (Transitively depends on the
standard-result axioms of `Erdos1014Problem.lean`, e.g. `R3_lower`, but on **none**
of the open-conjecture axiom `erdos_1014_conjecture`.)

References:
- Erdős [Er71], Problem 1014
- Shearer (1983), Kim (1995): `R(3,l) ≥ c·l²/log l`
- Ajtai–Komlós–Szemerédi (1980): `R(3,l) ≤ C·l²/log l`
-/

import Mathlib
import Proofs.Erdos1014Problem
import Proofs.Erdos1014OQ03

namespace Erdos1014OQ03Concrete

open Filter Topology Erdos1014OQ03

/-- **The k = 3 consecutive ratio converges (as a filter limit).** Repackages the
parent's ε–δ theorem `R3_ratio_convergence` (`R(3,l+1)/R(3,l) → 1`, proved
unconditionally from the Shearer/Kim and AKS bounds) as a `Tendsto` statement,
ready to feed into the abstract increment–ratio bridge. -/
theorem ramsey3_ratio_tendsto_one :
    Tendsto (fun l => (ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := R3_ratio_convergence ε hε
  refine ⟨L₀ + 1, fun l hl => ?_⟩
  rw [Real.dist_eq]
  exact hL₀ l (by omega)

/-- **`R(3, l)` is eventually positive.** For `l ≥ 1`, `R(3, l) ≥ 1 > 0`
(from `ramsey_pos`), so the real cast is eventually positive along `atTop`. -/
theorem ramsey3_pos_eventually :
    ∀ᶠ l in atTop, (0 : ℝ) < (ramseyNumber 3 l : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with l hl
  have := ramsey_pos 3 l (by omega) hl
  exact_mod_cast (show 0 < ramseyNumber 3 l by omega)

/-- **The k = 3 Ramsey increment is `o(R(3,l))` — concrete and unconditional.**

The normalized increment `Δ_l(3)/R(3,l) = (R(3,l+1) − R(3,l))/R(3,l)` tends to `0`.
This is the abstract bridge `increment_div_tendsto_zero_of_ratio_tendsto_one`
instantiated on `R(3, ·)` and fed the unconditional `ramsey3_ratio_tendsto_one`;
it is the honest, concrete form of `Δ_l(3) = o(R(3,l))` for the one case (`k = 3`)
where Erdős #1014's ratio convergence is a theorem rather than a conjecture. -/
theorem ramsey3_increment_div_tendsto_zero :
    Tendsto
      (fun l => ((ramseyNumber 3 (l + 1) : ℝ) - (ramseyNumber 3 l : ℝ))
        / (ramseyNumber 3 l : ℝ))
      atTop (𝓝 0) :=
  increment_div_tendsto_zero_of_ratio_tendsto_one
    (fun l => (ramseyNumber 3 l : ℝ))
    (ramsey3_pos_eventually.mono fun _ hl => hl.ne')
    ramsey3_ratio_tendsto_one

/-- **The k = 3 Ramsey increment is asymptotically log-flat — concrete and
unconditional.**

The additive log-increment `log R(3,l+1) − log R(3,l)` tends to `0`. This is the
logarithmic bridge `log_increment_tendsto_zero_of_ratio_tendsto_one` instantiated on
`R(3, ·)` and fed `ramsey3_ratio_tendsto_one`; it makes precise the "eventual
smoothness" of the increment raised in OQ-03's open questions, again for the
unconditional `k = 3` case. -/
theorem ramsey3_log_increment_tendsto_zero :
    Tendsto
      (fun l => Real.log (ramseyNumber 3 (l + 1) : ℝ) - Real.log (ramseyNumber 3 l : ℝ))
      atTop (𝓝 0) :=
  log_increment_tendsto_zero_of_ratio_tendsto_one
    (fun l => (ramseyNumber 3 l : ℝ))
    ramsey3_pos_eventually
    ramsey3_ratio_tendsto_one

end Erdos1014OQ03Concrete
