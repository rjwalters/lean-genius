/-
Harmonic `*StatementOnly.lean` Aristotle-submission file
(format from Loom #22468; docs at research/SORRY-CLASSIFICATION.md).

Follow-up for research problem `lebesgue-measure-oq-05` (σ-finite Radon–Nikodym
package, formalized in `proofs/Proofs/LebesgueMeasureOQ05.lean`, merged #24720).
The seven theorems of that file are complete (0 sorries, 0 axioms); this file
adds the natural next result — the **Radon–Nikodym chain rule** — now discharged
(0 sorries) by Mathlib's `Measure.rnDeriv_mul_rnDeriv`. Build-pending (Docker /
Aristotle blackout); the proof term is a verbatim match against the Mathlib pin.

Statement: For σ-finite measures `μ, ν, λ` on a measurable space with `μ ≪ ν`,
the Radon–Nikodym derivatives compose multiplicatively, `λ`-almost everywhere:

    (dμ/dν) · (dν/dλ) = dμ/dλ        [=ᵐ[λ]]

This is the measure-theoretic chain rule and the basis for change-of-variables
between densities (and, via λ = a base measure, for the transitivity of
probability-density transformations).

Citations:
- Radon, J. (1913). "Theorie und Anwendungen der absolut additiven
  Mengenfunktionen." Sitzungsber. Akad. Wiss. Wien 122, 1295–1438.
- Nikodym, O. (1930). "Sur une généralisation des intégrales de M. J. Radon."
  Fund. Math. 15, 131–179.
- Bogachev, V.I. (2007). Measure Theory, Vol. I, §3.2 (Radon–Nikodym).

Past Aristotle history for this problem: the base file was submitted only via
the deployer build-gate; no per-theorem Aristotle submission exists yet. This
file establishes the chain-rule baseline.

Proof: Mathlib's `MeasureTheory.Measure.rnDeriv_mul_rnDeriv` states exactly this
for a σ-finite triple under `μ ≪ ν` — signature
`(hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ` at the v4.26.0 pin
(Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:383), which is the
goal verbatim with `κ := lam`. The term is therefore `Measure.rnDeriv_mul_rnDeriv h`.

Answer: `μ.rnDeriv ν * ν.rnDeriv lam =ᵐ[lam] μ.rnDeriv lam`.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option pp.fullNames true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.all false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LebesgueMeasureOQ05ChainRuleStatement

variable {α : Type*} [MeasurableSpace α] {μ ν lam : Measure α}

/--
**Radon–Nikodym chain rule (σ-finite).** For σ-finite measures `μ, ν, λ` with
`μ ≪ ν`, the Radon–Nikodym derivative of `μ` w.r.t. `λ` factors through the
intermediate measure `ν`:
`(dμ/dν)·(dν/dλ) = dμ/dλ`, `λ`-almost everywhere.

This is the measure-theoretic analogue of the calculus chain rule. Combined
with the seven theorems of `LebesgueMeasureOQ05.lean` it completes the
elementary calculus of densities for the σ-finite gallery package.

The expected Mathlib glue is `MeasureTheory.Measure.rnDeriv_mul_rnDeriv`, which
states precisely this equality for a σ-finite triple under `μ ≪ ν`.
-/
theorem rnDeriv_chain [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite lam]
    (h : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv lam =ᵐ[lam] μ.rnDeriv lam :=
  Measure.rnDeriv_mul_rnDeriv h

end LebesgueMeasureOQ05ChainRuleStatement
