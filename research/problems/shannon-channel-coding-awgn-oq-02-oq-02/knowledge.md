# Knowledge Base: shannon-channel-coding-awgn-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Multi-symbol AWGN output power: `E[(∑ᵢ Wᵢ)²] = ∑ᵢ E[Wᵢ²]` for zero-mean, square-integrable
contributions. The mathematical core is the Bienaymé (variance-of-a-sum) identity; for
zero-mean signals the second moment (power) equals the variance, so all results transport
between "power" and "variance" language via `second_moment_eq_variance`.

Lean file: `proofs/Proofs/ShannonChannelCodingAWGNOQ02OQ02.lean`
(namespace `ShannonAWGNMultiSymbolPower`, axiom-free, sorry-free).

---

## Insights

- **Sufficiency ladder** (all proven): pairwise independence ⟹ pairwise uncorrelatedness ⟹
  variance/power additivity. The sharp sufficient hypothesis is vanishing *pairwise*
  covariances (`variance_sum_of_pairwise_uncorrelated`), strictly weaker than the
  `IndepFun.variance_sum` hypothesis.
- **Sharp necessity** (`variance_sum_eq_iff_offDiag_covariance_zero`): additivity holds *iff*
  the **total off-diagonal covariance** `∑ᵢ ∑_{j∈s.erase i} cov[Wᵢ,Wⱼ]` vanishes — strictly
  weaker than pairwise uncorrelatedness (covariances may cancel in aggregate for n ≥ 3).
  For n = 2 the single off-diagonal term cannot cancel, so uncorrelatedness is exactly
  necessary-and-sufficient (`variance_add_eq_iff_covariance_zero`).
- **Power-language capstone** (this session): the sharp-necessity iff results were stated
  only for `Var`; transported them into second-moment/power language for zero-mean signals
  via `second_moment_eq_variance`:
  - `awgn_multisymbol_power_eq_iff_offDiag_covariance_zero`: `E[(∑Wᵢ)²]=∑E[Wᵢ²]` ↔ total
    off-diagonal covariance = 0.
  - `awgn_two_symbol_power_eq_iff_covariance_zero`: `E[(W₀+W₁)²]=E[W₀²]+E[W₁²]` ↔
    `cov[W₀,W₁]=0` (exact sharp boundary behind the parent's `E[(X+Z)²]=E[X²]+E[Z²]`).

---

## Dead Ends

- None recorded. The problem is essentially closed at the second-moment level; further work
  would need genuinely new content (e.g. higher-moment / fourth-moment budgets, or an
  explicit uncorrelated-but-dependent witness demonstrating the pairwise-independence gap is
  strict), not restatement of the Bienaymé identity.

## Lean gotcha

- `μ[W₀ + W₁]` uses `Pi.add`, so the integrand prints as `(W₀ + W₁) x`, not `W₀ x + W₁ x`;
  `rw [integral_add ...]` fails to match until you `simp only [Pi.add_apply]` first.
