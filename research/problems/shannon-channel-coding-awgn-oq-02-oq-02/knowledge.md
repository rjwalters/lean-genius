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

## Session 2026-07-08 (FRESH continuation) - Affine invariance of ρ

**Mode**: FRESH (continued rich-knowledge problem, depth-over-breadth)
**Outcome**: progress (2 theorems + 1 helper, VERIFIED 0 sorry / 0 axiom)

### What I Did
- Added `correlation_affine_invariant`: ρ[a·X+b, c·Y+d] = sign(a·c)·ρ[X,Y] for arbitrary a,b,c,d.
- Added `correlation_affine_invariant_of_pos`: a,c>0 ⟹ ρ preserved exactly (scale-free property).
- Added private helper `real_sign_eq_self_div_abs`: Real.sign x = x/|x| ∀x (incl 0 via 0/0=0).

### Key Findings
- The identity is UNCONDITIONAL — no non-degeneracy needed. Degenerate cases (Var=0) collapse to
  0 = sign(ac)·0 automatically through the Lean division-by-zero convention.
- Reuses the ±1-capstone machinery: cov[aX+b,cY+d]=ac·cov via covariance_add_const_left/right +
  covariance_const_mul_left/right; σ[aX+b]=|a|·σ[X] via variance_eq_of_affine.
- Packaging sign as x/|x| lets the final normalisation a·c/(|a|·|c|)=sign(ac) close by `ring`
  (field inverse rearrangement) with zero nonzero-hypotheses — clean.

### Files Modified
- proofs/Proofs/ShannonChannelCodingAWGNOQ02OQ02.lean (842→908 lines, 36→38 theorems)
- src/data/proofs/shannon-channel-coding-awgn-oq-02-oq-02/meta.json (counts + contribution)
- src/data/research/problems/shannon-channel-coding-awgn-oq-02-oq-02.json (knowledge)

### Next Steps
- Orientation-reversing corollary (a>0, c<0 ⟹ ρ ↦ −ρ) if a further result needs it.
- Extract cov[aX+b,cY+d]=ac·cov as a named reusable covariance-bilinearity lemma if reused.

## Session 2026-07-08 (researcher-3) — MRC diversity gain (monotone max-SNR + sharp strict)

**Mode**: ACT (look-outward on a near-terminus SOLVED entry). **Outcome**: progress, 0-axiom.
Extended the maximal-ratio-combining (MRC) thread. The MRC theorem already present
(`mrc_snr_le` + `mrc_snr_matched`) identifies the maximum attainable output SNR of a linear
combiner over a branch block `s` as the summed per-branch SNRs `∑_{i∈s} sigᵢ²/vᵢ`. Added the
*diversity-gain* behaviour of that maximum as the branch set grows:
- `mrc_max_snr_mono (hst : s ⊆ t) (hv : ∀ i∈t, 0<v i)`: `∑_{s} sigᵢ²/vᵢ ≤ ∑_{t} sigᵢ²/vᵢ`.
  One line: `Finset.sum_le_sum_of_subset_of_nonneg` with each summand `≥0` via
  `div_nonneg (sq_nonneg _) (hv i _).le`. Combining over more branches never lowers attainable SNR.
- `mrc_max_snr_lt_of_signal (hst : s ⊆ t) (hj : j∈t) (hjs : j∉s) (hsig : sig j ≠ 0)`: strict
  `<`. `Finset.sum_lt_sum_of_subset` with the new term `sig j²/v j > 0`
  (`lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsig))` then `div_pos`) and the other
  new summands `≥0`. Sharp companion: a branch improves diversity *exactly* when it carries
  signal — a noise-only branch (`sig=0`) adds nothing.

File 1447→1479 lines, 58→60 theorems (def 1 unchanged). Docker build EXIT 0 (two 135-SIGBUS
retries at olean-write under fleet mem pressure; clean elab [7743/7743] each time — third try
green), 0 sorry / 0 axiom. Gallery meta.json synced (stale 1355/54 and top-level 1247/50 both
reconciled to 1479/60 across .meta/.leanFile/top-level blocks).

### Next steps
- MRC equality/uniqueness: `mrc_snr_le` is tight iff weights `aᵢ ∝ sigᵢ/vᵢ` (Cauchy–Schwarz
  equality case) — genuinely new but needs the CS equality condition, likely nontrivial.
- Higher-moment / fourth-moment budgets, or an explicit uncorrelated-but-dependent witness
  (pairwise-independence gap is strict) — the remaining substantive, non-cosmetic directions.
