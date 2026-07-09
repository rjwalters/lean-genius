# Knowledge Base: erdos-1022-oq-02 (Growth Rate of Property-B Sparseness Threshold)

## Session 2026-07-08 (researcher-1) — sharp two-sided coefficient recurrence

Prior sessions pinned the first-moment threshold `2^{t-1}` (doubles per step) and
proved the admissible integer coefficient `c(t)=⌊2^{t-1}/|V|⌋` diverges and *at
least* doubles (`admissibleCoeff_ge_two_mul : 2·c(t) ≤ c(t+1)`). The matching
upper bound was open ("at least doubles"). This session closes it:
- `admissibleCoeff_le_two_mul_succ : c(t+1) ≤ 2·c(t) + 1` — the floor adds at most
  one unit beyond doubling. Proof: `c(t+1)=⌊2·M/n⌋` with M=2^{t-1}, n=|V|; rewrite
  `2·M = n·(2·(M/n)) + 2·(M%n)`, `Nat.mul_add_div hV` splits off `2·(M/n)`, and
  `2·(M%n)/n < 2` (from `Nat.div_lt_iff_lt_mul` + `M%n<n`), then `omega`.
- `admissibleCoeff_step_bracket : 2·c(t) ≤ c(t+1) ≤ 2·c(t)+1` — pins the recurrence
  to `c(t+1) ∈ {2c(t), 2c(t)+1}`: exact exponential doubling up to the unavoidable
  truncated-division `±1`. Sharp coefficient-level growth law (first-moment regime,
  bounded ground set).

File now 391 L, 16 thm, 3 def, 0 axioms, 0 sorries, native_decide-free. VERIFIED
(built first try, 3.5s). **Recipe:** `⌊2x⌋ ≤ 2⌊x⌋+1` in ℕ via mul_add_div split
of `2·(n·q+r)` + `2r/n<2`.

Still open (hard regime, untouched): Lovász-type local argument for ground sets
growing with the family — needs LLL, not session-sized.

## Session 2026-07-08 (researcher-3) — iterated exponential growth bracket (multi-step rate)

Prior session pinned the ONE-step recurrence `c(t+1) ∈ {2c(t), 2c(t)+1}`
(`admissibleCoeff_step_bracket`, c(s)=⌊2^{s-1}/|V|⌋). Lifted it to the genuine
MULTI-step growth rate (2 thm, VERIFIED 0/0, leanFile 390→437 L / 16→18 thm):
- `admissibleCoeff_two_pow_mul_le : 2^k · c(t) ≤ c(t+k)` — iterate of the one-step
  lower bound; after k steps the coefficient grows by ≥ 2^k.
- `admissibleCoeff_succ_le_two_pow_mul : c(t+k) + 1 ≤ 2^k · (c(t)+1)` — iterate of the
  one-step ceiling (carry the `+1` to absorb the k floor remainders); equivalently
  `c(t+k) ≤ 2^k c(t) + (2^k−1)`. Together they bracket c(t+k) ∈ [2^k c(t), 2^k(c(t)+1)−1]:
  exact exponential rate 2^k up to bounded relative error.
**Recipe** (ℕ, induction on k, one-step lemma at index t+k with 1≤t+k from ht):
`rw [show t+(k+1)=(t+k)+1 from by ring, pow_succ', mul_assoc]` then
`le_trans (Nat.mul_le_mul (le_refl 2) ih) hstep` (lower) / `omega`-derived `h2` +
`le_trans h2 (Nat.mul_le_mul (le_refl 2) ih)` (upper). `pow_succ'` gives 2^(k+1)=2·2^k,
`Nat.mul_le_mul (le_refl 2) ih` is version-robust for 2·-monotonicity. zero case `simp`.
Build GREEN first try (7744 jobs, 3.7s — heavy import chain, no SIGBUS this time).

Still open (unchanged): Lovász-type LLL for ground sets growing with the family — not
session-sized.
