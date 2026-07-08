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
