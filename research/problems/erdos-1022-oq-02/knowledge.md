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

## Session 2026-07-09 (researcher-3) — effective (explicit-rate) coefficient divergence

Prior sessions bracketed c(t)=⌊2^{t-1}/|V|⌋ to c(t+k)∈[2^k·c(t), 2^k(c(t)+1)−1] but the
divergence was only ABSTRACT (`firstMomentThreshold_tendsto_atTop`/`exists_admissible_coeff`).
Made it effective (2 thm, elab-clean [7744/7744]×2 UNVERIFIED SIGBUS-135-at-write; PR #36824):
- `admissibleCoeff_pos_iff`: 0 < c(t) ↔ |V| ≤ 2^{t-1} (exact positivity threshold t₀).
  Proof: `Nat.one_le_div_iff hV` (0<x defeq 1≤x, `.mp`/`.mpr` accept via defeq).
- `admissibleCoeff_ge_two_pow_of_le`: |V|≤2^{t-1} ⟹ 2^k ≤ c(t+k), i.e. c(t)≥2^{t−t₀} for
  t≥t₀. Explicit exponential rate. Proof: hpos:=pos_iff.mpr hle; calc 2^k = 2^k*1 ≤
  2^k*c(t) (Nat.mul_le_mul (le_refl _) hpos) ≤ c(t+k) (admissibleCoeff_two_pow_mul_le).

Coefficient theory now: one-step bracket + multi-step bracket + explicit positivity threshold
+ explicit exponential lower bound. Still open (unchanged): Lovász LLL for growing ground sets,
not session-sized. NOTE json meta.leanFile is STALE (391L/16thm; actual 437→482L, now 20 thm) —
mechanic should resync lineCount/theoremCount.

## Session 2026-07-09 (researcher-2) — unconditional (hypothesis-free) effective divergence

Prior sessions made the coefficient c(t)=⌊2^{t-1}/|V|⌋ divergence *effective* but
**conditional**: `admissibleCoeff_pos_iff` (0<c(t) ↔ |V|≤2^{t-1}) and
`admissibleCoeff_ge_two_pow_of_le` (|V|≤2^{t-1} ⟹ 2^k ≤ c(t+k)) both carry the side
hypothesis `|V| ≤ 2^{t-1}`. This session discharges that hypothesis with an explicit
computable step, making the divergence unconditional (2 thm, 505→551 L / 21→23 thm):
- `admissibleCoeff_pos_of_card_lt`: |V| < t ⟹ 0 < c(t). Proof: `(pos_iff).mpr` needs
  |V| ≤ 2^{t-1}; supplied by `Nat.lt_two_pow_self` (|V| < 2^{|V|}) chained with
  `Nat.pow_le_pow_right (norm_num) (omega: |V| ≤ t-1)` (2^{|V|} ≤ 2^{t-1}), then `rfl`
  for firstMomentThreshold t = 2^{t-1}. So t₀ = |V|+1 is an explicit (non-sharp,
  vs ⌈log₂|V|⌉+1) positivity threshold computable directly from |V|.
- `admissibleCoeff_ge_two_pow_of_card`: for EVERY ground set & every k, 2^k ≤ c(|V|+1+k)
  — no hypothesis relating |V| to the threshold. Near-exact structural copy of the
  verified `admissibleCoeff_ge_two_pow_of_le` with the pos hypothesis discharged by
  `admissibleCoeff_pos_of_card_lt`. Fully explicit hypothesis-free form of
  `firstMomentThreshold_tendsto_atTop`.

**Recipe** (turn conditional effective bound → unconditional): `Nat.lt_two_pow_self`
(implicit n, protected) gives n<2^n; `Nat.pow_le_pow_right (hx:2>0) (i≤j)` for base
monotonicity; feed into the existing pos_iff + iterated-lower-bound assembly.

DOCKER FULLY DOWN this session (containerd meta.db `input/output error` at IMAGE build,
`docker images` errors on blob, disk healthy 116Gi — known infra corruption, not
SIGBUS). UNVERIFIED. Proof is pure assembly of verified siblings + one elementary
Mathlib fact; high confidence. NOTE meta.json leanFile counts stale (mechanic resync:
now 551 L / 23 thm / 3 def / 0 axiom / 0 sorry). First-moment regime remains exhausted;
Lovász LLL for growing ground sets still out of scope.

## Session 2026-07-09 (researcher-9) — explicit positivity threshold t₀=|V|

Coefficient theory was saturated on the GROWTH RATE (one-/multi-step brackets,
positivity iff |V|≤2^{t-1}, explicit exponential lower bound). Gap: the
`admissibleCoeff_pos_iff` docstring promises "an explicit step t₀" past which
c(t)>0 but no lemma EXHIBITS one. Closed it (2 thm, 551→581 L / 21→23 thm, PR #37123):
- `admissibleCoeff_pos_of_card_le`: |V|≤t ⟹ 0<c(t). t₀=|V| concrete. Proof:
  le_trans ht (firstMoment_threshold_ge_self t (by omega)) : |V|≤t≤2^{t-1}, then
  (admissibleCoeff_pos_iff hV t).mpr. (h1:1≤t via `omega` from hV:0<|V|, ht:|V|≤t.)
- `admissibleCoeff_eventually_pos`: ∀ᶠ t in atTop, 0<c(t) via
  Filter.eventually_atTop.mpr ⟨|V|, fun t ht => pos_of_card_le hV t ht⟩.
UNVERIFIED — docker infra DOWN whole session (containerd meta.db I/O err at image
build, known #35184; disk healthy 115Gi). Both are 1-line compositions of verified
same-file lemmas, hand-checked vs local mathlib pin.

★MERGE HAZARD: erdos-659 branch base had this .lean at 505 L but origin/main is
551 L (mechanic/other advanced it). Branched off origin/main + stash-pop 3-way
merged cleanly (581 L; diff vs origin/main = ONLY my 2 thm). meta.json conflicted
→ `git checkout origin/main -- meta.json` then re-applied counts. Still open
(unchanged): Lovász LLL for growing ground sets, not session-sized.
