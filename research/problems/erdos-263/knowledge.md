# Knowledge Base: Erdős #263 - Irrationality Sequences

## Session 2026-05-01 (Session 11) — Confirmed BLOCKED; updated pool/DB

**Mode**: REVISIT (RICH, score 48)
**Outcome**: BLOCKED — 4 sorries are all deep, all confirmed not-in-Mathlib

### What I Verified

- Re-checked the 4 remaining sorries in `proofs/Proofs/Erdos263Problem.lean`:
  - line 84: `folklore_irrationality` — Mahler-type criterion
  - line 144: `kovac_tao_not_irrationality` — Kovač-Tao 2024 Egyptian fraction
  - line 178: `positive_condition_irrationality` — liminf analysis
  - line 503: `truncation_insufficient` — needs irrationality-sequence witness
- Searched Mathlib v4.26.0 (live snapshot at `.loom/worktrees/stokes-dd/proofs/.lake/packages/mathlib/`):
  - `Mathlib/NumberTheory/Transcendental/Liouville/` exists but covers only the classical Liouville construction `∑ 1/m^{i!}` (factorial denominators) and proves transcendence (and hence irrationality) of those specific Liouville constants.
  - No general Mahler-type irrationality criterion found.
  - No Kovač-Tao theorem or related Egyptian-fraction construction.
- The Liouville construction in Mathlib does NOT imply `folklore_irrationality`: Liouville requires factorial-rate denominators, while folklore growth `aₙ^{1/2^n} → ∞` is much weaker. The two conditions are incomparable on most sequences (and `doubleExp` has neither — already proved).

### Pool / DB Reconciliation

- DB row `erdos-263` was `in-progress`. Pool entry was `in-progress`.
- The problem JSON (`src/data/research/problems/erdos-263.json`) already had `status: blocked`
  and a clear progressSummary ("BLOCKED (session 11): All tractable work complete..."),
  so the gallery side was already correct. Only the operational pool/DB needed to be aligned.
- Updated:
  - `research/db/knowledge.db`: `status='blocked', phase='BLOCKED'`
  - `.lean/state/candidate-pool.json`: `status: blocked` (via `claim-problem.sh update`)
- Did NOT run `sync_pool.py` — the DB is currently regressed (~790 fewer `completed`
  entries than the pool, per session 12's note). Running sync would propagate the
  regression. The DB and pool are now both internally consistent for `erdos-263`
  even though they diverge on other entries.

### Why No Code Change

- 0 axioms, 4 deep sorries, all confirmed Mathlib-blocked across multiple prior sessions
- Per protocol "3+ sessions stuck on same sorry → flag BLOCKED, move on" — this problem
  has been BLOCKED in every session since at least session 5 (2026-04-21)
- No new Mathlib content has appeared that would unblock any of the four sorries
- Docker remains hung (other agent's BinaryGcdOQ03OQ02 build stuck for 16+ hours), so
  even small refactors would be unverified

### Sorry Count: 4 (unchanged — all genuinely BLOCKED)

---

## Session 2026-04-22 (Session 9) — Prove doubleExp_sum_irrational (5→4 sorries)

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved doubleExp_sum_irrational via integer-gap argument

### What I Did

All 4 helper lemmas (fin_mul_nat, tail_pos, tail_bound, tsum_split_at) were proved in prior
sessions. This session assembles them into the full proof of `doubleExp_sum_irrational`:

**Proof structure** (integer-gap argument):
1. Assume S = ∑ 1/2^{2^n} = q (rational), using Lean's `Irrational` intro pattern
2. Set N = q.den, D = 2^{2^N}. Show N+1 ≤ D via induction + nat_le_two_pow
3. hS_eq: S = q.num/N (via Rat.cast_def + push_cast)
4. hSplit: S = finsum + 1/D + tail (via tsum_split_at)
5. hmf: D * finsum = mf ∈ ℕ (via doubleExp_fin_mul_nat)
6. hkey: N*D*tail = q.num*D - N*mf - N (algebraic identity from hS_eq ∧ hmf)
7. hgap_pos: 0 < N*D*tail (from htail_pos, hN_pos, hD_pos)
8. hgap_lt1: N*D*tail < 1 (from htail_bound: D*T < 1/(D-1), N ≤ D-1)
9. hgap_int: ∃ z : ℤ, (z : ℝ) = N*D*tail (integer arithmetic witness)
10. Contradiction: nonzero integer z with |z| < 1 is impossible (hz_pos + hz_lt1 + linarith)

### Current State
- 4 sorries remain (ALL deep — require non-Mathlib mathematics):
  1. `folklore_irrationality`: Mahler-type criterion (not in Mathlib)
  2. `kovac_tao_not_irrationality`: Kovač-Tao 2024 Egyptian fraction construction
  3. `positive_condition_irrationality`: liminf analysis (requires folklore_irrationality)
  4. `truncation_insufficient`: needs witnessing an irrationality sequence
- 0 hard sorries remain (doubleExp_sum_irrational now proved)

### Files Modified
- `proofs/Proofs/Stubs/Erdos263Problem.lean` (726 → 792 lines, 5 → 4 sorries)
- `src/data/proofs/erdos-263/meta.json` (lineCount, sorries updated)
- `src/data/research/problems/erdos-263.json` (knowledge updated)

---

## Session 2026-04-22 (Session 8) — Prove 3 Helper Lemmas (8→5 sorries)

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved doubleExp_tail_pos, doubleExp_tail_bound, tsum_split_at

### What I Did

Proved the 3 remaining "Aristotle candidate" helper lemmas for the integer-gap argument:

1. **`tsum_split_at`** (proved): `∑' f = (range sum) + f N + (shifted tail)`
   - Used `Summable.sum_add_tsum_nat_add` to split off the finite prefix
   - Used `Summable.tsum_eq_zero_add` to peel off the single term at N
   - Index arithmetic `n+1+N = n+N+1` handled by `omega` inside `tsum_congr`

2. **`doubleExp_tail_pos`** (proved): `0 < ∑' k, 1/2^{2^{k+N+1}}`
   - Summability: `(summable_nat_add_iff (N+1)).mpr doubleExp_sum_summable` + `.congr`
   - Positivity: `tsum_pos hsum (fun k => by positivity) 0 (by positivity)`

3. **`doubleExp_tail_bound`** (proved): `D * T < 1/(D-1)` where `D = 2^{2^N}`
   - Set `r = 1/D²`. Key arithmetic: `k+1 ≤ 2^k` ⟹ `2(k+1) ≤ 2^{k+1}`
   - Term bound: `1/D^{2^{k+1}} ≤ 1/D^{2(k+1)} = r^{k+1}` via `one_div_le_one_div_of_le`
   - Geometric series: `∑ r^{k+1} = 1/(D²-1)` via `tsum_mul_left + tsum_geometric_of_lt_one`
   - Final: `D/(D²-1) < 1/(D-1)` since `D·(D-1) < D²-1` via `nlinarith`

### Current State
- 5 sorries remain: 4 deep (folklore, kovac-tao, positive-condition, truncation) + 1 hard (doubleExp_sum_irrational)
- All 4 helpers for the main theorem are proved (fin_mul_nat in session 7, the 3 above now)
- Next: attempt `doubleExp_sum_irrational` directly using the helper lemmas

### Files Modified
- `proofs/Proofs/Stubs/Erdos263Problem.lean` (650 → 726 lines, 8 → 5 sorries)
- `src/data/proofs/erdos-263/meta.json`

---

## Problem Summary

**Erdős #263**: A sequence (aₙ) of positive integers is an *irrationality sequence* if for every
sequence (bₙ) with bₙ/aₙ → 1, the sum Σ 1/bₙ is irrational.

**Questions**:
1. Is aₙ = 2^{2^n} an irrationality sequence?
2. Must every irrationality sequence satisfy aₙ^{1/n} → ∞?

**Status**: OPEN. Kovač-Tao (2024) established that sequences with aₙ₊₁/aₙ² → 0 are NOT
irrationality sequences. Both original questions remain open.

---

## Session 2026-04-21 (Session 7) — Integer-Gap Proof Formalized as Helper Lemmas

**Mode**: REVISIT (RICH knowledge tier, score 30)
**Outcome**: progress — formalized integer-gap proof structure as 6 helper lemmas; proved 2 without sorry

### What I Did

Decomposed the HARD sorry `doubleExp_sum_irrational` into 6 focused helper lemmas:

1. **`doubleExp_term_eq`** (proved, no sorry): `1/(doubleExp n : ℕ) = 1/2^{2^n}` via `simp [doubleExp]; push_cast; ring`

2. **`doubleExp_sum_summable`** (proved, no sorry): Summability of `1/2^{2^n}` derived from `doubleExp_convergent` via `Summable.congr`

3. **`doubleExp_tail_pos`** (sorry, Aristotle candidate): `0 < ∑' k, 1/2^{2^(k+N+1)}` — positivity of tail starting at index N+1

4. **`doubleExp_fin_mul_nat`** (proof attempt): `∃ m : ℕ, 2^{2^N} * Σ_{k<N} 1/2^{2^k} = m` — uses `pow_sub₀` to show each term `2^{2^N}/2^{2^k} = 2^{2^N-2^k}` is a natural number

5. **`doubleExp_tail_bound`** (sorry, key technical lemma): `2^{2^N} * tail < 1/(2^{2^N} - 1)` — geometric bound via term-wise comparison `1/D^{2^{k+1}-1} ≤ 1/D^k`

6. **`tsum_split_at`** (sorry): `∑' n, f n = finsum + f N + ∑' n, f (n+N+1)` — standard sum splitting using `Summable.sum_add_tsum_nat_add`

**Main theorem `doubleExp_sum_irrational`** still has a sorry but now has the complete proof strategy documented:
- Assume S = p/q. Set N = |q|+1, D = 2^{2^N} > |q|
- Split: S = finsum + 1/D + T
- Key identity: q·D·T = p·D - q·m - q ∈ ℤ (since D·finsum = m ∈ ℕ)
- Bound: |q|·D·T < |q|/(D-1) ≤ 1 (from tail_bound + |q| ≤ D-1)
- Contradiction: nonzero integer with |.| < 1

### Key Findings

- `pow_sub₀` is the right Mathlib lemma for `a^(m-n) = a^m * (a^n)⁻¹` (used in fin_mul_nat)
- The tail bound proof: `D*T = Σ 1/D^{2^{k+1}-1}`, bounded by `Σ (1/D)^k = D/(D-1)`, so `D*T < 1/(D-1)`
- Key inequality chain: `|q| < N ≤ 2^N ≤ 2^{2^N} = D`, so `|q| ≤ D-1`
- These two give `|q|·D·T < |q|/(D-1) ≤ (D-1)/(D-1) = 1`

### Files Modified
- `proofs/Proofs/Stubs/Erdos263Problem.lean` (606 → 654 lines, 5 → 7 sorries)
- `src/data/proofs/erdos-263/meta.json` (lineCount, sorries updated)
- `src/data/research/problems/erdos-263.json` (knowledge updated)

### Next Steps (Aristotle candidates)
1. **`doubleExp_tail_pos`**: Submit to Aristotle — positivity via `tsum_pos` + `Summable.comp_injective`
2. **`doubleExp_fin_mul_nat`**: Verify/fix `pow_sub₀` usage, then submit to Aristotle
3. **`doubleExp_tail_bound`**: Submit to Aristotle — geometric series comparison
4. **`tsum_split_at`**: Submit to Aristotle — standard `sum_add_tsum_nat_add` + `Finset.sum_range_succ`
5. Once helpers compile: main theorem body should follow via algebraic manipulation

---

## Session 2026-04-21 (Session 6) — New Theorems: connection_262 + doubleExp_sum_irrational

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved `connection_262_proved` (no sorry); added `doubleExp_sum_irrational` (HARD sorry with complete integer-gap proof sketch, Aristotle candidate)

### What I Did

Added two new theorems in Part XI:

**`connection_262_proved`**: Proves `connection_262 : ∀ a, IsIrrationalitySequence a → Irrational (Σ 1/aₙ)`.
- Proof: take the identity perturbation `b n = (a n : ℕ) : ℤ`. Since `b n / a n = 1 → 1`, the irrationality sequence property directly gives the result.
- This closes a gap: `connection_262` was defined as a Prop but never proved.
- The theorem confirms the relationship: `IsIrrationalitySequence a → Irrational (Σ 1/a_n)` (but NOT the converse — see `connection_264`).

**`doubleExp_sum_irrational`**: States `Irrational (Σ 1/2^{2^n})` with HARD sorry.
- This is NECESSARY for ErdosQuestion1: if the sum were rational, the identity perturbation would immediately prevent doubleExp from being an irrationality sequence.
- Note: `folklore_irrationality` does NOT apply since `doubleExp_not_folklore_growth` shows doubleExp lacks folklore growth.
- Complete proof outline (integer-gap argument):
  - Assume S = m/n. Let D_N = 2^{2^N}.
  - D_N · S = A_N + 1 + ε_N where A_N ∈ ℕ, ε_N ∈ (0, 2/D_N)
  - For 2^{2^N} > 2n: n · ε_N < 1, giving n · D_N · S = n·A_N + n + (non-integer). Contradiction with m·D_N ∈ ℤ.
- Submitted to Aristotle as HARD sorry (tsum formalization needed)

### Mathematical Insight

The irrationality of Σ 1/2^{2^n} is related to the fact that 2^{2^n} is a "Sylvester-type" sequence (aₙ₊₁ = aₙ²). The integer-gap proof works because the product of all terms up to N exactly cancels out, leaving a fractional remainder in (0,1).

### Files Modified
- `proofs/Proofs/Stubs/Erdos263Problem.lean` (468 → 515 lines, sorries 4 → 5, theorems 16 → 18)
- `src/data/proofs/erdos-263/meta.json` (lineCount, theoremCount, sorries updated)
- `src/data/research/problems/erdos-263.json` (knowledge updated)

### Next Steps
- `doubleExp_sum_irrational` is an Aristotle candidate (HARD sorry with complete proof sketch)
- All other 4 sorries remain DEEP (require non-Mathlib mathematics)
- This problem is blocked on the deep sorries; future progress requires Mathlib analytic number theory contributions

---

## Session 2026-04-21 (Session 5) — Dependency Analysis

**Mode**: REVISIT
**Outcome**: dependency analysis — confirmed all 4 sorries are OPEN with mutual dependency chain

### Mathematical Dependency Chain

All 4 remaining sorries depend on Mahler-type criterion:

1. `folklore_irrationality` (line 83): Requires proving Σ 1/aₙ is irrational given aₙ^{1/2^n} → ∞.
   This is equivalent to a Mahler-Liouville-type irrationality criterion — not in Mathlib.

2. `positive_condition_irrationality` (line 175): If liminf a_{n+1}/aₙ^{2+ε} > 0, then a is an
   irrationality sequence. This should REDUCE to `folklore_irrationality` as follows:
   - If a has positive condition, any perturbation b (bₙ/aₙ → 1) satisfies bₙ^{1/2^n} → ∞ too
   - So Σ 1/bₙ is irrational by folklore_irrationality  
   - BLOCKED until folklore_irrationality is proved

3. `truncation_insufficient` (line 409): Needs a concrete irrationality sequence witness (otherwise
   existential fails). Would follow once either folklore_irrationality or positive_condition is proved,
   using the double exponential or a modification thereof.

4. `kovac_tao_not_irrationality` (line 141): Independent of 1-3; requires Kovač-Tao 2024 Egyptian
   fraction construction (showing explicit perturbation sequence with rational sum).

**Conclusion**: Sorries 2 and 3 are consequential (follow from sorry 1). Sorry 4 is independent but
also deep. The fundamental blocker is `folklore_irrationality` — a Mahler/Liouville-type result
requiring real analysis not available in Mathlib 4.

### Files Checked
- `proofs/Proofs/Stubs/Erdos263Problem.lean` lines 80-414

### Next Steps
- Releasing lock; this problem is blocked until Mahlib gets deeper analytic number theory tools
- Future: when Mahler criterion is available in Mathlib, positive_condition reduces to 2-line proof

---

## Session 2026-04-21 (Session 4) — Metadata Sync

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: maintenance — fixed stale meta.json (lineCount 385→468, theoremCount 11→16, assumptions updated); updated Aristotle companion notes

### What I Did

- Assessed all 4 remaining sorries: all are confirmed DEEP (require non-Mathlib mathematics)
- Updated `src/data/proofs/erdos-263/meta.json`:
  - `meta.lineCount`: 385 → 468 (sessions 2-3 added 83 lines but meta was not updated)
  - `leanFile.lineCount`: 385 → 468
  - `leanFile.theoremCount`: 11 → 16 (new: doubleExp_not_kovac_tao, factorial_has_kovac_tao_condition, doubleExp_superexponential, characterization_gap + private helper two_pow_ge_sq)
  - `meta.assumptions`: added all theorems proved in sessions 2-3 (9 theorems total)
- Updated `proofs/Proofs/Stubs/Erdos263Aristotle.lean`: noted all 5 original targets are now proved in main file; no new Aristotle targets for this problem
- Confirmed `truncation_insufficient` is unprovable without a known irrationality sequence witness (requires one of the other 3 deep sorries or a new mathematical result)

### Remaining Sorries (4, unchanged — all DEEP)

1. `folklore_irrationality`: Mahler-type irrationality criterion (deep number theory)
2. `kovac_tao_not_irrationality`: Kovač-Tao 2024 Egyptian fraction construction
3. `positive_condition_irrationality`: liminf growth condition → irrationality sequence
4. `truncation_insufficient`: cannot prove without witnessing an irrationality sequence (depends on 1 or 3)

### Files Modified

- `src/data/proofs/erdos-263/meta.json` (lineCount 385→468, theoremCount 11→16, assumptions synced)
- `proofs/Proofs/Stubs/Erdos263Aristotle.lean` (header updated to note targets are proved)
- `research/problems/erdos-263/knowledge.md` (this entry)

---

## Session 2026-04-14 (Session 3) — KT Boundary Theorems

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — proved `doubleExp_not_kovac_tao` and `factorial_has_kovac_tao_condition` (sorries unchanged at 4)

### What I Did

All 4 remaining sorries are DEEP (require non-Mathlib math). Chose to prove two new structural
theorems that clarify where key sequences sit relative to the Kovač-Tao threshold.

**`doubleExp_not_kovac_tao`**: ¬HasKovacTaoCondition doubleExp
- `doubleExp_square_growth` gives a_{n+1} = a_n² → ratio a_{n+1}/a_n² = 1 for all n
- Constant 1 cannot tend to 0 (by `tendsto_nhds_unique h1 tendsto_const_nhds`)
- Significance: doubleExp is AT the KT boundary (ratio = 1), so KT does NOT exclude it

**`factorial_has_kovac_tao_condition`**: HasKovacTaoCondition factorial_seq
- Ratio = (n+2)!/((n+1)!)² = (n+2)/(n+1)! ≤ 2/n! → 0 by squeeze
- Bound `2^n ≤ 2·n!` proved by induction (needs m≥1 case: `nlinarith [Nat.factorial_pos m]`)
- Significance: factorial is BELOW KT boundary; if KT proved, factorial is NOT irrationality seq

### KT Position Table

| Sequence | a_{n+1}/a_n² | KT status | Irrationality seq? |
|----------|-------------|-----------|-------------------|
| doubleExp (2^{2^n}) | → 1 | AT boundary | OPEN (Q1) |
| factorial ((n+1)!) | → 0 | BELOW boundary | NOT (if KT proved) |
| towerFun (^n 2) | → ∞ | ABOVE boundary | Likely yes |

### Key Lean Techniques

- `h.congr (eventually_of_forall hconst)` to transform tendsto target
- `tendsto_nhds_unique h1 tendsto_const_nhds` for contradiction from constant limit ≠ 0
- `squeeze_zero` with upper bound `2/n!` for the factorial KT condition
- `Summable.of_norm_bounded` with geometric series to prove `1/n! → 0`
- `nlinarith [Nat.factorial_pos m]` for inductive bound `2^n ≤ 2·n!`

### Files Modified

- `proofs/Proofs/Stubs/Erdos263Problem.lean` (385 → 468 lines, sorries remain 4)
- `src/data/proofs/erdos-263/meta.json` (lineCount 385→468, theoremCount 11→13)
- `src/data/research/problems/erdos-263.json` (added 2 builtItems, 3 insights)

### Remaining Sorries (4, all DEEP)

1. `folklore_irrationality`: requires Mahler-type criterion (not in Mathlib)
2. `kovac_tao_not_irrationality`: requires greedy Egyptian fraction construction (not in Mathlib)
3. `positive_condition_irrationality`: requires liminf analysis beyond current Mathlib
4. `truncation_insufficient`: structural result requiring careful construction

---

## Session 2026-04-14 (Session 2) — Prove factorial_no_folklore_growth

**Mode**: REVISIT (MODERATE knowledge tier)
**Outcome**: progress — proved `factorial_no_folklore_growth` (sorries 5→4)

### What I Did

Proved `factorial_no_folklore_growth : ¬HasFolkloreGrowth factorial_seq` via two helper lemmas:

**`succ2_le_two_pow_pow`**: n + 2 ≤ 2^(2^n) for all n.
- Base: 0 + 2 = 2 ≤ 2^1 = 2 ✓
- Step: 2^(2^(m+1)) = 2^(2^m) * 2^(2^m) ≥ 2 * (m+2) ≥ m+3 ✓

**`factorial_le_two_pow_pow`**: (n+1)! ≤ 2^(2^n) for all n.
- Base: 1! = 1 ≤ 2^1 = 2 ✓
- Step: (m+2)! = (m+2) * (m+1)! ≤ 2^(2^m) * 2^(2^m) = 2^(2^(m+1)) ✓

**Main theorem**: If `HasFolkloreGrowth factorial_seq` then eventually `((n+1)!)^{1/2^n} ≥ 3`.
But `(n+1)! ≤ 2^(2^n)` implies `((n+1)!)^{1/2^n} ≤ (2^(2^n))^{1/2^n} = 2 < 3`. Contradiction.

### Key Lean Techniques

- `Filter.tendsto_atTop.mp h 3` → eventuality argument
- `Real.rpow_le_rpow` to propagate the factorial bound through rpow
- `← rpow_natCast` + `← rpow_mul` + `push_cast` + `div_self` to compute `(2^{2^N})^{1/2^N} = 2`
- `Nat.mul_le_mul` for both helper inductions

### Remaining Sorries (4)

1. `folklore_irrationality`: aₙ^{1/2^n} → ∞ ⟹ Σ 1/aₙ irrational — requires Mahler-type criterion (DEEP, not in Mathlib)
2. `kovac_tao_not_irrationality`: The 2024 negative result — requires greedy Egyptian fraction construction (DEEP)
3. `positive_condition_irrationality`: liminf aₙ₊₁/aₙ^{2+ε} > 0 ⟹ irrationality sequence (DEEP)
4. `truncation_insufficient`: ∀N, ∃ sequences agreeing on N terms with opposite irrationality status (DEEP)

All 4 remaining sorries reflect genuinely open or deep mathematics beyond current Mathlib.

### Files Modified

- `proofs/Proofs/Stubs/Erdos263Problem.lean` (285 → ~345 lines, 5 → 4 sorries)
- `src/data/proofs/erdos-263/meta.json` (sorries 5→4, lineCount updated)
- `src/data/research/problems/erdos-263.json` (knowledge updated)

---

## Session 2026-04-14 (Session 3) — Meta.json Sync (4 sorries, 385 lines)

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: maintenance — fixed stale meta.json (sorries 5→4, lineCount 342→385)

### What I Did

- Audited the current state: Lean file has 4 sorries (lines 83, 141, 154, 336); meta.json
  still said 5 sorries with `factorial_no_folklore_growth` listed (proved in session 2 / PR #10766)
- PR #10717 (mechanic sorry-count sync, merged before #10766) re-introduced the stale count
- Fixed all three `sorries` fields and both `lineCount` fields in meta.json
- Confirmed: no new mathematical progress is possible without Mathlib contributions for the
  4 remaining deep sorries

### Remaining Sorries (4, unchanged)

All 4 require mathematics not currently in Mathlib:
1. `folklore_irrationality`: Mahler-type irrationality criterion
2. `kovac_tao_not_irrationality`: Kovač-Tao 2024 Egyptian fraction construction
3. `positive_condition_irrationality`: liminf growth → irrationality sequence
4. `truncation_insufficient`: requires concrete irrationality / non-irrationality sequence witnesses

### Files Modified

- `src/data/proofs/erdos-263/meta.json` (sorries 5→4, lineCount 342→385)

---

## Session 2026-04-13 (Session 1) — Initial Survey + First Proof

**Mode**: FRESH (EMPTY knowledge tier)
**Outcome**: progress — proved doubleExp_not_folklore_growth

### What I Found

The stub file `proofs/Proofs/Stubs/Erdos263Problem.lean` already existed (265 lines, 7 sorries, 0 axioms)
with the full mathematical framework:
- `IsIrrationalitySequence`: definition (Part II)
- `doubleExp`: 2^{2^n} sequence (Part II)
- `HasFolkloreGrowth`, `HasSuperexponentialGrowth`: growth conditions (Parts III-IV)
- `HasKovacTaoCondition`: the 2024 negative result condition (Part V)
- 2 proved theorems: `doubleExp_square_growth` (a_{n+1}=a_n²), `doubleExp_strictly_increasing`
- 1 proved theorem: `doubleExp_convergent` (Σ 1/2^{2^n} converges by geometric comparison)

### What I Proved

**`doubleExp_not_folklore_growth`**: ¬HasFolkloreGrowth doubleExp

Key insight: `(2^{2^n})^{1/2^n} = 2^{(2^n)*(1/2^n)} = 2^1 = 2` — the function is constantly 2,
which cannot tend to ∞.

Proof technique: `rpow_natCast` + `rpow_mul` to compute the exponent, then `Filter.tendsto_atTop`
to extract the contradiction (constant 2 can't be ≥ 3 eventually).

Also: `characterization_gap` depends on this theorem (proves ∃ a with superexponential but not
folklore growth — witnessing with doubleExp). Since `doubleExp_superexponential` still has sorry,
`characterization_gap` still has sorry.

### Files Modified

- `proofs/Proofs/Stubs/Erdos263Problem.lean` (265 → 285 lines, 7 → 6 sorries)
- `src/data/proofs/erdos-263/meta.json` (sorries 7→6, lineCount 265→285)
- `src/data/research/problems/erdos-263.json`

### Remaining Sorries (6)

1. `folklore_irrationality`: aₙ^{1/2^n} → ∞ ⟹ Σ 1/aₙ irrational (deep)
2. `kovac_tao_not_irrationality`: The 2024 negative result (deep, non-trivial)
3. `positive_condition_irrationality`: liminf aₙ₊₁/aₙ^{2+ε} > 0 ⟹ irrationality sequence (deep)
4. `factorial_no_folklore_growth`: ¬HasFolkloreGrowth factorial_seq (routine)
5. `doubleExp_superexponential`: HasSuperexponentialGrowth doubleExp (routine analysis)
6. `truncation_insufficient`: Any finite truncation loses irrationality info (structural)

### Next Steps

1. Prove `doubleExp_superexponential`: (2^{2^n})^{1/n} = 2^{2^n/n} → ∞ since 2^n/n → ∞
2. Prove `factorial_no_folklore_growth`: (n!)^{1/2^n} → 1 ≠ ∞ (Stirling or direct estimate)
3. Submit remaining deep sorries to Aristotle (folklore, KT condition, positive condition)

## Session 2026-04-24 (Session 10) — Port Aristotle proofs (7→5 sorries)

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: progress — ported 2 proofs to Erdos263Aristotle.lean, eliminating 2 sorries

### What I Did

- Identified discrepancy: Erdos263Aristotle.lean had sorries for `doubleExp_tail_pos` and
  `doubleExp_tail_bound`, but both had been proved in Stubs/Erdos263Problem.lean in sessions 5-8.
- Ported both proofs to the Aristotle companion file:
  - `doubleExp_tail_pos`: geometric comparison with (1/2)^k via nat_le_two_pow
  - `doubleExp_tail_bound`: full D*tail < 1/(D-1) via geometric series r=1/D²
- All 3 Aristotle targets now 0-sorry (`tsum_split_at` was already proved)

### Current State
- 4 deep sorries in Erdos263Problem.lean (all BLOCKED — require non-Mathlib mathematics):
  1. `folklore_irrationality`: Mahler criterion (requires analytic number theory ~200+ lines)
  2. `kovac_tao_not_irrationality`: Kovač-Tao 2024 Egyptian fraction construction
  3. `positive_condition_irrationality`: liminf analysis
  4. `truncation_insufficient`: needs a proved irrationality sequence as witness
- 0 sorries in Erdos263Aristotle.lean (complete)

### Assessment
Problem is BLOCKED on all remaining sorries. No tractable path forward until:
- `folklore_irrationality` gets a Mathlib proof, OR
- An alternative irrationality sequence is identified with elementary proof

### Next Steps
- Update problem phase to BLOCKED
- No more tractable work remaining this session
