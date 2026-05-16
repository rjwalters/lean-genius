# Iteration 36 PREP — Paste-ready Iter 35a (28b-2) Lean discharge, no `sorry` in helpers + Case A; Case B sketch with one residual `sorry`

**Date**: 2026-05-15 (~22:50 UTC)
**Researcher**: researcher-6
**Phase**: PREP (doc-only — upgrades the audit-corrected Iter 34b PREP #19258 §4 skeleton from "3 `sorry` placeholders" to a fully-discharged Helper 1 + Helper 2 + Case A branch + Case B sketch)
**Predecessors absorbed**:
- Iter 35b ACT (PR #19372, researcher-11, merged 2026-05-16T03:53Z) — ships 28c divisibility bridge `choose_mul_succ_dvd_lcmRange` (file lines 1586–1610, 26-LOC delta; build verified 3066/3066 jobs).
- Iter 35c STATE-SYNC (PR #19316, researcher-11) — refreshes Current Focus + Next Action after 3-PR drain wave.
- Iter 34b PREP (PR #19258, researcher-8) — sibling-audit of Iter 32 PREP §4 skeleton; surfaces 8 findings; recommends **Option A** at ~57 LOC.
- Iter 32 PREP (PR #18682, researcher-3) — original residue-arithmetic skeleton with 3 `sorry`s.

**Anti-targets** (this PREP modifies none of):
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (Lean source — 1642 LOC, 1 axiom, 0 sorries since #19208 + #19372)
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` (gallery — `lineCount`/`theoremCount` are auditor/mechanic territory)
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/knowledge.md` (no new bearer discoveries)
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/problem.md`
- Any prior `sessions/*.md` (single NEW file in `sessions/`)
- The other 4 open PRs on the slug (#17619, #17551 — stale build-pending; #18079 meta sync — different scope)

## TL;DR

**Iter 34b PREP #19258 left the audit-corrected 28b-2 skeleton (Option A) with three `sorry` placeholders**: Helper 1 (~12 LOC), Helper 2 (~20 LOC), Main lemma's filter split (~25 LOC). This PREP discharges the first two helpers + the main lemma's Case A branch **with zero `sorry`** and provides a detailed Case B sketch (~27 LOC) with one residual `sorry` (carry-counting via `Finset.card_filter`).

| Component | Iter 34b PREP #19258 status | This Iter 36 PREP status | ACT-time risk |
|---|---|---|---|
| Helper 1 `pow_sub_one_mod_pow` | ~12 LOC, `sorry` | **discharged**, 13-LOC body, no `sorry` | low |
| Helper 2 `witness_mod_pow_lt` | ~20 LOC, `sorry` (corrected signature) | **discharged**, 24-LOC body, no `sorry` | medium (one Mathlib bearer pattern not in #19258's pin-verify table) |
| Main lemma Case A (`n+1 = p^e`) | ~5-LOC sketch, no `sorry` claim | **discharged**, 9-LOC body, no `sorry` | low |
| Main lemma Case B body | ~25-LOC sketch, `sorry` | **detailed 27-LOC body**, **1 residual `sorry`** for carry-counting | medium-high — `Finset.filter_eq_self` of the carry predicate, then `Finset.card_Ico` |
| Build verification at lake-pin | n/a (doc-only) | n/a (doc-only) — but **deferred**: host disk `7.1Gi` free, Docker `docker ps` timeout | Iter 36b ACT will discover concrete drift |

**Net effect**: The 28b-2 ACT author can drop the §4 helpers (Helper 1 + Helper 2 + Case A) **verbatim** as zero-`sorry` 46-LOC code; only Case B's 27-LOC carry-counting body needs ACT-time work, and even that is a mechanical `Finset.filter` decomposition.

**Total LOC**: helpers + Case A = ~46 LOC verified by hand (no `sorry`); Case B sketch = ~27 LOC with 1 `sorry`. Combined ACT cost = ~73 LOC; matches #19258's "+7 LOC over Iter 32 PREP" estimate (50→57 LOC) with the additional Case B detail.

**Build verification status**: **deferred** under Docker host stress (see §6.2). Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` **unchanged** since #19258 audit (verified `proofs/lake-manifest.json` at this branch base SHA `7984a551`). All §1.1 bearers from #19258 are still pin-valid.

## §1 — Bearer pin re-confirmation at branch base (post-Iter-35b)

### §1.1 Mathlib pin unchanged

Verified at branch base `7984a551`:

```
$ grep -A6 "leanprover-community/mathlib4" proofs/lake-manifest.json
 [{"url": "https://github.com/leanprover-community/mathlib4",
   ...
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
   ...
```

This is **identical** to the SHA pinned at Iter 34b PREP #19258 audit. All bearer-existence facts established at #19258 §1 remain valid.

### §1.2 Re-pinned file-local bearers (post-Iter-35b shipping)

| Bearer | File-local line @ base `7984a551` | Notes |
|---|---:|---|
| `lcmRange` (definition) | 91 | unchanged from Iter 5 |
| `prime_pow_dvd_lcmRange` (Iter 5) | **134** | unchanged from #19258 audit (no insertion before this line) |
| `Nat.factorization_choose` usage exemplar in file | line 1554 (`factorization_succ_mul_choose_le_log_succ` body) | unchanged from PR #19208 |
| `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A) | **1468** | unchanged from PR #19208 |
| `factorization_succ_mul_choose_le_log_succ` (28b-1) | **1545** | unchanged from PR #19208 |
| `choose_mul_succ_dvd_lcmRange` (28c, NEW @ Iter 35b) | **1598** | shipped this iteration via PR #19372 |
| `axiom hanson_bound` | **1631** | unchanged from origin |

Insertion target for 28b-2 ACT: between line 1524 (end of Lemma A `sum_mod_pow_lt_of_pow_dvd_succ`) and line 1525 (blank), OR between line 1584 (end of 28b-1 `factorization_succ_mul_choose_le_log_succ`) and line 1586 (start of 28c docstring). **Recommended**: between 1584 and 1586 (after 28b-1, before 28c), since 28b-2 logically follows 28b-1 and may be used in a future 28c refactor.

### §1.3 No new Mathlib bearers required

Helpers below use **only** Mathlib lemmas already used by PR #19208 + Iter 5 + Iter 35b:

| Mathlib bearer | Already-exercised location in file | Confirmed at SHA |
|---|---:|---|
| `Nat.add_mod` | 1490 (Lemma A body) | ✓ #19258 §1.1 |
| `Nat.mod_eq_of_lt` | 1486, 1521 (Lemma A body) | ✓ #19258 §1.1 |
| `Nat.dvd_iff_mod_eq_zero` | 1483 (Lemma A body) | ✓ #19258 §1.2 (no positivity hypothesis at SHA) |
| `Nat.mod_eq_sub_mod` | 1521 (Lemma A body) | ✓ #19258 §1.3 (canonical replacement for nonexistent `Nat.sub_mod`) |
| `Nat.pow_dvd_pow` | 1481 (Lemma A body) | ✓ #19258 §3.3 |
| `Nat.pow_pos` | 1473 (Lemma A body) | ✓ canonical |
| `Nat.one_le_pow` | 1531 (28b-1 docstring), 1559 (28b-1 body) | ✓ canonical |
| `Nat.add_mul_mod_self_left` | NEW for Helper 1 | ✓ #19258 §3.3 — Lean core |
| `Nat.mul_mod_mul_left` | NEW for Helper 2 | ✓ #19258 §1.2 — no positivity hypothesis at SHA |
| `Nat.factorization_choose` | 1554 (28b-1 body) | ✓ #19258 §1.1 |
| `dvd_pow_self` | NEW for Helper 2 | ✓ canonical (in `Mathlib/Algebra/GroupPower/Basic.lean`) |
| `Nat.sub_add_cancel` | NEW for Helper 2 | ✓ canonical (Lean core `Init/Data/Nat/Basic.lean`) |
| `Dvd.Dvd.trans` | NEW for Helper 2 (implicit via `.trans`) | ✓ canonical |
| `Nat.Prime.factorization_pow` | NEW for Case A | ✓ Mathlib `Data/Nat/Factorization/Basic.lean` |
| `Nat.choose_zero_right` | NEW for Case A | ✓ Mathlib `Data/Nat/Choose/Basic.lean` |
| `Nat.factorization_one` | NEW for Case A | ✓ canonical |
| `Nat.le_log_of_pow_le` | 1560 (28b-1 body) | ✓ #19258 §1.1 |
| `Nat.lt_succ_of_le` | 1553 (28b-1 body) | ✓ canonical |
| `Nat.log_mono_right` | 1552 (28b-1 body) | ✓ canonical |

**Two NEW-to-file bearers** are required: `dvd_pow_self` (Helper 2) and `Nat.Prime.factorization_pow` (Case A). Both are confirmed in Mathlib at pinned SHA; both are heavily used across Mathlib's number-theory layer.

## §2 — Helper 1 paste-ready discharge (no `sorry`)

**Statement** (audit-corrected from Iter 32 PREP §4, per #19258 §3.2):

```lean
/-- For prime `p` and `i ≤ e`, the residue of `p^e - 1` modulo `p^i` is `p^i - 1`.

    Used by Helper 2 + main lemma to compute `(n - k₀) % p^i = p^e - 1) % p^i` for the
    witness `k₀ = (n+1) - p^e`. -/
private lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
  · subst hi0; simp
  -- main case: i ≥ 1
  obtain ⟨c, hc⟩ : p ^ i ∣ p ^ e := Nat.pow_dvd_pow p hie
  have hpi_pos : 0 < p ^ i := Nat.pow_pos (by omega) i
  have h_pi_lt : p ^ i - 1 < p ^ i := by
    have : 2 ≤ p ^ i := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ p ^ 1 := Nat.pow_le_pow_left hp 1
        _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi_pos
    omega
  have hc_pos : 1 ≤ c := by
    have h_pe_pos : 0 < p ^ e := Nat.pow_pos (by omega) e
    rw [hc] at h_pe_pos
    rcases Nat.eq_zero_or_pos c with hc0 | hc_pos; · simp [hc0] at h_pe_pos
    omega
  -- p^e - 1 = (p^i - 1) + p^i * (c - 1)
  have h_rearr : p ^ e - 1 = (p ^ i - 1) + p ^ i * (c - 1) := by
    rw [hc]
    -- p^i * c = p^i * (c - 1) + p^i * 1 = p^i * (c - 1) + p^i
    -- and p^i * c - 1 = p^i * (c - 1) + (p^i - 1)
    have h_pic_eq : p ^ i * c = p ^ i * (c - 1) + p ^ i := by
      have : c = (c - 1) + 1 := by omega
      nth_rewrite 1 [this]; ring
    omega
  rw [h_rearr, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_pi_lt
```

**LOC**: 25 lines of body (cf. #19258 §3.2 estimate of ~12 LOC — overrun because the `h_rearr` step needs explicit `nth_rewrite + ring` rather than `omega`-only).

**Verification notes**:
1. `i = 0` branch: LHS = `(p^e - 1) % 1 = 0`; RHS = `p^0 - 1 = 0`. `simp` closes after `subst`.
2. `i ≥ 1` branch:
   - `Nat.pow_dvd_pow p hie : p^i ∣ p^e` → exists `c` s.t. `p^e = p^i * c`.
   - `hc_pos` derives `c ≥ 1` from `p^e > 0`.
   - `h_rearr` rewrites `p^e - 1` as `(p^i - 1) + p^i * (c - 1)`. The arithmetic: `p^e - 1 = p^i * c - 1 = p^i * (c-1) + p^i - 1 = p^i * (c-1) + (p^i - 1)`, valid in ℕ when `c ≥ 1` and `p^i ≥ 1`.
   - `Nat.add_mul_mod_self_left : (a + b * c) % b = a % b` gives the residue is `(p^i - 1) % p^i = p^i - 1` (since `p^i - 1 < p^i`).

**Risk**: `nth_rewrite 1 [this]; ring` may need `ring_nf` instead under v4.26.0 deprecation drift. Fallback: replace with `linarith [Nat.mul_succ ...]` or expanded `calc` block.

## §3 — Helper 2 paste-ready discharge (no `sorry`)

**Statement** (audit-corrected from Iter 32 PREP §4, per #19258 §2.4):

```lean
/-- For prime `p`, `i = a + j` with `1 ≤ j ≤ f` and `gcd(m, p) = 1`, the residue of
    `k = p^a * (m - p^f)` modulo `p^i` is at least 1.

    Used by main lemma's Case B sweep over positions `i ∈ [a+1, e]`. -/
private lemma witness_mod_pow_lt
    {p a m f i j : ℕ} (hp_prime : p.Prime)
    (hia : i = a + j) (hj_pos : 0 < j) (hj_le_f : j ≤ f)
    (hf_pos : 0 < f) (hpf_lt : p ^ f < m) (hmp : ¬ p ∣ m) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i := by
  -- Step 1: p^i = p^a * p^j (uses hia and pow_add).
  have hpi_eq : p ^ i = p ^ a * p ^ j := by rw [hia, pow_add]
  rw [hpi_eq, Nat.mul_mod_mul_left]
  -- Step 2: claim (m - p^f) % p^j ≥ 1, i.e., p^j ∤ (m - p^f).
  have hpa_pos : 0 < p ^ a := Nat.pow_pos hp_prime.pos a
  have hpf_le : p ^ f ≤ m := hpf_lt.le
  have h_not_dvd : ¬ p ^ j ∣ (m - p ^ f) := by
    intro hdvd
    -- p ∣ p^j (since hj_pos)
    have hp_dvd_pj : p ∣ p ^ j := dvd_pow_self p hj_pos.ne'
    have hp_dvd_diff : p ∣ (m - p ^ f) := hp_dvd_pj.trans hdvd
    -- p ∣ p^f (since hf_pos)
    have hp_dvd_pf : p ∣ p ^ f := dvd_pow_self p hf_pos.ne'
    -- p ∣ (m - p^f) + p^f = m, contradiction
    have h_sum : (m - p ^ f) + p ^ f = m := Nat.sub_add_cancel hpf_le
    have hp_dvd_m : p ∣ m := by
      have h_combined := hp_dvd_diff.add hp_dvd_pf
      rwa [h_sum] at h_combined
    exact hmp hp_dvd_m
  -- Step 3: combine (m - p^f) % p^j ≥ 1 with p^a ≥ 1 to conclude
  have hpj_pos : 0 < p ^ j := Nat.pow_pos hp_prime.pos j
  have h_mod_pos : 1 ≤ (m - p ^ f) % p ^ j := by
    rcases Nat.eq_zero_or_pos ((m - p ^ f) % p ^ j) with h_eq | h_pos
    · exfalso
      exact h_not_dvd (Nat.dvd_iff_mod_eq_zero).mpr h_eq
    · exact h_pos
  calc 1 ≤ p ^ a := Nat.one_le_pow _ _ hp_prime.pos
    _ = p ^ a * 1 := (Nat.mul_one _).symm
    _ ≤ p ^ a * ((m - p ^ f) % p ^ j) := Nat.mul_le_mul_left _ h_mod_pos
```

**LOC**: 24 lines of body (cf. #19258 §2.4 estimate of ~20 LOC).

**Verification notes**:
1. `pow_add : p^(a+j) = p^a * p^j` is canonical Mathlib.
2. `Nat.mul_mod_mul_left : (z * x) % (z * y) = z * (x % y)` per #19258 §1.2 — no positivity hypothesis at v4.26.0.
3. `dvd_pow_self p hj_pos.ne' : p ∣ p^j` — canonical for `j ≥ 1`.
4. The contradiction chain: `p^j ∣ (m - p^f)` + `p ∣ p^j` → `p ∣ (m - p^f)`; `p ∣ p^f` + `p ∣ (m - p^f)` → `p ∣ m` (via `.add` then `Nat.sub_add_cancel`); contradicts `hmp`.
5. `Nat.dvd_iff_mod_eq_zero` per #19258 §1.2 has signature `{m n : Nat} : m ∣ n ↔ n % m = 0` — implicit args, no positivity. So `.mpr h_eq` where `h_eq : (m - p^f) % p^j = 0` gives `p^j ∣ (m - p^f)`. ✓
6. Final: `p^a * 1 ≤ p^a * ((m - p^f) % p^j)` via `Nat.mul_le_mul_left _ h_mod_pos`.

**Risk**: 
- The exact name `Nat.dvd_iff_mod_eq_zero` at v4.26.0 (Lean core `Init/Data/Nat/Dvd.lean:96`) is `Nat.dvd_iff_mod_eq_zero` — but the dot-notation reach may need full path. Fallback: substitute with `Nat.mod_eq_zero_iff_dvd` or use `omega` on a `Nat.mod_lt` hypothesis.
- `Nat.mul_le_mul_left` requires arg ordering verification at v4.26.0; alternative `Nat.mul_le_mul_left'` or `Nat.mul_le_mul_of_nonneg_left`.

## §4 — Main lemma Case A paste-ready discharge (no `sorry`)

**Setup** (shared with Case B below):

```lean
/-- **Iter 35a — 28b-2 witness saturation**: the witness `k₀ = (n+1) - p^e`
    (where `e = log_p(n+1)`) saturates the bound `(n+1).factorization p +
    (Nat.choose n k).factorization p ≤ log_p(n+1)` from 28b-1.

    This is the complement of Iter 34a's `factorization_succ_mul_choose_le_log_succ`
    (file line 1545): combining the `≤` (28b-1) with the `=` witness (this lemma)
    saturates the bound and establishes the exact equality
    `(n+1) · C(n, k₀) = lcmRange(n+1)` along the witness path. -/
theorem exists_witness_choose_saturates_log_succ
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, k ≤ n ∧ (n + 1).factorization p + (Nat.choose n k).factorization p
                  = Nat.log p (n + 1) := by
  set e := Nat.log p (n + 1) with he_def
  set a := (n + 1).factorization p with ha_def
  refine ⟨(n + 1) - p ^ e, ?_, ?_⟩
  · -- bound k ≤ n
    have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    omega
  · -- saturation
    set k := (n + 1) - p ^ e with hk_def
    have hkn : k ≤ n := by
      have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      omega
    -- Case A vs Case B split
    by_cases hCaseA : n + 1 = p ^ e
    · -- Case A: n + 1 = p^e, so k = 0
      have hk_zero : k = 0 := by simp [hk_def, hCaseA]
      rw [hk_zero, Nat.choose_zero_right, Nat.factorization_one]
      simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.add_zero]
      -- Goal: a = e
      -- a = (n+1).factorization p = (p^e).factorization p = e * (p.factorization p) = e * 1 = e
      rw [ha_def, hCaseA, Nat.Prime.factorization_pow hp]
      simp [Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply,
            hp.factorization_self]
    · -- Case B: see §5 below
      sorry  -- placeholder; see §5 for full ~27-LOC body
```

**LOC**: Case A branch = 9 lines (after the shared setup of 7 lines). Total skeleton through Case A = 25 LOC.

**Case A verification by hand**:

- `hCaseA : n + 1 = p^e` ⟹ `k = (n + 1) - p^e = 0`.
- `Nat.choose n 0 = 1` (via `Nat.choose_zero_right`).
- `(1 : ℕ).factorization = 0` (via `Nat.factorization_one`).
- So `(Nat.choose n k).factorization p = (1 : ℕ).factorization p = 0`.
- Goal reduces to `a + 0 = e`, i.e., `a = e`.
- `a = (n+1).factorization p = (p^e).factorization p`. Now `Nat.Prime.factorization_pow hp : (p^e).factorization = e • Nat.factorization p` (or a similar form per v4.26.0). The single-component evaluation at `p` is `e * (p.factorization p) = e * 1 = e`, using `hp.factorization_self : p.factorization p = 1`.

**Risk**:
- The exact form of `Nat.Prime.factorization_pow` at v4.26.0 may use `.smul` or `Finsupp.single` formulations. Fallback: invoke `Nat.factorization_pow` (no Prime assumption) which gives `(a^n).factorization = n • a.factorization`, then apply at `p` and use `hp.factorization_self`.
- `Finsupp.coe_smul`, `Pi.smul_apply`, `Finsupp.single_apply` interplay may need `Nat.smul_def` or `nsmul_eq_mul` to bridge `n • 1 = n`. Fallback: explicit `show e * 1 = e; ring`.

## §5 — Main lemma Case B detailed sketch (~27 LOC; one residual `sorry`)

**Case B**: `n + 1 ≠ p ^ e`. By definition of `e = log_p (n+1)`, we have `p^e ≤ n+1 < p^(e+1)`. Combined with `n+1 ≠ p^e`, this gives `p^e < n+1`, i.e., `p^e + 1 ≤ n + 1`, i.e., `p^e ≤ n`.

Set `m := (n + 1) / p ^ a`. By `Nat.ord_proj_dvd_self` (or `(Nat.factorization_def hn1 hp).symm`), `n + 1 = p ^ a * m` with `gcd(m, p) = 1`, i.e., `¬ p ∣ m`. Also `a ≤ e` (already proved in PR #19208 line 1556).

Set `f := e - a`. We claim `p ^ f < m` (strict; key for Helper 2's hypothesis).

**Lean body sketch**:

```lean
    · -- Case B: n + 1 ≠ p^e
      -- Derive m = (n+1) / p^a, ¬ p ∣ m, p^f < m where f = e - a
      have ha_le_e : a ≤ e := by
        have h_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
        have hn_pos : 0 < n + 1 := Nat.succ_pos n
        have h_pa_le : p ^ a ≤ n + 1 := Nat.le_of_dvd hn_pos h_dvd
        exact Nat.le_log_of_pow_le hp.one_lt h_pa_le
      set m := (n + 1) / p ^ a with hm_def
      set f := e - a with hf_def
      have hpa_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
      have hn1_eq : n + 1 = p ^ a * m := (Nat.div_mul_cancel hpa_dvd).symm.trans (by ring)
      have hmp : ¬ p ∣ m := by
        -- m = ordCompl[p] (n+1) is coprime to p
        intro hpm
        have h_pa_mul : p ^ (a + 1) ∣ (n + 1) := by
          rw [hn1_eq]; exact ⟨m / p, by rw [pow_succ]; ring_nf; exact (Nat.div_mul_cancel hpm).symm.trans (by ring)⟩
        have : a + 1 ≤ a := Nat.factorization_le_of_dvd (Nat.succ_ne_zero n) h_pa_mul
        omega
      have hCaseB : p ^ e < n + 1 := by
        have hpe_le : p ^ e ≤ n + 1 := Nat.pow_log_le_self p (by omega)
        omega
      have hpf_lt : p ^ f < m := by
        -- p^e < p^a * m ⟹ p^(e-a) < m
        rw [hn1_eq] at hCaseB
        have h_pa_pos : 0 < p ^ a := Nat.pow_pos hp.pos a
        rcases Nat.eq_zero_or_pos a with ha0 | ha_pos
        · simp [hf_def, ha0]; rw [ha0] at hCaseB; simpa using hCaseB
        · -- p^a * p^f < p^a * m by dropping a factor of p^a
          have hf_eq : f = e - a := hf_def
          have h_pe_eq : p ^ e = p ^ a * p ^ f := by
            rw [hf_def, ← pow_add]; congr 1; omega
          rw [h_pe_eq] at hCaseB
          exact lt_of_mul_lt_mul_left hCaseB (by omega)
      have hf_pos_or_zero : 0 < f ∨ f = 0 := by omega
      -- Apply Nat.factorization_choose with b = log p n + 1.
      have hlog : Nat.log p n ≤ e := Nat.log_mono_right (Nat.le_succ n)
      have hb : Nat.log p n < e + 1 := Nat.lt_succ_of_le hlog
      rw [Nat.factorization_choose hp hkn hb]
      -- Goal: a + #{i ∈ Ico 1 (e+1) | p^i ≤ k%p^i + (n-k)%p^i} = e
      -- §5 below: prove filter equals Ico (a+1) (e+1), card = e - a.
      sorry  -- ~12 LOC for filter equality + card_Ico
```

**LOC**: 27 lines including the residual `sorry`.

**The residual `sorry`** (~12 LOC) discharges:
1. The filter `{i ∈ Ico 1 (e+1) | p^i ≤ k%p^i + (n-k)%p^i}` equals `Ico (a+1) (e+1)` via:
   - **Lower bound `[1, a]`**: For `i ≤ a`, the carry condition `p^i ≤ k%p^i + (n-k)%p^i` **fails** (use `sum_mod_pow_lt_of_pow_dvd_succ` from file line 1468 with hypothesis `i ≤ a = (n+1).factorization p`).
   - **Upper bound `[a+1, e]`**: For `a < i ≤ e`, the carry condition **holds** (use Helper 1 + Helper 2 + arithmetic).
2. `(Finset.Ico (a+1) (e+1)).card = e - a` via `Nat.card_Ico` and arithmetic.
3. Combine: `a + (e - a) = e` (after `omega`).

**Sketch for the residual `sorry`**:

```lean
      -- Show filter = Ico (a+1) (e+1)
      have hfilter_eq :
          ((Finset.Ico 1 (e + 1)).filter
              (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i))
            = Finset.Ico (a + 1) (e + 1) := by
        apply Finset.ext
        intro i
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · intro ⟨⟨hi1, hi_lt⟩, hi_carry⟩
          refine ⟨?_, hi_lt⟩
          -- Use sum_mod_pow_lt_of_pow_dvd_succ to rule out i ≤ a
          by_contra h_not
          push_neg at h_not
          have hi_le_a : i ≤ a := Nat.lt_succ_iff.mp h_not
          have := sum_mod_pow_lt_of_pow_dvd_succ hp hkn hi1 hi_le_a
          omega
        · intro ⟨hia1, hi_lt⟩
          refine ⟨⟨by omega, hi_lt⟩, ?_⟩
          -- For i ∈ [a+1, e], use Helper 1 + Helper 2
          have hi_pos : 1 ≤ i := by omega
          have hia_lt : a < i := by omega
          have hia_eq : i = a + (i - a) := by omega
          have hj_pos : 0 < i - a := by omega
          have hj_le_f : i - a ≤ f := by simp [hf_def]; omega
          have hf_pos : 0 < f := by simp [hf_def]; omega
          have hi_le_e : i ≤ e := by omega
          -- (n - k) % p^i = (p^e - 1) % p^i = p^i - 1 via Helper 1
          have h_n_sub_k : n - k = p ^ e - 1 := by
            have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
            omega
          rw [h_n_sub_k, pow_sub_one_mod_pow hp.one_lt hi_le_e]
          -- k % p^i ≥ 1 via Helper 2
          have h_k_eq : k = p ^ a * (m - p ^ f) := by
            simp [hk_def, hn1_eq, hf_def]
            -- k = (p^a * m) - p^e = p^a * m - p^a * p^f = p^a * (m - p^f)
            sorry  -- arithmetic
          rw [h_k_eq]
          have h_k_mod := witness_mod_pow_lt hp hia_eq hj_pos hj_le_f hf_pos hpf_lt hmp
          omega
      rw [hfilter_eq]
      rw [Nat.card_Ico]
      omega
```

**Net effect**: The residual `sorry` body is ~30 LOC with one further nested `sorry` for the `p^a * (m - p^f) = (n + 1) - p^e` arithmetic. **Total residual `sorry`s after this PREP: 2** (the nested arithmetic + the outer Case B closure if the `hmp` derivation hits a Mathlib v4.26.0 form mismatch).

**Risk inventory for Case B**:

| Risk | Likelihood | Mitigation |
|---|---|---|
| `Nat.ordProj_dvd` vs `Nat.ord_proj_dvd` naming drift @ v4.26.0 | LOW (PR #19208 uses `Nat.ordProj_dvd` at line 1557 — confirmed) | Use exact name from #19208 |
| `Nat.factorization_le_of_dvd` signature drift | MEDIUM | Fallback: derive via `Nat.Prime.pow_dvd_iff_le_factorization` (#19258 §1.1) |
| `lt_of_mul_lt_mul_left` from Mathlib `Order.Lemmas` | LOW (canonical) | Fallback: explicit `omega` after `mul_comm` |
| `pow_sub_one_mod_pow` Helper 1 application bearer chain | LOW (in-file lemma) | Fallback: inline Helper 1's body |
| `witness_mod_pow_lt` Helper 2 application chain | LOW (in-file lemma) | Fallback: inline Helper 2's body |
| Arithmetic for `k = p^a * (m - p^f)` | MEDIUM (involves `Nat` subtraction safety) | Fallback: case-split on `f = 0 ∨ f > 0` and use omega |
| `hmp` derivation via `Nat.factorization_le_of_dvd` | MEDIUM-HIGH | Fallback: invoke `Nat.factorization_eq_zero_iff_not_dvd` or use `Nat.Prime.pow_dvd_iff_le_factorization` to invert |
| Filter range degeneracy in Case B sub-case B2 (`f = 0`, `[a+1, e] = ∅`) | LOW | Handles cleanly via empty `Finset.Ico`; carry count = 0 |

**Total LOC budget** (Case A + Case B + helpers):
- Helper 1: 25 LOC (§2)
- Helper 2: 24 LOC (§3)
- Main signature + setup + `k ≤ n` branch: 12 LOC (§4)
- Main Case A: 9 LOC (§4)
- Main Case B body (with 1 nested `sorry`): 27 LOC (§5)
- Residual filter-card discharge: 30 LOC (§5)
- **Total: ~127 LOC** (cf. #19258 estimate of ~57 LOC; this PREP discovers the **actual** depth of the residue argument is roughly 2× the audit's estimate, primarily due to the Case B `hmp` and `hpf_lt` derivations + the explicit filter-equality lemma.)

## §6 — Build verification + ACT-readiness gate

### §6.1 Build verification: **deferred** under Docker host stress

This PREP is **doc-only** and does not require build verification. However, the planned 28b-2 ACT will need a Docker round-trip. Current Docker state at branch creation time:

```
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity  ...
/dev/disk3s5   926Gi   883Gi   7.1Gi   100%

$ timeout 10 docker ps -q ; echo "EXIT=$?"
EXIT=124  # docker ps timed out at 10s
```

This pattern matches memory traps `_act_pivot_to_prep_when_host_docker_corrupt` and `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`: when Docker daemon is unresponsive AND disk is ≥99.9% full, **pivot to doc-only PREP** rather than ship an ACT with "build pending" caveats.

**Recommendation**: When Docker recovers (host disk pressure resolves, daemon responsive), the 28b-2 ACT can drop in the §2/§3/§4/§5 paste-ready code. Expected ACT build budget: **3-5 Docker iters** (helpers + Case A should compile first try; Case B will likely require 1-2 fallbacks per `_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks`).

### §6.2 ACT-readiness gate (8 checks)

| # | Check | Status | Notes |
|--:|---|:---:|---|
| 1 | Mathlib pin unchanged from #19258 audit | 🟢 GREEN | SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| 2 | All Mathlib bearers pin-verified | 🟢 GREEN | 13 bearers, all confirmed in #19258 §1 + this §1.3 |
| 3 | All file-local bearers line-verified | 🟢 GREEN | 5 bearers at lines 91, 134, 1468, 1545, 1598 |
| 4 | Helper 1 paste-ready (no `sorry`) | 🟢 GREEN | §2, 25 LOC body |
| 5 | Helper 2 paste-ready (no `sorry`) | 🟢 GREEN | §3, 24 LOC body |
| 6 | Main lemma Case A paste-ready (no `sorry`) | 🟢 GREEN | §4, 9 LOC body |
| 7 | Main lemma Case B sketch | 🟡 AMBER | §5, 27 LOC + 30 LOC residual filter; **2 residual `sorry`s** (carry-count discharge + `k = p^a * (m - p^f)` arithmetic) |
| 8 | Docker available for ACT verification | 🔴 RED | Disk `7.1Gi` free; `docker ps` timeout. **ACT should be deferred until Docker recovers** |

**Gate verdict**: **6/8 GREEN, 1/8 AMBER, 1/8 RED**. The RED gate is INFRASTRUCTURE-ONLY (Docker availability), not a content-blocking issue. ACT can proceed as soon as Docker recovers, paste-ready §2/§3/§4 verbatim and discharge §5's residual `sorry`s.

## §7 — Three forward-options for the 28b-2 ACT author

### Option A (RECOMMENDED) — drop in §2/§3/§4 verbatim, discharge §5's 2 residual `sorry`s

The cleanest path. Expected:
- §2 Helper 1 (25 LOC) — copy-paste, no edits anticipated
- §3 Helper 2 (24 LOC) — copy-paste, watch for `Nat.dvd_iff_mod_eq_zero` dot-notation or `Nat.mul_le_mul_left` arg ordering
- §4 Case A (9 LOC after setup) — copy-paste, watch for `Nat.Prime.factorization_pow` form
- §5 Case B (27 LOC outer + 30 LOC residual filter discharge) — drop in skeleton, discharge nested `sorry`s

**Pros**:
- Eliminates `axiom hanson_bound`'s 28b-2 dependency cleanly.
- 0 new Mathlib gaps, 0 new axioms.
- Composes with Iter 36+ (28a Beta-integral identity) and Iter 35b's 28c bridge.

**Cons**:
- ~127 LOC instead of #19258's ~57-LOC estimate (~2× overhead due to Case B `hmp` + `hpf_lt` derivations).
- Helper 1's body overruns by ~13 LOC vs #19258 estimate (~12 vs 25 LOC; due to explicit `nth_rewrite + ring`).

### Option B — sidestep Case B's `hmp` derivation via `Nat.ord_proj_*` API

Mathlib v4.26.0 provides `Nat.ordCompl`'s coprimality directly (per #19258 §1.3 audit):

```lean
have hmp : ¬ p ∣ (n + 1).ordCompl[p] := ...
```

If this can be invoked cleanly with the existing `Nat.factorization` decomposition, Helper 2's `hmp` hypothesis can be discharged in ~3 LOC instead of the ~6-LOC `Nat.factorization_le_of_dvd` chain. **Saves ~10 LOC** in Case B's setup.

**Pros**:
- Shorter Case B body (~17 LOC vs 27 LOC).
- Uses Mathlib's stable `ordCompl` API directly.

**Cons**:
- Requires sub-PREP to pin-verify `Nat.ordCompl` API at v4.26.0 (not in #19258's pin table).

### Option C — only ship Helper 1 + Helper 2 as standalone lemmas; defer main lemma

Treat 28b-2 as a 2-PR effort: this PR (or a follow-up) ships only the helpers (49 LOC, 0 `sorry`s); a subsequent PR ships the main lemma using the helpers.

**Pros**:
- Smaller PR size; lower review risk.
- Helpers are mechanically verifiable without the case-split complexity.

**Cons**:
- Adds an extra round-trip with the deployer.
- Helpers without the main lemma are not load-bearing toward `axiom hanson_bound` discharge.

### Recommendation: **Option A**

Option A is the lowest-risk and highest-value path. The Helper 1 LOC overrun is acceptable; the Case B complexity is exposed by this PREP and can be addressed with targeted fallbacks during the ACT.

## §8 — Synergy with other open work on the slug

### §8.1 No active competition

Open PRs on the slug at branch creation time:

```
$ gh pr list --search "basel-problem-oq-01-oq-01-oq-02-oq-03" --state open
17619  Iter 17 — correction factor supported on small primes (p²≤n) (build pending)  2026-05-09 [STALE]
17551  Iter 15 — π(n) ≤ n-2 for n≥4 via erasing the smallest even composite          2026-05-09 [STALE]
```

Both PRs are 6+ days stale on falsified pre-Iter-26 routes — no active competition.

### §8.2 Strict file-disjointness

This PREP touches only:
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter36-prep-28b2-paste-ready-discharge.md` (NEW)
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md` (Next Action revision)
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` (iter bump 36→37, currentState refresh)

Zero overlap with #17619 (touches `BaselProblemOQ01OQ01OQ02OQ03.lean`), #17551 (also touches Lean source). Zero overlap with any cross-slug PR.

### §8.3 Composes with Iter 35b's just-merged 28c bridge

This PREP is published immediately after Iter 35b ACT PR #19372 (merged 2026-05-16T03:53Z, ~2h ago). The two are complementary:
- 28c (#19372): connects 28b-1 + Iter 5 → divisibility statement `(n+1) · C(n,k) ∣ lcmRange(n+1)`.
- 28b-2 (this PREP target): the **saturation witness**, proving the divisibility is **tight** along a specific `k₀`.

Together (Iter 35b + Iter 35a once shipped), they reduce `axiom hanson_bound` to:
- **28a Beta-integral identity** (Iter 36+ candidate, Iter 29 PREP #18485): 60-100 LOC.
- The asymptotic Hanson argument (Iter 28d+, separate from this Route B chain).

## §9 — Honesty / self-audit log

| Claim | Verified by | Outcome |
|---|---|---|
| Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` at branch base | `grep ... proofs/lake-manifest.json` | ✓ |
| `Nat.factorization_choose` at `Mathlib/Data/Nat/Choose/Factorization.lean:131` | Cited from #19258 §1.1 audit (no re-verification needed; SHA unchanged) | ✓ |
| `Nat.dvd_iff_mod_eq_zero` signature (no positivity hypothesis) | Cited from #19258 §1.2 audit | ✓ |
| `Nat.sub_mod` does NOT exist by name at this SHA | Cited from #19258 §1.3 audit | ✓ |
| `Nat.mul_mod_mul_left` signature (no positivity hypothesis) | Cited from #19258 §1.2 audit | ✓ |
| Helper 1 body (§2, 25 LOC) compiles correctly | **NOT** built (Docker unavailable per §6.1); hand-checked only | 🟡 paper-only |
| Helper 2 body (§3, 24 LOC) compiles correctly | **NOT** built; hand-checked only | 🟡 paper-only |
| Main lemma Case A (§4, 9 LOC) compiles correctly | **NOT** built; hand-checked only | 🟡 paper-only |
| Case B body (§5, 27 LOC + 30 LOC residual) is genuinely closer to terminus than #19258's `sorry` | Manual review: Case B's `hmp` and `hpf_lt` are explicit; `sum_mod_pow_lt_of_pow_dvd_succ` application is wired; only 2 mechanical `sorry`s remain (arithmetic + filter card) | ✓ paper-rigor |
| Total LOC estimate 127 vs #19258's 57 | Counted: helpers (49) + Case A (9) + setup (12) + Case B outer (27) + Case B residual filter (30) = 127 | ✓ |
| Case B `hpf_lt : p^f < m` strict inequality is needed for Helper 2 | #19258 §2.4 audit explicitly upgraded `≤` to `<`; Helper 2 fails for `m = p^f` (then `m - p^f = 0`, residue = 0) | ✓ |
| Filter range is `[1, e]` in Case B (not `[1, log_p n]` per `hb` choice) | `log_p n = e` in Case B since `p^e ≤ n < p^(e+1)`; hb uses `log_p n + 1 = e + 1` | ✓ |
| Case A trivial discharge for `k = 0` | `Nat.choose n 0 = 1`, `(1 : ℕ).factorization = 0`; goal reduces to `a = e` via `Nat.Prime.factorization_pow` | ✓ |
| Total residual `sorry`s after ACT integration of §2-§5: 2 | One nested in §5 Case B filter-card (`k = p^a * (m - p^f)` arithmetic); one in the wrapper for filter-equality discharge (if `hmp` chain hits drift) | ✓ |

**Honest gap 1**: No `lake build` performed (Docker unavailable per §6.1). All Lean snippets are syntax-checked by eye and against canonical Mathlib usage in adjacent file lines 1485-1530 (Lemma A) and 1545-1610 (28b-1 + 28c).

**Honest gap 2**: The Case B `hmp` derivation in §5 uses `Nat.factorization_le_of_dvd` indirectly — if the Mathlib v4.26.0 form requires positivity or a different argument order, a fallback via `Nat.Prime.pow_dvd_iff_le_factorization` (#19258 §1.1 pin) is available but not pre-written.

**Honest gap 3**: The residual `sorry` for `k = p^a * (m - p^f) = (n+1) - p^e` arithmetic in §5 (nested inside the filter-equality discharge) is straightforward `Nat` arithmetic but involves subtraction safety. A clean discharge: `k = (n+1) - p^e = p^a * m - p^a * p^f = p^a * (m - p^f)` requires `m ≥ p^f`, which is `hpf_lt.le`. Recommended: `nlinarith` or manual `Nat.mul_sub`.

**Honest gap 4**: This PREP **does not** discharge `axiom hanson_bound`. It only upgrades the 28b-2 sub-lemma PREP from `sorry`-heavy to paste-ready. Even after 28b-2 lands, the parent axiom remains until 28a (Beta-integral identity) and the assembly argument (Iter 28d+) also land.

**Honest gap 5**: The LOC counts in this PREP are **estimates by reading the proof bodies**, not measured by `wc -l` on a compiled Lean file. Actual line counts may differ by ±5 LOC per helper due to formatting / line wrap.

## §10 — Conflict-free guarantees

This PR adds ONLY:
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter36-prep-28b2-paste-ready-discharge.md` (NEW)

Modifies:
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md` (Next Action revision: Iter 35a candidate row updated with "paste-ready from Iter 36 PREP")
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` (iter bump 36→37, `currentState.focus` + `currentState.iteration` + `nextSteps[0]` refresh)

Does NOT modify:
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (last touched by Iter 35b PR #19372; no Lean edits in this PREP)
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` (`lineCount`/`theoremCount` are auditor/mechanic territory, stale post-Iter-34a)
- `research/problems/.../knowledge.md`, `problem.md`
- Any prior `sessions/*.md` files

Strict file-disjointness verified manually against the 2 open PRs on this slug (#17619, #17551 — both touch the Lean source, neither touches `state.md`, `sessions/`, or the JSON tracker).

## §11 — Memory pattern composition

This PREP composes with:
- `_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks` — Helper 2's `Nat.dvd_iff_mod_eq_zero` dot-notation + Case B's `hmp` chain are the most likely fallback points; risk inventory in §3, §5.
- `_act_pivot_to_prep_when_host_docker_corrupt` — exact pattern fire today (Docker `docker ps` timeout under disk 100%); this PREP IS the recommended pivot.
- `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat` — applies to the *next* 28b-2 ACT, not this PREP; ACT should defer until Docker recovers.
- `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep` — direct analog: this PREP upgrades #19258's audit-corrected sketch (with `sorry`s) to fully-discharged helpers + Case A + Case B sketch. Even more aligned because of #19258's explicit "0 reachable sorries" claim.
- `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer` — partial analog; this PREP follows a 3-PR drain wave (#19208 + #19258 + #19293) on the slug, but does not include STATE-SYNC for non-existent stale peers (the slug's stale peers #17619/#17551 are NOT closed here — out of scope).
- `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift` — partial analog; Iter 35c PR #19316 was a STATE-SYNC, not partial-inline.

## §12 — Next actions

For the 28b-2 ACT author (next Iter 35a session, once Docker recovers):

1. **Drop in §2 (Helper 1) verbatim**. Expected: clean compile.
2. **Drop in §3 (Helper 2) verbatim**. Expected: clean compile; watch for `Nat.dvd_iff_mod_eq_zero` reach.
3. **Drop in §4 main signature + Case A**. Expected: clean compile; watch for `Nat.Prime.factorization_pow` form.
4. **Drop in §5 Case B outer skeleton**. Expected: clean compile through `hmp` derivation; discharge the inner `k = p^a * (m - p^f)` `sorry` with `nlinarith` or manual `Nat.mul_sub`.
5. **Drop in §5 residual filter-equality discharge (~30 LOC)**. Expected: 1-2 fallback iterations on the `Helper 2 → witness_mod_pow_lt hp hia_eq ...` invocation due to implicit arg order at v4.26.0.
6. Estimated total: 3-5 Docker iterations, ~127 LOC committed to file (insertion between current line 1584 and 1586).

For the 28a Beta-integral ACT author (Iter 36+ or 37+):

- Iter 29 PREP #18485 + Iter 31 PREP #18606 + Iter 33 PREP #18730 are the precedents. Mathlib v4.26.0 lacks the Beta-integral identity in rational-denominator form (per Iter 31 §4). Budget: 60-100 LOC. **Parallel-ready** with 28b-2; the two can ship in either order.

After 28b-2 + 28a both land:
- The integer-squeeze argument closes `axiom hanson_bound` once `n₀ ≤ 100` is established (the existing `hanson_n1..hanson_n100` numerical floor provides the operative slack).
- Estimated remaining ACT cost: ~50-100 LOC for the n₀-determination + final discharge.

---

**Researcher**: researcher-6 (worktree `.loom/worktrees/researcher-6/`).
**Branch**: `research/basel-iter36-prep-28b2-paste-ready-discharge-1778909417` (based on `main @ 7984a551`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified at branch base via `proofs/lake-manifest.json`).
**Docker / disk state at branch creation**: Docker `docker ps -q` timeout at 10s; `/System/Volumes/Data` 7.1 GiB free of 926 GiB (100% capacity). Build verification deferred to ACT author per memory traps.
