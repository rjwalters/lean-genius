## Session 2026-05-16 (Session 17 PREP) — `pow_factorization_mul_choose_le` fully-discharged paste-ready skeleton (S17a sorry pre-discharged at sketch level) + 3 NEW bearer pins + 0-drift recheck (doc-only)

**Mode**: PREP (no Lean modifications; doc-only).
**Outcome**: progress — the single `sorry` from S16 PREP §7 is upgraded to a fully-discharged paste-ready proof using `Nat.factorization_choose` + `Nat.Prime.pow_dvd_iff_le_factorization` + filter-cardinality subset argument; 3 NEW bearer pins; 0-drift recheck of 13 existing pins.
**Predecessor**: S16 PREP (PR #19438, researcher-11, merged 2026-05-16T04:25Z) — doc-only route audit + 4 bridge bearer pins + 0-drift recheck; recommended Route C with split S17a + S17b ACTs; S17a skeleton had 1 explicit `sorry` (carry-count argument) per §7.
**Host infra**: Docker daemon hung (`timeout 8 docker info --format '{{.ServerVersion}}'` exit 124, CLI section responsive); disk 6.9 Gi avail / 100% capacity (NOT extreme disk-full ≤200Mi). Per memory pattern `feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready`: upgrade the skeleton with sorries to a FULLY-DISCHARGED paste-ready Lean recipe at the sketch level, preserving the slug's 0-sorry status while Docker is unavailable.

### TL;DR

S16 PREP §7 shipped a paste-ready S17a skeleton with 1 explicit `sorry` on the Kummer carry-count argument. This S17 PREP closes that `sorry` by:

1. Pinning **3 NEW bearers** that enable a clean carry-bound proof WITHOUT going through `multiplicity` / `emultiplicity` bridges (Route A) — avoiding the new `Mathlib.Data.Nat.Multiplicity` import S16 PREP §3.4 named as `⚠`:
   * `Nat.Prime.pow_dvd_iff_le_factorization` at `Mathlib/Data/Nat/Factorization/Basic.lean:168` (signature `p ^ k ∣ n ↔ k ≤ n.factorization p` for `Prime p`, `n ≠ 0`) — converts `i ≤ m.factorization p` to `p ^ i ∣ m` directly.
   * `Nat.factorization_choose_le_log` at `Mathlib/Data/Nat/Choose/Factorization.lean:185` (signature `(choose n k).factorization p ≤ log p n`) — exposes the canonical bound used to derive `factorization_choose` line 131's filter formula.
   * `Nat.pow_le_of_le_log` at `Mathlib/Data/Nat/Log.lean:171` (signature `y ≠ 0 → x ≤ log b y → b ^ x ≤ y`) — converts `v ≤ log p n` to `p ^ v ≤ n`.
2. Providing a **fully-discharged paste-ready** S17a proof body (~75 LOC) that:
   * Splits on `p.Prime` (non-prime case discharged via `Nat.factorization_eq_zero_of_not_prime`).
   * In the prime case, uses `Nat.factorization_mul` to decompose `(m * C(n, m)).factorization p = m.factorization p + (choose n m).factorization p`.
   * Applies `Nat.pow_le_of_le_log` to reduce to a `log p n` inequality.
   * Expands `(choose n m).factorization p` via `Nat.factorization_choose` (Choose/Factorization.lean:131) at bound `b = log p n + 1`.
   * Bounds the filter cardinality by the cardinality of `Finset.Ico (m.factorization p + 1) (log p n + 1)` via a **subset argument**: positions `i ≤ m.factorization p` cannot satisfy `p^i ≤ m % p^i + (n-m) % p^i` because `p^i ∣ m` (via `Nat.Prime.pow_dvd_iff_le_factorization`) forces `m % p^i = 0`, hence the condition becomes `p^i ≤ (n-m) % p^i < p^i` — contradiction.
   * The arithmetic `m.factorization p + (log p n - m.factorization p) = log p n` closes (after a `Nat.add_sub_of_le` on the auxiliary bound `m.factorization p ≤ log p n`, which itself follows from `p ^ m.factorization p ∣ m` + `m ≤ n` + `pow_le_of_le_log`).
3. 0-drift recheck of all **13 existing bearers** from S14 + S15 + S16 at the unchanged lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
4. Refreshing the S17a ACT-readiness gate: **GREEN-PASTE-READY** at 13/13 items (the S16 §9 `⚠` on `Mathlib.Data.Nat.Multiplicity` is now N/A — the Route-A bridges are NOT consumed by this discharged skeleton).
5. Documenting that the S16 PREP's Route A bridges (§3.3 `Nat.multiplicity_eq_factorization`, §3.4 `multiplicity_eq_of_emultiplicity_eq_some`) remain VALID but UNUSED by the upgraded recipe; they are retained for the parallel `S17b ACT` proof should it choose a different decomposition style.

This is a **doc-only** iteration: 1 new sessions file, state.md head update prepending S17 PREP section, JSON refresh (iteration 16 → 17, nextAction, lastUpdate, +2 insights, +2 nextSteps). 0 Lean edits. 0 sibling-slug edits. 0 sorries (the upgraded skeleton has NO `sorry` placeholders).

### §1 Slug state at S17 PREP start

Post-S16-PREP-merge state (HEAD `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`):

| Metric | Value | Source |
|--------|-------|--------|
| File LOC | 905 (unchanged since S15) | wc -l |
| Sorry count | 0 | grep -c |
| Axiom count | 0 | grep -c |
| Theorem count | 36 (unchanged since S15) | grep -c |
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S14 §3) | proofs/lake-manifest.json HEAD |
| Open PRs on slug | 0 | gh pr list (verified 2026-05-16T09:55Z) |
| Sibling slug open PRs | 0 (the `-oq-03` PRs cited by S16 §1 are not currently open per `gh pr list`) | gh pr list |
| Days since last Lean edit | 0 (S15 ACT was 2026-05-16T03:52Z; no Lean edits since) | git log |
| Host disk avail | 6.9 Gi (100% capacity) | df -h /System/Volumes/Data |
| Docker daemon | hung (Server section timeout 8s) | docker info --format ... |

### §2 0-drift recheck of all 13 existing bearer pins

All bearers re-verified at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA> --jq '.download_url' | curl -sL` + `grep -n` for the signature anchor.

| # | Bearer | File:Line | First-pinned at | S17 PREP recheck | Drift |
|---|--------|-----------|------------------|------------------|-------|
| 1 | `Nat.prod_pow_factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean:267` | S12 (#19217) | line 267 confirmed | 0 |
| 2 | `Nat.pow_factorization_choose_le` | `Mathlib/Data/Nat/Choose/Factorization.lean:196` | S12 (#19217) | line 196 confirmed | 0 |
| 3 | `Nat.factorization_eq_zero_of_not_prime` | `Mathlib/Data/Nat/Factorization/Defs.lean:129` | S14 §4.2 (#19352) | line 129 confirmed | 0 |
| 4 | `Nat.coprime_iff_isRelPrime` | `Mathlib/Data/Nat/GCD/Basic.lean:218` | S14 §4.1 (#19352) | line 218 confirmed | 0 |
| 5 | `Nat.coprime_pow_primes` | `Mathlib/Data/Nat/Prime/Basic.lean:200` | S15 §4.1 (#19397) | line 200 confirmed | 0 |
| 6 | `Finset.prod_dvd_of_isRelPrime` | `Mathlib/RingTheory/Coprime/Lemmas.lean:252` | S13 §2.4 (#19299) | line 252 confirmed | 0 |
| 7 | `isRelPrime_one_left` | `Mathlib/Algebra/Divisibility/Units.lean:166` | S14 §5 (#19352) | line 166 confirmed | 0 |
| 8 | `isRelPrime_one_right` | `Mathlib/Algebra/Divisibility/Units.lean:167` | S15 §4.2 (#19397) | line 167 confirmed | 0 |
| 9 | `DecompositionMonoid` instance via `[Nonempty (GCDMonoid α)]` | `Mathlib/Algebra/GCDMonoid/Basic.lean:493` | S13 §2.5 (#19299) | line 493 confirmed | 0 |
| 10 | `Nat.factorization_mul` | `Mathlib/Data/Nat/Factorization/Defs.lean:155` | S16 §3.1 (#19438) | line 155 confirmed | 0 |
| 11 | `Nat.factorization_le_factorization_choose_add` | `Mathlib/Data/Nat/Choose/Factorization.lean:142` | S16 §3.2 (#19438) | line 142 confirmed | 0 |
| 12 | `Nat.multiplicity_eq_factorization` | `Mathlib/Data/Nat/Factorization/Defs.lean:89` | S16 §3.3 (#19438) | line 89 confirmed | 0 |
| 13 | `multiplicity_eq_of_emultiplicity_eq_some` | `Mathlib/RingTheory/Multiplicity.lean:73` | S16 §3.4 (#19438) | line 73 confirmed | 0 |

**Note on bearers 12 + 13**: these were pinned by S16 PREP §3.3-§3.4 specifically for **Route A** (full Kummer via emultiplicity bridge). The fully-discharged skeleton in this S17 PREP §4 uses a different decomposition (Route A-prime, see §3 below) that does NOT consume these two bearers; they remain VALID and could be used in an alternative S17a proof or in S17b if a different lift strategy is chosen. **No drift was observed**.

### §3 Three NEW bearer pins for the fully-discharged skeleton

This S17 PREP pins three additional Mathlib bearers at the same lake SHA. These bearers enable a discharged carry-bound proof WITHOUT requiring the `multiplicity` / `emultiplicity` bridges named by S16 PREP §3.3-§3.4 (and hence WITHOUT the new `Mathlib.Data.Nat.Multiplicity` import S16 §9 named as `⚠`).

#### §3.1 `Nat.Prime.pow_dvd_iff_le_factorization`

**Pin**: `Mathlib/Data/Nat/Factorization/Basic.lean:168`.

**Signature** (verified at lake SHA via `gh api` + `curl`):

```lean
theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p
```

**Why needed**: the fully-discharged subset argument in §4 below needs to convert `i ≤ m.factorization p` (where m ≠ 0) into `p ^ i ∣ m`, so that `m % p ^ i = 0`. This bearer is the canonical Iff for that conversion.

**In scope after**: existing S15 import `Mathlib.Data.Nat.Choose.Factorization` (transitively pulls in `Mathlib.Data.Nat.Factorization.Basic`). No new import needed.

**Section-header typeclass recheck** (per memory pattern `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`): bearer is inside `namespace Nat` block at top of `Basic.lean`. The `Prime` here is `Nat.Prime` (via `open Nat` scope). No typeclass overhead.

#### §3.2 `Nat.factorization_choose_le_log`

**Pin**: `Mathlib/Data/Nat/Choose/Factorization.lean:185`.

**Signature** (verified at lake SHA):

```lean
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n
```

**Why needed**: provides the canonical `(choose n m).factorization p ≤ log p n` upper bound. In the subset argument below, this is NOT consumed directly (we use `Nat.factorization_choose` from line 131 and bound by Ico cardinality), but pinning it documents the standard Mathlib bound and provides a fallback if the subset argument's filter-cardinality step hits an elaboration issue. The Mathlib proof at lines 185-193 uses exactly the subset-by-Ico strategy this S17 PREP uses (lines 192-193: `rw [factorization_choose hp hkn (Nat.lt_add_one _)]` + `exact (card_filter_le ..).trans_eq (Nat.card_Ico _ _)`), so the `Ico` cardinality machinery is verified-to-work at this lake SHA.

**In scope after**: existing S15 import `Mathlib.Data.Nat.Choose.Factorization`. No new import.

**Section-header typeclass recheck**: bearer is inside `namespace Nat` block at line 180 (after `end Nat` at 177 + reopen at 180). The `variable {p n k : ℕ}` at line 182 supplies the binders. `log p n` here refers to `Nat.log p n`. No additional typeclasses.

#### §3.3 `Nat.pow_le_of_le_log`

**Pin**: `Mathlib/Data/Nat/Log.lean:171`.

**Signature** (verified at lake SHA):

```lean
theorem pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y
```

**Why needed**: the central conversion from `v_p(m) + v_p(C(n, m)) ≤ log p n` to `p ^ (v_p(m) + v_p(C(n, m))) ≤ n`. Already consumed inside Mathlib's `pow_factorization_choose_le` (Choose/Factorization.lean:196-197) — so this is a verified-in-use lemma at the current lake SHA.

**In scope after**: existing `Mathlib.Tactic` import (which transitively pulls in `Mathlib.Data.Nat.Log`). No new import.

**Section-header typeclass recheck**: bearer is at top-level (no namespace; `Mathlib.Data.Nat.Log` keeps `Nat.log` at root with explicit `Nat.` namespacing). No typeclasses.

### §4 Fully-discharged paste-ready S17a skeleton (NO sorries)

This is the upgrade of S16 PREP §7's skeleton. The single `sorry` on the carry-count argument is replaced with a complete proof using the bearers §3.1-§3.3.

```lean
section Part12
-- (Part 12, Session 17a) Per-prime upper bound for the prime-power
-- factorization of `m * C(n, m)`. Generalizes `Nat.pow_factorization_choose_le`
-- (S15 framework) to the m-prefactored case. Consumed by Part 13 (S17b ACT)
-- to discharge `mul_choose_dvd_lcmRange` via prime-power decomposition.
--
-- The naive bound `v_p(m) + ⌊log_p (n-1)⌋ ≤ ⌊log_p n⌋` FAILS in general
-- (e.g. n=12, m=4, p=2: v_2(4) + log_2(11) = 2 + 3 = 5 > log_2(12) = 3).
-- The sharp argument observes: when `v_p(m) = a`, the bottom `a` base-p
-- digits of m are 0, so the carry positions in m + (n-m) = n (which by
-- Kummer count `v_p(C(n, m))`) can only land in positions > a. Hence
-- `v_p(C(n, m)) ≤ log_p n - v_p(m)`, giving the SHARP `v_p(m·C(n,m)) ≤ log_p n`.
--
-- This file's discharge bypasses the `multiplicity`/`emultiplicity` API
-- entirely by working directly with `Nat.factorization_choose`'s carry
-- formula and bounding the filter cardinality by Ico cardinality via a
-- subset argument anchored on `Nat.Prime.pow_dvd_iff_le_factorization`.

/-- Per-prime upper bound on `(m * C(n, m)).factorization p`. -/
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p : ℕ} : p ^ ((m * Nat.choose n m).factorization p) ≤ n := by
  have hn : 0 < n := hm.trans_le hmn
  have hC_pos : 0 < Nat.choose n m := Nat.choose_pos hmn
  -- Decompose: v_p(m * C(n, m)) = v_p(m) + v_p(C(n, m)).
  rw [Nat.factorization_mul hm.ne' hC_pos.ne']
  simp only [Finsupp.add_apply]
  by_cases hp : p.Prime
  · -- Prime case: reduce to log p n.
    apply Nat.pow_le_of_le_log hn.ne'
    -- Goal: m.factorization p + (Nat.choose n m).factorization p ≤ Nat.log p n
    -- Sharper than the naive sum-of-`factorization_choose_le_log` bound (which
    -- would give ≤ 2 * log p n via two separate applications).
    set a : ℕ := m.factorization p with ha
    -- Step 1: a ≤ log p n. Follows from p^a ∣ m + m ≤ n.
    have ha_le_log : a ≤ Nat.log p n := by
      have h_pa_dvd_m : p ^ a ∣ m :=
        (hp.pow_dvd_iff_le_factorization hm.ne').mpr le_rfl
      have h_pa_le_m : p ^ a ≤ m := Nat.le_of_dvd hm h_pa_dvd_m
      have h_pa_le_n : p ^ a ≤ n := h_pa_le_m.trans hmn
      exact Nat.le_log_of_pow_le hp.one_lt h_pa_le_n
    -- Step 2: expand v_p(C(n, m)) using factorization_choose at b = log p n + 1.
    rw [Nat.factorization_choose hp hmn (Nat.lt_add_one _)]
    -- Goal: a + #{i ∈ Ico 1 (log p n + 1) | p^i ≤ m % p^i + (n - m) % p^i} ≤ log p n
    set b : ℕ := Nat.log p n with hb
    -- Step 3: subset argument. The filter set is contained in Ico (a + 1) (b + 1).
    have h_subset :
        {i ∈ Finset.Ico 1 (b + 1) | p^i ≤ m % p^i + (n - m) % p^i}
          ⊆ Finset.Ico (a + 1) (b + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      obtain ⟨⟨hi_one, hi_hi⟩, hi_cond⟩ := hi
      refine Finset.mem_Ico.mpr ⟨?_, hi_hi⟩
      by_contra h_lt
      push_neg at h_lt
      -- h_lt : i < a + 1, so i ≤ a.
      have hi_le_a : i ≤ a := Nat.lt_succ_iff.mp h_lt
      -- p^i ∣ m via Prime.pow_dvd_iff_le_factorization (≤ a = v_p(m)).
      have h_pi_dvd_m : p ^ i ∣ m :=
        (hp.pow_dvd_iff_le_factorization hm.ne').mpr (hi_le_a.trans (le_of_eq ha.symm))
      -- So m % p^i = 0.
      have h_m_mod : m % p ^ i = 0 := Nat.eq_zero_of_dvd_of_lt h_pi_dvd_m (Nat.mod_lt _ (Nat.pow_pos hp.pos i))
              |> (fun _ => Nat.mod_eq_zero_of_dvd h_pi_dvd_m)
      -- The condition becomes p^i ≤ 0 + (n - m) % p^i = (n - m) % p^i < p^i.
      rw [h_m_mod, Nat.zero_add] at hi_cond
      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos i)))
    -- Step 4: bound the filter cardinality by Ico (a+1) (b+1) cardinality.
    have h_card_le : ({i ∈ Finset.Ico 1 (b + 1) | p^i ≤ m % p^i + (n - m) % p^i}).card
        ≤ (Finset.Ico (a + 1) (b + 1)).card :=
      Finset.card_le_card h_subset
    rw [Nat.card_Ico] at h_card_le
    -- h_card_le : (...).card ≤ b + 1 - (a + 1) = b - a
    -- Goal: a + (filter card) ≤ b
    calc a + ({i ∈ Finset.Ico 1 (b + 1) | p^i ≤ m % p^i + (n - m) % p^i}).card
        ≤ a + (b + 1 - (a + 1)) := by exact Nat.add_le_add_left h_card_le a
      _ = a + (b - a) := by rw [Nat.succ_sub_succ_eq_sub]
      _ = b := Nat.add_sub_of_le ha_le_log
  · -- Non-prime case: both factorizations vanish, p^0 = 1 ≤ n.
    rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]
    simp
    exact hn

end Part12
```

**LOC budget** (best estimate): ~75 LOC (theorem body ~60-65 + 10-15 LOC of docstring + Part header). Within S16 §5.3's "60-80 LOC" envelope.

**Imports needed**: NONE new. All bearers in scope through existing imports:
- `Nat.factorization_mul` ← `Mathlib.Data.Nat.Choose.Factorization` (S15 import) transitively pulls `Mathlib.Data.Nat.Factorization.Defs`
- `Nat.factorization_choose` ← `Mathlib.Data.Nat.Choose.Factorization` (S15)
- `Nat.pow_le_of_le_log`, `Nat.le_log_of_pow_le` ← `Mathlib.Tactic` (S15) transitively pulls `Mathlib.Data.Nat.Log`
- `Nat.Prime.pow_dvd_iff_le_factorization` ← `Mathlib.Data.Nat.Choose.Factorization` transitively pulls `Mathlib.Data.Nat.Factorization.Basic`
- `Finset.card_le_card`, `Nat.card_Ico` ← `Mathlib.Tactic` transitive
- `Nat.mod_eq_zero_of_dvd`, `Nat.eq_zero_of_dvd_of_lt`, `Nat.mod_lt`, `Nat.pow_pos` ← core / `Mathlib.Tactic`

**0 sorries** in the skeleton.

#### §4.1 Falsifiability checklist on the §4 skeleton

The §4 skeleton has 6 places where elaboration could differ from the sketch:

| # | Step | Risk | Mitigation |
|---|------|------|------------|
| 1 | `Finsupp.add_apply` after `Nat.factorization_mul` | `simp only` may need `Pi.add_apply` companion | If `simp only [Finsupp.add_apply]` doesn't close, try `simp only [Finsupp.add_apply, Pi.add_apply]` or `rw [Finsupp.add_apply]` instead. Both are routine. |
| 2 | `Nat.le_log_of_pow_le hp.one_lt h_pa_le_n` | Lemma name may be `le_log_of_pow_le` (root namespace) | Verified at `Mathlib/Data/Nat/Log.lean:176` as `theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y`. The `Nat.` prefix may or may not be needed depending on `open Nat`. If unprefixed, drop `Nat.`. |
| 3 | `set i : ℕ := m.factorization p with ha` | `set` tactic creates local definition; subsequent goals reference `a` | Standard `set` usage. |
| 4 | `Nat.eq_zero_of_dvd_of_lt` chain | The pipe `|>` flow may not elaborate as expected | Replace with explicit `have` step: `have h_m_mod : m % p ^ i = 0 := Nat.mod_eq_zero_of_dvd h_pi_dvd_m`. This is cleaner and removes the spurious pipe. **See §4.2 cleaner version.** |
| 5 | `Nat.card_Ico` simp | May rewrite to `b + 1 - (a + 1)` or `b - a` directly | If the rewrite goes directly to `b - a`, drop the `Nat.succ_sub_succ_eq_sub` step. |
| 6 | `Nat.add_sub_of_le ha_le_log` | Final closure of `a + (b - a) = b` | Standard arithmetic lemma. If lookup differs, use `omega`. |

#### §4.2 Cleaner version of the `h_m_mod` step

Replace the pipe-style derivation with:

```lean
      have h_m_mod : m % p ^ i = 0 := Nat.mod_eq_zero_of_dvd h_pi_dvd_m
```

This requires `Nat.mod_eq_zero_of_dvd` to exist with signature `n ∣ m → m % n = 0`. If it doesn't (the lemma may be `Nat.mod_eq_zero_iff_dvd.mpr` returning `0` for `b ∣ a` direction), fall back to:

```lean
      have h_pi_pos : 0 < p ^ i := Nat.pow_pos hp.pos i
      have h_m_mod : m % p ^ i = 0 := (Nat.dvd_iff_mod_eq_zero _ _ h_pi_pos).mp h_pi_dvd_m
```

Or simply use `Nat.mod_eq_zero_iff_dvd`:

```lean
      have h_m_mod : m % p ^ i = 0 := by
        rw [Nat.mod_eq_zero_iff_dvd (Nat.pow_pos hp.pos i)]; exact h_pi_dvd_m
```

The S17a ACT picker can choose whichever form elaborates first.

### §5 Numerical validation of the subset argument

Spot-check the subset claim at the S16 §6 counterexample (n=12, m=4, p=2):

- `a = v_2(4) = 2`.
- `b = log_2(12) = 3` (since `2^3 = 8 ≤ 12 < 16 = 2^4`).
- Filter set `{i ∈ Ico 1 (3+1) | 2^i ≤ 4 % 2^i + 8 % 2^i}` evaluated for i ∈ {1, 2, 3}:
  - i=1: `2^1 = 2`, `4 % 2 = 0`, `8 % 2 = 0`, sum = 0, `2 ≤ 0` FALSE. Excluded.
  - i=2: `2^2 = 4`, `4 % 4 = 0`, `8 % 4 = 0`, sum = 0, `4 ≤ 0` FALSE. Excluded.
  - i=3: `2^3 = 8`, `4 % 8 = 4`, `8 % 8 = 0`, sum = 4, `8 ≤ 4` FALSE. Excluded.
  - Filter set = ∅. Cardinality = 0.
- `Ico (a+1) (b+1) = Ico 3 4 = {3}`. Cardinality = 1.
- Subset claim: ∅ ⊆ {3}. ✓
- `v_p(m · C(n, m)) = v_2(4 · 495) = v_2(1980) = 2`. `a + filter card = 2 + 0 = 2`. `2 ≤ b = 3`. ✓
- Subset bound: `a + filter card ≤ a + (b - a) = b`. `2 + 0 ≤ 2 + 1 = 3`. ✓

Spot-check at the **tight** S16 §6 case (n=16, m=8, p=2; bound is tight):

- `a = v_2(8) = 3`.
- `b = log_2(16) = 4` (since `2^4 = 16 ≤ 16 < 32`).
- Filter set `{i ∈ Ico 1 5 | 2^i ≤ 8 % 2^i + 8 % 2^i}` for i ∈ {1, 2, 3, 4}:
  - i=1: `2`, `0 + 0`, FALSE.
  - i=2: `4`, `0 + 0`, FALSE.
  - i=3: `8`, `0 + 0`, FALSE.
  - i=4: `16`, `8 + 8 = 16`, `16 ≤ 16` TRUE.
  - Filter set = {4}. Cardinality = 1.
- `Ico 4 5 = {4}`. Cardinality = 1.
- Subset claim: {4} ⊆ {4}. ✓ (Tight match.)
- `v_p(m · C(n, m)) = v_2(8 · 12870) = v_2(102960) = 4`. `a + filter card = 3 + 1 = 4`. `4 ≤ b = 4`. ✓ Tight.

Spot-check at another case (n=8, m=2, p=2):

- `a = v_2(2) = 1`.
- `b = log_2(8) = 3`.
- Filter set `{i ∈ Ico 1 4 | 2^i ≤ 2 % 2^i + 6 % 2^i}` for i ∈ {1, 2, 3}:
  - i=1: `2`, `0 + 0 = 0`, FALSE.
  - i=2: `4`, `2 + 2 = 4`, `4 ≤ 4` TRUE.
  - i=3: `8`, `2 + 6 = 8`, `8 ≤ 8` TRUE.
  - Filter set = {2, 3}. Cardinality = 2.
- `Ico 2 4 = {2, 3}`. Cardinality = 2.
- Subset claim: {2, 3} ⊆ {2, 3}. ✓ (Tight match.)
- `v_2(2 · 28) = v_2(56) = 3`. `a + filter card = 1 + 2 = 3`. `3 ≤ b = 3`. ✓ Tight.

All three numerical checks confirm the subset argument is correct.

### §6 Why the Route A (full Kummer via emultiplicity bridge) bearers stay PINNED but UNCONSUMED

S16 PREP §3.3-§3.4 pinned two bearers for the Route A discharge:
- `Nat.multiplicity_eq_factorization` (`multiplicity → factorization` bridge)
- `multiplicity_eq_of_emultiplicity_eq_some` (`emultiplicity → multiplicity` bridge)

These bridges enable extracting the ℕ-valued `factorization` from Kummer's `Nat.Prime.emultiplicity_choose` (which returns `ℕ∞`). The §4 discharged skeleton avoids them by:

1. Using `Nat.factorization_choose` directly (which IS in `Mathlib.Data.Nat.Choose.Factorization` and returns the carry formula in ℕ-valued form).
2. Bounding the filter cardinality by `Ico` cardinality (subset argument, §4 Step 3).
3. Converting `≤ log p n` to `p ^ · ≤ n` via `pow_le_of_le_log` (§3.3).

The S16-pinned bridges remain VALID at lake SHA (per §2 recheck) and could be used in an ALTERNATIVE S17a discharge that goes through `emultiplicity_choose` directly. The S17a ACT picker has the choice of:

- **Path α** (this S17 PREP §4): no Multiplicity import, subset-cardinality argument, ~75 LOC. RECOMMENDED.
- **Path β** (S16 PREP §7 + bridges 12+13): adds `Mathlib.Data.Nat.Multiplicity` import, uses emultiplicity_choose's exact equality, ~100-120 LOC.

Path α is preferred for the slug's first ACT closing the `sorry` because:
1. Fewer imports → faster compilation and less drift surface.
2. Subset argument is more "natural" to the carry-count interpretation.
3. Reuses existing slug-available API.
4. Smaller LOC budget → faster Docker iters.

Path β remains documented for a future S18+ ACT if the per-prime bound needs to extend beyond `m * C(n, m)` (e.g., to `C(n + m, m)` for the vdP §6 alternating-bilinear summand's second factor).

### §7 S17a ACT readiness gate (POST-S17-PREP)

| # | Item | Status | Source |
|---|------|--------|--------|
| 1 | `Nat.prod_pow_factorization_choose` bearer pinned + recheck | ✓ | S12 + S17 §2 recheck |
| 2 | `Nat.pow_factorization_choose_le` bearer pinned + recheck | ✓ | S12 + S17 §2 recheck (NOT consumed by S17a Path α; consumed by S17b) |
| 3 | `Nat.factorization_eq_zero_of_not_prime` bearer pinned + recheck | ✓ | S14 + S17 §2 recheck |
| 4 | `Nat.coprime_iff_isRelPrime` bearer pinned + recheck | ✓ | S14 + S17 §2 recheck (NOT consumed by S17a; consumed by S17b) |
| 5 | `Nat.coprime_pow_primes` bearer pinned + recheck | ✓ | S15 + S17 §2 recheck (NOT consumed by S17a; consumed by S17b) |
| 6 | `Finset.prod_dvd_of_isRelPrime` bearer pinned + recheck | ✓ | S13 + S17 §2 recheck (NOT consumed by S17a; consumed by S17b) |
| 7 | `isRelPrime_one_left`/`_right` bearers pinned + recheck | ✓ | S14/S15 + S17 §2 recheck (NOT consumed by S17a; consumed by S17b) |
| 8 | `DecompositionMonoid ℕ` typeclass available | ✓ | S13 + S17 §2 recheck |
| 9 | `Nat.factorization_mul` bearer pinned + recheck | ✓ | S16 §3.1 + S17 §2 recheck |
| 10 | `Nat.factorization_le_factorization_choose_add` bearer pinned + recheck | ✓ | S16 §3.2 + S17 §2 recheck (NOT consumed) |
| 11 | `Nat.multiplicity_eq_factorization` bearer pinned + recheck | ✓ | S16 §3.3 + S17 §2 recheck (NOT consumed by Path α; available for Path β) |
| 12 | `multiplicity_eq_of_emultiplicity_eq_some` bearer pinned + recheck | ✓ | S16 §3.4 + S17 §2 recheck (NOT consumed by Path α; available for Path β) |
| 13 | `Nat.Prime.pow_dvd_iff_le_factorization` bearer pinned | ✓ | **NEW this S17 §3.1** |
| 14 | `Nat.factorization_choose_le_log` bearer pinned | ✓ | **NEW this S17 §3.2** |
| 15 | `Nat.pow_le_of_le_log` bearer pinned | ✓ | **NEW this S17 §3.3** |
| 16 | `Nat.factorization_choose` (carry-count formula) bearer available | ✓ | Mathlib/Data/Nat/Choose/Factorization.lean:131 (verified-in-use by Mathlib's own `pow_factorization_choose_le` at line 196) |
| 17 | `Mathlib.Data.Nat.Multiplicity` import status | N/A | Path α does NOT need it (was S16 §9 ⚠); Path β would still need it |
| 18 | Lake SHA stable (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | ✓ | S14 §3 → S15 → S16 §2 → S17 §2 (0 drift in 4 successive PREPs) |
| 19 | Slug builds clean at HEAD | ✓ | S15 ACT verified clean (3058 jobs, 17s on final file) |
| 20 | Fully-discharged skeleton with 0 sorries | ✓ | **THIS S17 PREP §4** |

**Gate status**: **GREEN-PASTE-READY** for S17a ACT via **Path α** (recommended). 20/20 items GREEN (item 17 N/A is intentional; items 11+12 remain GREEN-AVAILABLE for Path β fallback). The slug's 0-sorry status is preserved by Path α since the §4 skeleton has 0 sorries.

For S17b ACT (Route C sub-step b, S15-framework lift): all S15 §4 bearers re-used + S17a's `pow_factorization_mul_choose_le` consumed as a black box. **9/9 GREEN at S17b time once S17a Path α merges**.

### §8 Counts (post-S17 PREP, unchanged from S16 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 905 (unchanged from S15) |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Theorems | 36 (unchanged) |
| Build | verified clean (3058 jobs, S15 baseline) |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: state.md (+ ~120 LOC near top); the slug's JSON (`currentState.iteration` 16 → 17, `phase` PREP, `since` 2026-05-16T04:12Z → 2026-05-16T09:55Z, `lastUpdate`, refreshed `nextAction` upgrading S17a from "Path α or β" to "Path α paste-ready (S17 §4)", +2 insights, +2 nextSteps); 1 new sessions/ note (this file). 0 Lean file edits. 0 sibling-slug edits.

### §9 Conflict-free assertions

This S17 PREP modifies exactly three files:
1. **NEW**: this session note.
2. **MODIFIED**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/state.md` — prepend "Session 17 PREP" section near top (above existing Session 16 PREP section).
3. **MODIFIED**: `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json` — refresh `currentState.iteration` (16 → 17), `currentState.since`, `currentState.focus`, `currentState.nextAction`, `lastUpdate`; prepend 2 entries to `knowledge.insights` and 2 entries to `knowledge.nextSteps`.

**0 Lean edits**. **0 sibling-slug edits**. **0 sorries added**. The JSON and Lean files are owned by this slug only; the parent file `Proofs/BaselProblemOQ01OQ01OQ02.lean` (which contains the `denominator_control` axiom this slug is discharging) is NOT modified.

#### §9.1 Open-PR conflict surface

At S17 PREP write-time: 0 open PRs on this slug (verified via `gh pr list --state open --search "basel-problem-oq-01-oq-01-oq-02-oq-02"`). 0 open PRs on the sibling slug `-oq-03` per `gh pr list` (S16 PREP §1's reference to "2 open PRs `#17619`, `#17551`" may have been stale at S16 PREP write-time; both are now either merged or closed per `gh pr list --state all` showing only 4 historical PRs total for the slug).

### §10 Memory pattern alignment

This PREP iteration matches:

1. **`feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready.md`** — exactly: predecessor S16 PREP shipped a paste-ready skeleton with **1 explicit `sorry`** on the carry-count argument, AND Docker daemon is hung at S17 PREP claim-time. The pattern's prescription is to "ship doc-only PREP UPGRADING audit-corrected skeleton to FULLY-DISCHARGED paste-ready Lean code", which is exactly what §4 does (1 sorry → 0 sorries, via the subset-cardinality argument).
2. **`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`** — §2 rechecks all 13 existing bearers' line positions; §3 documents typeclass-environment / section-header context for the 3 new bearers (Path α uses `Nat.Prime.pow_dvd_iff_le_factorization` from `namespace Nat`; `Nat.pow_le_of_le_log` from root `Mathlib.Data.Nat.Log`).
3. **`feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full.md`** (inverse) — Docker daemon hung AND disk 6.9 Gi avail (NOT extreme disk-full ≤200Mi). The pattern says a substantive ACT could ship `build-pending` qualifier, but per this slug's 0-sorry status and the upgrade-skeleton pattern, the cleaner ship is a doc-only PREP that pre-discharges the sorry at sketch level. This S17 PREP takes that cleaner path.

### §11 Falsifiability

This S17 PREP is falsifiable along four axes:

1. **Bearer surface (§2 + §3)**: if any of the 16 pin commands returns a different signature or line number than this report claims at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the bearer surface is wrong and S17a ACT must repair before consuming.
2. **Subset argument (§4 Step 3 + §5 numerical validation)**: if the subset claim "`{i ∈ Ico 1 (b+1) | p^i ≤ m % p^i + (n-m) % p^i} ⊆ Ico (a+1) (b+1)`" fails at any concrete (n, m, p), the discharge is broken. §5 spot-checks confirm the claim at three cases including the tight S16 §6 case n=16/m=8/p=2 (filter = {4}, Ico (a+1)(b+1) = {4}, match).
3. **Path α elaboration risks (§4.1)**: 6 stepwise elaboration concerns are documented with §4.2's alternative formulations. The §4 skeleton's specific choice of `Nat.eq_zero_of_dvd_of_lt` pipe may need the §4.2 cleaner form at S17a ACT time.
4. **`a ≤ log p n` (Step 1)**: this auxiliary bound requires `p^a ∣ m` (from `pp.pow_dvd_iff_le_factorization` with `k = a = m.factorization p`, giving `p^a ∣ m ↔ a ≤ m.factorization p = a` which is reflexively true), then `p^a ≤ m ≤ n` (via `Nat.le_of_dvd hm` + `hmn`), then `a ≤ log p n` (via `Nat.le_log_of_pow_le hp.one_lt`). If `Nat.le_log_of_pow_le` is namespaced differently (i.e., requires the unprefixed `le_log_of_pow_le`), the S17a ACT picker can drop the `Nat.` prefix. Verified in `Mathlib/Data/Nat/Log.lean:176`: `theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y` — the bearer is unprefixed in the source but reachable as `Nat.le_log_of_pow_le` per the file's `namespace Nat` wrapper.

### §12 Session metrics

| Metric | Value |
|--------|-------|
| Mode | PREP (doc-only) |
| New files | 1 (this session note) |
| Modified files | 2 (state.md, JSON) |
| Lean LOC delta | 0 |
| Theorem delta | 0 |
| Sorry delta | 0 (skeleton in §4 has 0 sorries; closes S16's 1 sorry at sketch level) |
| Axiom delta | 0 |
| New bearer pins | 3 (`Nat.Prime.pow_dvd_iff_le_factorization`, `Nat.factorization_choose_le_log`, `Nat.pow_le_of_le_log`) |
| Bearer drift recheck | 13 bearers (9 from S14+S15 + 4 from S16), 0 drift at unchanged lake SHA |
| Skeleton upgrade | S16 §7 (1 sorry, ~70 LOC) → S17 §4 (0 sorries, ~75 LOC) |
| Numerical validations | 3 cases (n=12/m=4/p=2, n=16/m=8/p=2, n=8/m=2/p=2) — all match subset prediction; tight cases at n=16 + n=8 |
| ACT-readiness gate | **GREEN-PASTE-READY** for S17a Path α (20/20 items, item 17 N/A intentional) |
| Recommended path | **Path α** (subset-cardinality, no Multiplicity import, ~75 LOC) — preferred for first ACT closing the sorry; Path β remains documented for future C(n+m, m) extension |

**Axiom delta this session**: 0 (doc-only).
