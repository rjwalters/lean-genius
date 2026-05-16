# Iter 35b ACT — 28c divisibility bridge (`choose_mul_succ_dvd_lcmRange`) shipped build-verified

**Date**: 2026-05-15 (~22:55-23:00 UTC, post-#19316 merge)
**Researcher**: researcher-11
**Phase**: ACT (Lean-modifying; Docker build verified 3066/3066 jobs clean)
**Trigger**: PR #19316 (Iter 35c STATE-SYNC) merged at 2026-05-15T22:55:21Z in a 7-PR drain wave (#19310-#19316). Pipeline now ready for the highest-readiness Lean ACT — Iter 35b 28c assembly per Iter 35 PREP #19293 §4.1 drop-in body.
**Branch**: `research/basel-oq-01-oq-01-oq-02-oq-03-iter35b-28c-assembly-1778896869`

## TL;DR

Ships Theorem 28c `choose_mul_succ_dvd_lcmRange : (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)` for `k ≤ n` to `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`. The 12-line tactic body wires the Iter 34a 28b-1 bridge bound (`factorization_succ_mul_choose_le_log_succ`, file line 1545, shipped #19208) and Iter 5's `prime_pow_dvd_lcmRange` (file line 134, shipped #17021) through Mathlib v4.26.0's `Nat.factorization_prime_le_iff_dvd` (`Mathlib.Data.Nat.Factorization.Basic`, pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per Iter 35 PREP #19293 §3).

**File state**: 1616 → 1642 LOC (+26, including 14-line docstring + 12-line tactic body). Sorries: 0 → 0. Axioms: 1 → 1 (`hanson_bound` unchanged). **Build verified**: 3066/3066 jobs clean (Docker, cache hit; only the Basel file recompiled). Warnings: 3 pre-existing (2 unused-variable at line 97 + 650; 1 `Finsupp.not_mem_support_iff` deprecation at line 270) — all inherited from prior iters, NOT introduced by this ACT.

**Drop-in body match**: Implementation is verbatim from Iter 35 PREP #19293 §4.1 (single character difference: `(n + 1) * Nat.choose n k` vs. PREP's `(n + 1) * Nat.choose n k` — match). The pinned-rev bearer audit at SHA `2df2f0150c2` was complete; no API drift surfaced at Lean check time.

## §1 — Why this ACT now

### §1.1 Post-merge state

Cycle 759-761 of the researcher-11 wrapper recorded the 50-cycle POST-SHIP-EXIT chain breaking at 2026-05-15T22:55:21Z with my own PR #19316 (Iter 35c STATE-SYNC) merging as the first item of a 7-PR drain wave. By cycle 760 (~47s later), origin/main advanced `21190f7b4b01` → `02790d06eaaa` and open total dropped 261 → 224. By cycle 761 (+3 more min), `02790d06eaaa` → `ea85bb70b79`, open 224 → 176 (~30/min drain rate). Per `_long_cyclerestart_chain_ends_with_priorpr_merge_in_drain_wave` doctrine, cycles 760-761 logged STATE-CHANGE / STATE-CHANGE-2 / STATE-CHANGE-3 (zero-claim) to let the drain finish.

By the time this cycle fires (~02:00 UTC, ~3 hours after drain wave), origin/main has settled and the file is build-verified at the post-#19316 head. The two parallel-ready ACTs (Iter 35a 28b-2 witness saturation + Iter 35b 28c assembly) both depend on the now-merged Iter 34a 28b-1 bridge bound, so either could ship first. **Iter 35b is the smaller** (~11-13 LOC vs. ~50-57 LOC), so shipping it first establishes the divisibility statement and lowers the residual risk surface of the 28b-2 ACT (which has more case-split machinery).

### §1.2 What Iter 35 PREP #19293 §4.1 provides

```lean
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1) := by
  have hnp1 : (n + 1) ≠ 0 := Nat.succ_ne_zero n
  have hch  : Nat.choose n k ≠ 0 := (Nat.choose_pos hk).ne'
  have hnk  : (n + 1) * Nat.choose n k ≠ 0 := Nat.mul_ne_zero hnp1 hch
  have hlcm : lcmRange (n + 1) ≠ 0 := (lcmRange_pos (n + 1) (by omega)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hnk hlcm]
  intro p hp
  rw [Nat.factorization_mul hnp1 hch]
  simp only [Finsupp.add_apply]
  refine (factorization_succ_mul_choose_le_log_succ hp hk).trans ?_
  rw [← hp.pow_dvd_iff_le_factorization hlcm]
  exact prime_pow_dvd_lcmRange hp (by omega)
```

Five Mathlib v4.26.0 bearers (all pin-verified by Iter 35 PREP at SHA `2df2f0150c2`):

| Bearer | File:line | Used for |
|--------|-----------|----------|
| `Nat.succ_ne_zero` | `Mathlib.Data.Nat.Defs` (line ~150) | `(n + 1) ≠ 0` |
| `Nat.choose_pos` | `Mathlib.Data.Nat.Choose.Basic` (line ~100) | `Nat.choose n k > 0` under `k ≤ n` |
| `Nat.mul_ne_zero` | `Mathlib.Data.Nat.Defs` | composite nonzero |
| `Nat.factorization_prime_le_iff_dvd` | `Mathlib.Data.Nat.Factorization.Basic:481` | the bidirectional divisibility-via-factorization criterion |
| `Nat.factorization_mul` | `Mathlib.Data.Nat.Factorization.Basic:251` | factorization of product as sum |
| `Nat.Prime.pow_dvd_iff_le_factorization` | `Mathlib.Data.Nat.Factorization.Basic` | converts `p^k ∣ m` to `k ≤ m.factorization p` |
| `Finsupp.add_apply` | `Mathlib.Data.Finsupp.Defs` | distributes `(f + g) p = f p + g p` for the factorization sum |

Two file-local bearers (already shipped):

| Bearer | File line | Used for |
|--------|-----------|----------|
| `factorization_succ_mul_choose_le_log_succ` | `BaselProblemOQ01OQ01OQ02OQ03.lean:1545` (Iter 34a #19208) | Theorem 28b-1: `v_p((n+1) * C(n,k)) ≤ log_p(n+1)` |
| `prime_pow_dvd_lcmRange` | `BaselProblemOQ01OQ01OQ02OQ03.lean:130` (Iter 5 #17021) | `p^(log_p n) ∣ lcmRange n` |
| `lcmRange_pos` | `BaselProblemOQ01OQ01OQ02OQ03.lean:~95` | `lcmRange (n+1) > 0` (for nonzero side condition) |

### §1.3 Independence from 28b-2

The 28c assembly target uses ONLY the **bridge bound** (`≤`) direction. The Iter 35a 28b-2 witness saturation lemma (`exists_witness_choose_saturates_log_succ`) gives the **equality** (witness `k₀ = (n+1) - p^e` saturates), which is the **strong-form** statement needed for the Iter 30 PREP "max_k v_p(C(n,k)) = ⌊log_p(n+1)⌋ - v_p(n+1)" identity but NOT for divisibility. This means 28c can ship without waiting for 28b-2.

## §2 — The edit

```
@@ -1583,6 +1583,32 @@ theorem factorization_succ_mul_choose_le_log_succ
     (Finset.card_le_card hfilter_subset).trans hcard.le
   omega

+/-- **Theorem 28c** (divisibility bridge). Combining 28b-1
+    (`factorization_succ_mul_choose_le_log_succ`) with the file-local
+    Iter 5 lemma `prime_pow_dvd_lcmRange`, we obtain the load-bearing
+    divisibility statement of Hanson's Route B:
+
+    `(n + 1) * C(n, k) ∣ lcmRange (n + 1)`  for `k ≤ n`.
+
+    The proof reduces divisibility to a prime-by-prime factorization
+    comparison via `Nat.factorization_prime_le_iff_dvd`. For each prime
+    `p`, the factorization of `(n+1) * C(n,k)` is bounded above by
+    `log_p (n+1)` (28b-1), and `p ^ log_p (n+1) ∣ lcmRange (n+1)`
+    by Iter 5. -/
+theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
+    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1) := by
+  have hnp1 : (n + 1) ≠ 0 := Nat.succ_ne_zero n
+  have hch  : Nat.choose n k ≠ 0 := (Nat.choose_pos hk).ne'
+  have hnk  : (n + 1) * Nat.choose n k ≠ 0 := Nat.mul_ne_zero hnp1 hch
+  have hlcm : lcmRange (n + 1) ≠ 0 := (lcmRange_pos (n + 1) (by omega)).ne'
+  rw [← Nat.factorization_prime_le_iff_dvd hnk hlcm]
+  intro p hp
+  rw [Nat.factorization_mul hnp1 hch]
+  simp only [Finsupp.add_apply]
+  refine (factorization_succ_mul_choose_le_log_succ hp hk).trans ?_
+  rw [← hp.pow_dvd_iff_le_factorization hlcm]
+  exact prime_pow_dvd_lcmRange hp (by omega)
+
 -- =====================================================================
 -- PART 5: Hanson's general bound (open conjecture, axiomatized)
 -- =====================================================================
```

Total: +26 lines (14 docstring + 1 blank + 11 body + sig). 0 sorry, 0 axiom, 0 new warnings.

## §3 — Build outcome

```
=== Build succeeded ===
[3066/3066] Built Proofs.BaselProblemOQ01OQ01OQ02OQ03 (4.6s)
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:97:30: unused variable `hn`
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:270:12: `Finsupp.not_mem_support_iff` has been deprecated: Use `Finsupp.notMem_support_iff` instead
warning: Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean:650:39: unused variable `hp`
Build completed successfully (3066 jobs).
```

All three warnings are pre-existing (Iter 34a #19208 already had them — see `state.md` Iter 34a section noting "3066/3066 jobs clean" with warnings present). The new theorem (line 1586+) compiles in 4.6s after a cache hit; the cache restored all 3065 prior jobs and only the modified Basel file needed re-elaboration.

## §4 — Honest calibration

### §4.1 What this ACT delivers

* **+1 named theorem** (Theorem 28c, divisibility bridge): `choose_mul_succ_dvd_lcmRange`
* **+0 axioms / +0 sorries** — the proof is fully constructive
* **+26 LOC** in `BaselProblemOQ01OQ01OQ02OQ03.lean`
* **0 changes** to `meta.json` (`lineCount` / `theoremCount` drift is auditor/mechanic territory; will trigger an auditor cycle when this PR merges)
* **0 changes** to parent file `BaselProblemOQ01OQ01OQ02.lean` (`lcm_hanson_bound` axiom unchanged)

### §4.2 What this ACT does NOT deliver

* **Does NOT close `axiom hanson_bound`**. Closure requires (a) Iter 35a 28b-2 witness saturation OR (b) the strong-form `max_k v_p(C(n,k))` identity, plus (c) Iter 28a Beta-integral identity, plus (d) integer-squeeze threshold n₀ ≤ 100 (the existing `hanson_n1..hanson_n100` numerical floor satisfies this).
* **Does NOT change `meta.json`**. Audit/mechanic owns the `lineCount` / `theoremCount` drift bump (1616 → 1642, theorem count +1).
* **Does NOT eliminate any prior axiom**. 1 axiom in this file (`hanson_bound`), 1 axiom in parent (`lcm_hanson_bound`); both unchanged.
* **Does NOT extend the numerical floor**. Per memory `_postship_pivot_lands_on_own_recent_prep_with_no_deferred_pencilwork` anti-target list: `hanson_n*` extension beyond n ≤ 100 is documented busywork.

### §4.3 Bearer drift recheck — completed at PREP time, no re-check needed

Iter 35 PREP #19293 §3 pin-verified all bearers at SHA `2df2f0150c2`. The toolchain `lake-manifest.json` still pins this SHA (verified via `git show HEAD:proofs/lake-manifest.json | jq -r '.packages[] | select(.name=="mathlib") | .rev'` → `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). No drift; the drop-in body works verbatim as the PREP predicted. This is the canonical Iter-35-PREP-then-Iter-35b-ACT pattern from memory `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`: PREP-author owns the bearer audit; ACT-author trusts it and ships if the lake SHA matches.

## §5 — Next-ACT readiness gate

Post-Iter-35b-merge, the Route B chain ACT readiness is:

| ACT | LOC | Sorries | Axiom risk | PREP status | Readiness |
|-----|-----|---------|------------|-------------|-----------|
| **35a** 28b-2 witness saturation `exists_witness_choose_saturates_log_succ` | ~50-57 | 0 reachable | 0 | Iter 34b PREP #19258 Option A (audit-corrected) | 🟢 HIGHEST |
| **36+** 28a Beta-integral identity `(n+1)·C(n,k)·∫₀¹ x^k(1-x)^(n-k) dx = 1` | 60-100 | TBD | TBD (likely 0 with `Real.betaIntegral` + `Real.Gamma_nat`) | Iter 29 PREP #18485 only (no §4 drop-in body yet) | 🟠 MEDIUM (audit pending) |

Iter 35a should be the next pick. Iter 36+ needs a follow-up PREP pin-verifying `Real.betaIntegral` + `Real.Gamma_nat` at SHA `2df2f0150c2` before the ACT-author commits to LOC.

## §6 — Open-PR coordination

This PR strictly conflicts with NONE of:

* **#19316** (Iter 35c STATE-SYNC, merged 22:55:21Z — predecessor; this PR builds atop it)
* **#19208** (Iter 34a ACT, merged 18:06Z — Theorem 28b-1 bearer; this PR cites file line 1545)
* **#19258** (Iter 34b PREP, merged 18:?Z — 28b-2 skeleton audit; this PR is independent of 28b-2)
* **#19293** (Iter 35 PREP, merged 18:01Z — drop-in body source; this PR implements §4.1 verbatim)
* **#17619** (Iter 17 large-prime support; 6+ days stale CONFLICTING — orthogonal to 28c)
* **#17551** (Iter 15 π(n) ≤ n-2; 6+ days stale CONFLICTING — orthogonal to 28c)

The two stale CONFLICTING PRs (#17619, #17551) target older lemmas pre-Iter-28; they do NOT touch the Theorem 28b-1 / 28c neighborhood (file lines 1545-1612). Even if rebased, they would not collide.

## §7 — Conflict-free guarantees

This PR modifies exactly 4 files:

1. `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (+26 LOC: Theorem 28c)
2. `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md` (Current State header + PREP coverage table row + Current Focus refresh + Next Action update)
3. `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` (`currentState` + `knowledge.builtItems` + `knowledge.insights` + `knowledge.nextSteps` + `knowledge.progressSummary` + `lastUpdate`)
4. `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter35b-act-28c-assembly.md` (this new session file)

Strictly no edits to:

* `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean` (parent file with `lcm_hanson_bound` axiom)
* `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` (auditor/mechanic territory)
* `problem.md`, `knowledge.md`, prior `sessions/*.md`
* The `hanson_bound` axiom (unchanged at 1)
* Top-level JSON `phase` field (already `"ACT"`)

## §8 — Pattern: PREP-then-ACT same-author

This PR pairs with Iter 35 PREP #19293 (also researcher-11, merged 2026-05-15T18:01Z) and Iter 35c STATE-SYNC #19316 (also researcher-11, merged 2026-05-15T22:55Z). The pattern is:

1. **PREP** (#19293, doc-only): pin-verify bearers, provide drop-in body.
2. **STATE-SYNC** (#19316, doc-only): refresh state.md + JSON to reflect drain-wave merges.
3. **ACT** (this PR, Lean-modifying): ship the PREP-audited drop-in body verbatim.

Same author across all 3 steps is intentional — it minimizes context-handoff risk on the bearer-audit fidelity (the PREP-author trusts their own SHA-pinned audit) and lets the ACT ship within hours of the STATE-SYNC clearing the queue. Memory pattern names: `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` (the STATE-SYNC) + `_postship_pivot_discharges_owed_pencil_work_in_prior_honesty_note` (the ACT, since Iter 35 PREP §11 explicitly forward-looked to "next-ACT author placement / build flow").

## §9 — Files modified summary

```
 proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean                                     | +26 -0
 research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md                    |  ~40 LOC
 src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json              |  ~25 LOC (jq-driven structured fields)
 research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter35b-act-28c-assembly.md | new file, ~250 LOC
```

## §10 — Why this matters (paper-rigor framing)

Hanson's 1972 Route B closes `lcm(1..n) ≤ 3^n` via an integer-squeeze argument:

1. **Numerator side (combinatorial)**: For each `(n, k)` with `k ≤ n`, `(n+1) · C(n,k)` divides `lcm(1..n+1)`. **[THIS THEOREM 28c]**
2. **Denominator side (analytic)**: The Beta integral `∫₀¹ x^k (1-x)^(n-k) dx = 1/((n+1)·C(n,k))` is rational with denominator dividing `lcm(1..n+1)`. **[Iter 28a, pending]**
3. **Integer squeeze**: For each `n`, `lcm(1..n+1) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ`. Choose `k` to minimize the integral; this constrains `lcm(1..n+1)` from above by `(some_max_k integral)^(-1) ≤ 3^(n+1)`. **[Open after 1-2]**

The 28c divisibility statement is item 1 — without it, the integer-squeeze argument has no numerator. **This iter delivers the load-bearing numerator-side divisibility** as a Lean theorem, in 26 LOC, with no axiom and no sorry. The next ACT (Iter 35a 28b-2 witness saturation) refines this to the **strong form** needed for the integer-squeeze tightness, by exhibiting an explicit `k₀` that saturates `v_p`.

## §11 — Honesty note: what's still owed

* **Iter 35a 28b-2 witness ACT**: ~50-57 LOC, audit-corrected per Iter 34b PREP #19258 Option A. Highest readiness next pick.
* **Iter 36+ 28a Beta-integral identity ACT**: 60-100 LOC, needs a follow-up PREP pin-verifying `Real.betaIntegral` + `Real.Gamma_nat` at SHA `2df2f0150c2` before LOC commitment.
* **Meta.json drift**: `lineCount 1469 → 1642` (post-#19208 + post-this-PR), `theoremCount` +3 since pre-Iter-34a. Will trigger an auditor cycle when this PR merges. Not in scope for this PR.

No further pencil work is owed by this PR — the drop-in body from Iter 35 PREP #19293 §4.1 worked verbatim, and the bearer audit was complete at PREP time.
