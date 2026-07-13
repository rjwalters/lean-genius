# S18 — PREP: Mechanic handoff for parent `Proofs.LagrangeFourSquares` v4.26.0 fixes (paste-ready, per-error)

**Date**: 2026-05-16
**Researcher**: researcher-5
**Predecessor merges**:
- S17 BUILD-DIAGNOSTIC #19442 (researcher-1) merged 2026-05-16T04:39:18Z — 9-error catalog + rough fix sketch
- S15 STATE-SYNC #19366 (researcher-3) merged 2026-05-16T03:53:34Z — 3-PR drain wave
**Knowledge tier at claim**: RICH (score 27)
**Outcome**: ✅ doc-only PREP shipped — Mechanic handoff with paste-ready Lean edits per error, bearer-pinned at v4.26.0 SHA

## 1. Why this PREP

S17 BUILD-DIAGNOSTIC produced an excellent diagnostic catalog (9 errors E1–E10 across 5 v4.26.0 API-drift classes at parent file `proofs/Proofs/LagrangeFourSquares.lean` lines 210–365) plus high-level §5 "likely fixes (rough sketch, not verified)". This S18 PREP **upgrades the sketch to paste-ready per-error Lean edits**, so the next Mechanic session can apply them in a single Docker pass without re-deriving each fix from first principles.

This PREP is **doc-only** — no Lean / meta.json / Mathlib lake-manifest edits. The parent fix itself remains Mechanic scope per S17 §6 anti-scope hygiene (5 distinct API-drift classes × 4 sibling slugs at risk → researcher heuristic fixes risk cascading regressions). The Mechanic uses this PREP as a paste manifest.

Host-disk note: `df -h /System/Volumes/Data` = 100% capacity (~7.2 Gi free / 926 Gi); Docker containerd `meta.db` cannot write atomically. This PREP is doc-only and does not need Docker; Mechanic will run the parent rebuild once host-disk recovers.

## 2. Mathlib bearer drift recheck (lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

All bearers below were verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` during this session (2026-05-16T~05:00Z). Lake-pin unchanged since 2026-05-13 v4.26.0 bump.

| # | Lemma | Mathlib path | Signature / role | Status |
|---|---|---|---|---|
| B1 | `Nat.Prime.eq_one_or_self_of_dvd` | `Mathlib/Data/Nat/Prime/Defs.lean:88` | `{p : ℕ} (pp : p.Prime) (m : ℕ) (hm : m ∣ p) : m = 1 ∨ m = p` | ✅ present, Or-branch order = `m = 1 ∨ m = p` (parent's `.symm` is the bug) |
| B2 | `Nat.log` | `Mathlib/Data/Nat/Log.lean:62` | `def log (b n : ℕ) : ℕ` (binary; partial application illegal) | ✅ present, binary arity confirmed |
| B3 | `Nat.Prime.mod_two_eq_one_iff_ne_two` | `Mathlib/Data/Nat/Prime/Basic.lean:108` | `{p : ℕ} (hp : p.Prime) : p % 2 = 1 ↔ p ≠ 2` | ✅ present, direct replacement for `odd_of_ne_two |>.mod_cast` chain |
| B4 | `sq_abs` | `Mathlib/Algebra/Order/Ring/Abs.lean` (used at `Mathlib/NumberTheory/SumFourSquares.lean:41,121,155`) | `∀ a, |a| ^ 2 = a ^ 2` (linear-ordered ring) | ✅ present; Mathlib's own `SumFourSquares` uses `push_cast [sq_abs]` for exactly this pattern |
| B5 | `Int.toNat_natCast` | `Mathlib/Algebra/Order/Group/Int/Sum.lean` (and Lean core `Init.Data.Int.LemmasAux`) | `(n : ℕ) : ((n : ℤ).toNat) = n` | ✅ present |
| B6 | `Nat.Prime.odd_of_ne_two` | `Mathlib/Data/Nat/Prime/Basic.lean:102` | `{p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p` | ✅ present (the `.mod_cast` field on its return value is the bug, not the lemma) |
| B7 | `Finset.sum_pair` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | `(h : a ≠ b) : (∑ x ∈ {a, b}, f x) = f a + f b` | ✅ present, unchanged (parent's `rw [hfilt, Finset.sum_pair h1_ne_p]` is sound; just leaves unsolved `id 1 + id p = 1 + p`) |

**Drift assessment**: 0 bearers absent at lake-pin. All 7 fixes below use only bearers verified present.

## 3. Per-error paste-ready fix table

Each row lists: the parent file line being edited, the diff (with surrounding context for paste safety), the Mathlib bearer used, and a risk class (TRIVIAL / LOW / MEDIUM). The fixes are independent (Mechanic can apply in any order) except E1↔E2 and E3↔E4 are pairs (E2/E4 are cascades).

### E3 (L220) — `Nat.Prime.eq_one_or_self_of_dvd` Or-branch reorder (TRIVIAL)

**Cause**: Mathlib `Nat.Prime.eq_one_or_self_of_dvd` returns `m = 1 ∨ m = p`. Parent's `.symm` flips it to `m = p ∨ m = 1`, but the consuming `rintro (rfl | rfl)` at L221 expects the natural order `(d=1 | d=p)` per the case-branches at L222 (h4_ndvd_1, the d=1 case) and L223 (dvd_refl p, the d=p case).

**Edit** (drop the trailing `.symm`):

```diff
-      exact (hp.eq_one_or_self_of_dvd d hd_dvd).symm
+      exact hp.eq_one_or_self_of_dvd d hd_dvd
```

**Bearer**: B1 (`Nat.Prime.eq_one_or_self_of_dvd`, returns `m = 1 ∨ m = p`).
**Fixes**: E3 directly, E4 (cascade — `p` is back in scope once L220 type-checks).

### E1 + E2 (L210–212) — unsolved goal `id 1 + id p = 1 + p` after `Finset.sum_pair` rewrite (LOW)

**Cause**: `sumDivisorsNot4` uses `.sum id` (line 206). After `rw [hfilt, Finset.sum_pair h1_ne_p]` at L224 the goal reduces to `id 1 + id p = 1 + p`. Pre-v4.26.0 simp/refl auto-discharged via `id` definitional unfolding; post-v4.26.0 the goal is left unsolved. E2 is the cascading omega failure on L212 (`have h1_ne_p : (1 : ℕ) ≠ p := by omega`) which can't see a usable lower bound on `p` from `hp : Nat.Prime p`.

**Edit** (fix E1 by closing the trailing goal; fix E2 by using primality directly instead of omega):

```diff
   have h1_ne_p : (1 : ℕ) ≠ p := by omega
   have h4_ndvd_1 : ¬(4 ∣ 1) := by omega
   have h4_ndvd_p : ¬(4 ∣ p) := by intro ⟨k, hk⟩; omega
```

becomes

```diff
   have h1_ne_p : (1 : ℕ) ≠ p := hp.one_lt.ne'
   have h4_ndvd_1 : ¬(4 ∣ 1) := by decide
   have h4_ndvd_p : ¬(4 ∣ p) := by
     intro ⟨k, hk⟩
     have h2 : p ≥ 2 := hp.two_le
     omega
```

and at the very end of the proof (after the existing L224 `rw`):

```diff
   rw [hfilt, Finset.sum_pair h1_ne_p]
+  rfl
```

**Bearers**: B7 (`Finset.sum_pair`), `Nat.Prime.one_lt` (in `Mathlib/Data/Nat/Prime/Defs.lean`), `Nat.Prime.two_le` (same file).
**Fixes**: E1 directly (`rfl` closes `id 1 + id p = 1 + p`), E2 directly (use `hp.one_lt.ne'`), and the `decide` swap for `¬(4 ∣ 1)` is defensive — omega should still handle this constant goal but v4.26.0 may have tightened its preconditions.

**Alternative**: replace `.sum id` with `.sum fun d => d` in the `sumDivisorsNot4` def at line 206. That sidesteps the `id` unfolding requirement entirely. Less invasive to the proof at L224 but changes a definition that other code may match against. Recommend the L224 `rfl` patch first; only fall back to the def change if `rfl` fails.

### E5 (L292) — `Nat.log` binary arity (LOW)

**Cause**: v4.26.0 `Nat.log` has signature `def log (b n : ℕ) : ℕ` (binary). Parent's `Nat.log k` is a partial application, returning `ℕ → ℕ`. The expression at L292 (Vinogradov's bound axiom statement) needs explicit base.

**Edit** (insert base `2` at both occurrences):

```diff
 axiom vinogradov_waring_bound :
     ∃ C > 0, ∀ k : ℕ, k ≥ 2 →
-      waringBigG k ≤ k * (Nat.log k + C * Nat.log (Nat.log k + 2) + C)
+      waringBigG k ≤ k * (Nat.log 2 k + C * Nat.log 2 (Nat.log 2 k + 2) + C)
```

**Bearer**: B2 (`Nat.log` binary).
**Mathematical note**: Vinogradov's bound is asymptotic so the base is arbitrary (changing base 2 → base e only rescales the constant `C`). Base 2 is the most common Mathlib convention for `Nat.log` (matches `Nat.log_two_le`, `Nat.log_two_lt`, etc.).
**Fixes**: E5 directly.

### E6 (L304) — `Int.natAbs` rewrite shifted to `|·|` form (LOW)

**Cause**: At L303 `zify` normalises `(Int.natAbs x : ℤ)` to `|x|`. So the L304 rewrite `rw [Int.natAbs_sq, Int.natAbs_sq]` (which expects pattern `(Int.natAbs ?a : ℤ) ^ 2`) finds no match. Mathlib's own `SumFourSquares.lean` uses `push_cast [sq_abs]` for this pattern.

**Edit** (replace the rewrite with `simp [sq_abs]` before the existing `push_cast`):

```diff
   refine ⟨((a : ℤ) * c + b * d).natAbs, ((a : ℤ) * d - b * c).natAbs, ?_⟩
   zify
-  rw [Int.natAbs_sq, Int.natAbs_sq]
-  push_cast
+  push_cast [sq_abs]
   ring
```

**Bearer**: B4 (`sq_abs`).
**Fixes**: E6 directly.

### E7 (L321) — `Exists.mod_cast` field removed; use direct `Prime.mod_two_eq_one_iff_ne_two` (LOW)

**Cause**: `Nat.Prime.odd_of_ne_two hp hp_odd` returns `Odd p` (a `Nat`-valued existential), and v4.26.0 dropped the `.mod_cast` projection on `Exists`-valued terms. Parent's `.mod_cast` was trying to convert `Odd p` (ℕ-form `∃ k, p = 2k + 1`) to `p % 2 = 1`.

**Edit** (replace the projection chain with the direct iff):

```diff
-    have hp_odd' : p % 2 = 1 := Nat.Prime.odd_of_ne_two hp hp_odd |>.mod_cast
+    have hp_odd' : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp_odd
```

**Bearer**: B3 (`Nat.Prime.mod_two_eq_one_iff_ne_two`).
**Fixes**: E7 directly. This is cleaner than the original — bypasses the `Odd p` intermediate entirely.

### E8 + E9 (L325–326) — omega mod-4 fails on `a^2 % 4 = 0 ∨ a^2 % 4 = 1` (MEDIUM)

**Cause**: v4.26.0 `omega` no longer reduces `a^2 % 4` to its enumerated residues `{0, 1}`. Need explicit case split on `a % 2`.

**Edit** (replace each `have ha4`/`have hb4` line with the case-split version):

```diff
-    have ha4 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by omega
-    have hb4 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by omega
+    have sq_mod_four : ∀ x : ℕ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
+      intro x
+      rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
+      · left
+        have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
+        rw [this]; omega
+      · right
+        have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
+        rw [this]; omega
+    have ha4 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := sq_mod_four a
+    have hb4 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := sq_mod_four b
```

**Bearer**: `Nat.even_or_odd` (in `Mathlib/Data/Nat/Parity.lean`, gives `Even x ∨ Odd x` ≡ `(∃ k, x = 2k) ∨ (∃ k, x = 2k+1)`). Plus `ring` and `omega` (core tactics).

**Mathematical note**: The proof works by explicit residue enumeration:
- If `x = 2k`: `(2k)^2 = 4k^2`, so `(2k)^2 % 4 = 0`. omega closes via `4 * k^2 % 4 = 0`.
- If `x = 2k+1`: `(2k+1)^2 = 4(k^2+k) + 1`, so `(2k+1)^2 % 4 = 1`. omega closes via `(4 * (k^2+k) + 1) % 4 = 1`.

**Fixes**: E8 + E9 directly. The lemma is extracted as `sq_mod_four` (8 LOC) to share between both call sites and keep the main proof readable.

**Alternative (more concise)**: `have := Nat.sq_mod_four_eq` if a Mathlib lemma already states this. Quick `gh api` search at v4.26.0 SHA finds no exact match — the closest is `ZMod.sq_eq_zero_or_one_mod_four` which is for `ZMod 4` not `ℕ % 4`. Extract our own helper as above.

### E10 (L365) — `simp [LipschitzQuaternion.norm]; omega` fails on `(↑a^2 + … : ℤ).toNat = n` (MEDIUM)

**Cause**: After `simp [LipschitzQuaternion.norm]` the goal is `((↑a : ℤ)^2 + ↑b^2 + ↑c^2 + ↑d^2).toNat = n` with `h : a^2 + b^2 + c^2 + d^2 = n` (all ℕ). omega can't reduce because (a) it doesn't see `^2` as a primitive, (b) the `.toNat` conversion needs `Int.toNat_natCast` to flatten.

**Edit** (explicit cast collapse via `push_cast` + `Int.toNat_natCast`):

```diff
 theorem every_nat_is_quaternion_norm (n : ℕ) :
     ∃ q : LipschitzQuaternion, q.norm = n := by
   obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares n
-  exact ⟨⟨a, b, c, d⟩, by simp [LipschitzQuaternion.norm]; omega⟩
+  refine ⟨⟨a, b, c, d⟩, ?_⟩
+  show ((↑a : ℤ) ^ 2 + (↑b : ℤ) ^ 2 + (↑c : ℤ) ^ 2 + (↑d : ℤ) ^ 2).toNat = n
+  have cast_eq : ((↑a : ℤ) ^ 2 + (↑b : ℤ) ^ 2 + (↑c : ℤ) ^ 2 + (↑d : ℤ) ^ 2)
+               = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℕ) : ℤ) := by push_cast; ring
+  rw [cast_eq, Int.toNat_natCast, h]
```

**Bearer**: B5 (`Int.toNat_natCast`).

**Mathematical note**: The two key steps are (a) prove the cast-distributed integer expression equals the cast of the summed ℕ expression (`push_cast; ring`), and (b) apply `Int.toNat_natCast` to strip the round-trip ℕ→ℤ→ℕ.

**Fixes**: E10 directly.

**Alternative (more concise)**: `exact ⟨⟨a, b, c, d⟩, by unfold LipschitzQuaternion.norm; rw [← h]; push_cast; rfl⟩` — but the rewritten form may not match `.toNat` reduction. The explicit form above is preferred for paste safety.

### Warnings W1–W4 — style only (TRIVIAL, optional)

Mechanic may include these in the same fix-PR for cleanliness, or skip and let a separate lint pass handle:

- W1 (L103:35): drop `sq_abs` from a `simp only [...]` arg list where it's unused.
- W2 (L199:8): rename `n` → `_n` in the `r4` placeholder def.
- W3 (L356:39): rename `q₁` → `_q₁` in `lipschitz_norm_multiplicative`.
- W4 (L356:42): rename `q₂` → `_q₂` in same theorem.

These are non-blocking and do not affect any sibling-slug elaboration.

## 4. Anti-scope hygiene

- ❌ **No Lean edits in this PR**. Parent file `proofs/Proofs/LagrangeFourSquares.lean` is untouched. The fixes above are paste-ready manifests for Mechanic, not edits in this PREP.
- ❌ **No `meta.json` edits** for any slug. Parent slug `lagrange-four-squares-waring-g2` gallery counts will change downstream of any axiom-count shift from Mechanic's fix (none expected based on E1–E10 inspection — all fixes are local to proof bodies or axiom statements; no `axiom` declarations added or removed); but counting/auditing is Mechanic + Auditor scope.
- ❌ **No edits to the four downstream sibling slugs** (`lagrange-four-squares-oq-04`, `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` aristotle companion, `LagrangeFourSquaresWaringG2OQ01Counting.lean`, `LagrangeFourSquaresWaringG2OQ01CountingG4.lean`). They are blocked by the same parent regression; Mechanic's fix unblocks all four simultaneously.
- ❌ **No re-attempt of S17 ACT** (the S16 PREP §3.2 paste-ready recipe). Still blocked on parent; remains exactly as documented in S16 PREP §3.2 and S17 §1 — ready to ship in a 5-minute paste-and-build cycle once parent compiles.
- ❌ **No Docker run**. Host disk at 100% (7.2 Gi free), and this PREP is doc-only by design. Mechanic must verify the fixes with Docker in a separate session once host-disk recovers.

## 5. Risk analysis for Mechanic

Per fix, summarized:

| # | Fix class | Risk | Reasoning |
|---|---|---|---|
| E1+E2 | unsolved-goal + omega cascade | LOW | `rfl` closes a `def`-equality; `hp.one_lt.ne'` and explicit `Nat.Prime.two_le` bindings give omega the bounds it needs. |
| E3 | type-mismatch | TRIVIAL | Single-token deletion (`.symm`). |
| E4 | scope cascade | TRIVIAL | Resolves automatically once E3 type-checks. |
| E5 | API arity | LOW | Insert `2` at two call sites in an axiom statement (no proof obligation changed). |
| E6 | rewrite pattern | LOW | Mathlib's own `SumFourSquares` uses the same `push_cast [sq_abs]` idiom; bearer-verified at SHA. |
| E7 | API removal | LOW | Direct lemma replacement via `mod_two_eq_one_iff_ne_two.mpr` — cleaner than the original chain. |
| E8+E9 | omega failure | MEDIUM | Need to extract an 8-LOC `sq_mod_four` helper. The `ring`-rewrite-then-omega pattern is robust but adds elaboration time. |
| E10 | omega+simp failure | MEDIUM | Need `Int.toNat_natCast` plus explicit cast equality. Mechanic should verify the `show` line matches the post-`simp` goal exactly; if `LipschitzQuaternion.norm` unfolding differs in v4.26.0, may need `unfold` instead of `show`. |

**Aggregate Docker risk**: single full rebuild of `proofs/Proofs/LagrangeFourSquares.lean` is required. Cache-replay forecast: dependents (the 4 sibling slugs) will pick up automatically from the .olean since their files are unchanged. Expected Mechanic build time: ~3–5 minutes (parent file only) + ~30 seconds per dependent file ×4 = ~5–7 minutes total once host-disk recovers.

**Aggregate diff size**: ~25 LOC additions, ~10 LOC deletions across 7 fix sites (E3, E1+E2, E5, E6, E7, E8+E9, E10). Single PR, single commit, single Docker pass.

## 6. ACT-readiness gate (refresh from S17)

| Gate | Status | Notes |
|---|---|---|
| 1. S16 PREP §3.2 recipe mathematically sound | ✅ GREEN | Confirmed in S17 §4. No edits needed once parent compiles. |
| 2. Parent file `LagrangeFourSquares.lean` Docker-green | ❌ RED → 🟡 AMBER (post-S18 paste) | Mechanic action required: apply §3 paste-ready fixes. |
| 3. Bearer drift on parent fixes | ✅ GREEN | 7 bearers verified at lake-pin (§2 table). |
| 4. Host disk recovery for Docker | ❌ RED (INFRASTRUCTURE-ONLY) | 7.2 Gi free / 100%. Wait for cleanup. |
| 5. Sibling slugs ready to ride parent fix | ✅ GREEN | Source files unchanged on origin/main; will rebuild from .olean. |
| 6. S4 ACT 5-minute paste cycle after parent fix | ✅ GREEN | S16 PREP §3.2 recipe is byte-identical to S17's drafted-then-reverted edits. |
| 7. S18 PREP doc-only deliverable shipped | ✅ GREEN (this PR) | Paste-ready manifest for Mechanic. |
| 8. No cross-slug state changes | ✅ GREEN | This PREP touches only this slug's state.md + JSON + sessions/. |

Gate count: 5/8 GREEN, 1/8 AMBER (post-paste parent build), 2/8 RED (INFRASTRUCTURE-ONLY — Docker daemon + host disk).

## 7. JSON / state.md changes (this PR)

| File | Change |
|---|---|
| `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md` | Append new head block §"S18 PREP" (this PREP's deliverables + Mechanic handoff pointer); bump `Iteration` 16 → 17; append iteration-history table row. **B1 blocker entry retained** (parent still red until Mechanic ships fix). |
| `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` | `currentState.iteration: 16 → 17`; `currentState.lastUpdate` refresh to 2026-05-16T~05:00Z; `currentState.focus` rewrite (S17 → S18 PREP narrative); `currentState.nextAction` rewrite (rough sketch → paste-ready manifest pointer); `knowledge.builtItems` +1 entry (S18 paste-ready manifest); `knowledge.insights` +1 entry (paste-ready Mechanic handoff pattern reduces re-derivation cost). `currentState.phase` unchanged (`ACT-BLOCKED`); `currentState.blockers` B1 unchanged. `attemptCounts.total: 16 → 17`. |
| `research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-16-s18-prep-mechanic-handoff-parent-v426-paste-ready-fixes.md` | this memo (new file) |

**No `meta.json` edits**. **No Lean changes**. **No bearer file edits**. **No PR labels on the 4 downstream sibling slugs.**

## 8. Honest-status block

- **Mathematical progress this session**: zero new theorems. Mechanic-handoff manifest is process-class improvement, not mathematics.
- **Build-verification status**: ❌ unchanged from S17 — parent Docker-red. This PREP does not attempt to verify; explicitly deferred to Mechanic.
- **Axiom status**: parent axioms unchanged in source (`hilbert_waring`, `wieferich_nine_cubes`, `waring_general_formula`, `vinogradov_waring_bound`); count remains as-textually-declared. No environment-level audit possible until parent compiles.
- **Open conjecture status**: unchanged from S17. Still BLOCKED on Mechanic parent fix for all 5 queued ACTs (S4/S5/S6/S6b/S7).

## 9. Handoff

**Tag for next agent**: `loom:mechanic` on a PR that applies §3 paste-ready edits to `proofs/Proofs/LagrangeFourSquares.lean`. Recommend Mechanic also include the §3 W1–W4 warning cleanup if convenient (single-PR scope is fine; the warnings are non-blocking and won't lengthen the Docker pass).

**Recommended Mechanic PR title**: `mechanic(lagrange-four-squares): v4.26.0 parent regression fix — E1–E10 per S18 PREP §3 (unblocks 5 queued OQ-01 ACTs + 4 downstream slugs)`

**Recommended Mechanic PR body checklist**:
- [ ] Apply §3 fixes E1–E10 (7 sites, ~25 LOC add / ~10 LOC del).
- [ ] (Optional) Apply §3 warnings W1–W4 cleanup.
- [ ] `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquares` returns 0.
- [ ] `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01Counting` returns 0 (sibling check).
- [ ] `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG4` returns 0 (sibling check).
- [ ] Update `src/data/proofs/lagrange-four-squares/meta.json` line/theorem counts if changed (this PREP's §3 edits should net ~+15 LOC on the parent — verify post-build).

**Recommended next-researcher action (post-Mechanic)**: claim this slug back, ship S4 ACT verbatim from S16 PREP §3.2 — single Docker pass, ~5-minute cycle. All five queued ACTs (S4/S5/S6/S6b/S7) become runnable in parallel by separate researcher cycles.

## 10. Trap data point

This S18 PREP is a new instance of the "researcher upgrades predecessor's rough mechanic-handoff sketch into paste-ready manifest" pattern. Distinguished from the existing memory entries:

- vs `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep`: that's PREP→PREP within the same slug; this is BUILD-DIAGNOSTIC sketch → paste-ready manifest, also same slug but crossing the diagnostic/handoff seam.
- vs `_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready`: that's discharging sorries in an audit-corrected skeleton; this is per-error fix recipes for a Mechanic-scoped parent regression.

Recommendation: add a new memory entry for this pattern (researcher S18 PREP after BUILD-DIAGNOSTIC). Trigger: when claim-random lands on slug whose just-merged BUILD-DIAGNOSTIC catalogued ≥5 errors with §"Recommended Mechanic actions" but the recommendations are sketch-level (not paste-ready), and Docker is infrastructure-blocked (host disk ≥99% / containerd I/O / etc.). Action: ship doc-only PREP that upgrades each error's fix to paste-ready Lean code with bearer pin at lake-SHA, organised by error class, with per-fix risk classification for the Mechanic. Typical LOC ~250-400 in the session memo; ~3 files touched (sessions/ + state.md head + JSON delta). Iteration bumps by 1.

---

**End of S18 PREP memo.** Mechanic-handoff active.
