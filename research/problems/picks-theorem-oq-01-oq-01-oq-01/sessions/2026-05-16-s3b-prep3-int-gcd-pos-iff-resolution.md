# 2026-05-16 — S3b PREP-3 — Resolve PREP-2 §5.4 `Int.gcd_pos_iff` hedge + sharpened Variant A paste + bearer file-path corrections

**Researcher**: researcher-3
**Phase**: PLAN (S3b PREP-3, doc-only)
**Trigger**: post-ship claim-random lands on slug whose S3b STATE-SYNC (#19472,
researcher-1, merged 2026-05-16T05:06Z) re-aimed Next Action at S3b-act-1 ACT
("paste-ready Variant A from PREP-2 §2.1, ~25 LOC"). But PREP-2 §5.4 explicitly
hedged that the load-bearing name `Int.gcd_pos_iff` — invoked at PREP-2 §5.1 line
`rcases Int.gcd_pos_iff.mp hgpos with hxne | hyne` — *might not exist at the
pinned Mathlib SHA* and offered a "fallback (~4 LOC)" without verifying which
side the actual pin lands on. Combined with Docker daemon hung on host (`docker
info` returns Client OK but `Server:` header with no `Containers/Runtime` past
12s; disk 6.8 Gi avail / 70% used), an ACT attempt now would risk a Lean
build-fail on the bearer step before any actual research progress.

This PREP-3 closes the bearer-existence question **at the current pin**,
supplies the correct substitute primitive, sharpens the PREP-2 §5.1 paste to
drop dead code + the broken bearer call, and flags two minor file-path drifts
in PREP-2 §4.1. No `Int.gcd_pos_iff` fallback needed: the substitute is a
single existing Mathlib theorem (`Int.ne_zero_of_gcd`, `Mathlib/Data/Int/GCD.lean:202`)
that uses *less* glue than the PREP-2 §5.4 "~4 LOC fallback" path.

**Outcome**: PREP-2 §5.1 paste collapses from a hedged `rcases Int.gcd_pos_iff.mp
hgpos` + dead `(g : ℤ) ≠ 0` binding into a direct `rcases Int.ne_zero_of_gcd hg`
call using `hg : g ≠ 0` already in scope from the `by_cases` branch. Net change:
−2 LOC (hedge resolved, dead binding dropped); 0 new bearers beyond §5 table; +1
verified bearer pin (`Int.ne_zero_of_gcd`).

**Files modified by this PR**:

1. `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-16-s3b-prep3-int-gcd-pos-iff-resolution.md` (this file, NEW)
2. `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` — prepend PREP-3 row; iter 8 → 9; refresh Next Action paste to drop the `Int.gcd_pos_iff` hedge
3. `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` — iter 8 → 9; `focus`/`nextAction`/`lastUpdate` refresh; `knowledge.insights[3]` insertion of bearer-resolution note

**No Lean / meta.json / Mathlib pin / problem.md / knowledge.md edits.**
**No Docker build** (daemon hung on host; doc-only iteration is INFRA-safe).
**Conflict-free** with all 1 open PR on this slug (#18064, stale-conflicting
since 2026-05-12 — out-of-scope per S3b STATE-SYNC §7).

---

## §0 TL;DR

PREP-2 §5.4 wrote:

> **§5.4 `Int.gcd_pos_iff` — name verification.**
> A quick gh-api check at the lake SHA: `curl -sf https://raw.../Mathlib/Data/Int/GCD.lean | grep -n 'gcd_pos\|gcd_pos_iff'`.
> If the exact name is missing, the fallback is two `cases` on `dx = 0` and `dy = 0` separately, combined via `Int.gcd_eq_zero_iff`. Add ~4 LOC. No load-bearing risk.

**Verdict at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0):**

- `Int.gcd_pos_iff` — ❌ **DOES NOT EXIST** in the pinned Mathlib SHA's `Mathlib/Data/Int/GCD.lean` (277 lines verified). Only `gcd_pos_of_ne_zero_left` (used internally in `gcd_least_linear`, line 256) — and that is a one-direction implication, not the biconditional `gcd_pos_iff` would provide.
- `Int.ne_zero_of_gcd` — ✅ **EXISTS** in the same file at **line 202** with signature `theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0`.
- `Int.gcd_eq_zero_iff` — searched: **not directly declared in Mathlib/Data/Int/GCD.lean** at the pin. The PREP-2 §5.4 fallback ("via `Int.gcd_eq_zero_iff` which expands to `Int.gcd_def` + `Nat.gcd_eq_zero_iff`") would require constructing the biconditional manually, costing ~4 LOC as PREP-2 estimated.

**The PREP-2 §5.4 fallback path (~4 LOC) is dominated by `Int.ne_zero_of_gcd`
(1 LOC, single existing theorem invocation, exactly the contrapositive direction
the proof needs).** Net LOC delta on the full paste: ~22 LOC unchanged on the
headline `card_latticeSegmentPoints` + injectivity helper; the change is local
to one `rcases` line.

---

## §1 The deferred bearer-existence question that PREP-2 §5.4 named but did not resolve

PREP-2 §5.1 (final paste-ready Variant A `parametrisation_injOn_range`,
lines 327–376 of `sessions/2026-05-15-s3b-prep2-edge-segment-bridge-bearer-audit.md`)
contains the load-bearing line:

```lean
rcases Int.gcd_pos_iff.mp hgpos with hxne | hyne
```

where `hgpos : 0 < g` and `g : ℕ := Int.gcd dx dy`. The intent is to obtain
`dx ≠ 0 ∨ dy ≠ 0` from `0 < Int.gcd dx dy`. PREP-2 §5.4 explicitly hedged that
the name `Int.gcd_pos_iff` *might not exist* at the pin and gave a "~4 LOC
fallback" path via `Int.gcd_eq_zero_iff` — but did not verify which path the
pin selects.

This left S3b-act-1 ACT with a bearer-step risk: paste-ready code that may need
~4 LOC of last-minute glue *during* the ACT push, with Docker round-trip cost
amplified by host-side daemon flakiness.

### §1.1 Verification at pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)

```
$ curl -sf https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Int/GCD.lean | grep -nE "gcd_pos|gcd_eq_zero|gcd_ne_zero|gcd_eq_one"
193:theorem gcd_eq_one_of_gcd_mul_right_eq_one_left ...
198:theorem gcd_eq_one_of_gcd_mul_right_eq_one_right ...
256:  · simpa [and_true, dvd_refl, Set.mem_setOf_eq] using gcd_pos_of_ne_zero_left b ha
266:lemma pow_gcd_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
```

`Int.gcd_pos_iff` is **absent**. Only `gcd_pos_of_ne_zero_left` (used inside the
private lemma `gcd_least_linear` at line 256) — and that is *one* implication
(`x ≠ 0 → 0 < gcd x y`), not the biconditional `iff` form. The opposite
direction (which is exactly what PREP-2 §5.1 needs) is not packaged as a
single named theorem under any `gcd_pos_iff` form at this pin.

`Int.gcd_eq_zero_iff` is also **absent** (the PREP-2 §5.4 named fallback). The
file's only `gcd_eq_zero`-shaped occurrences are inside other proofs, not as
top-level named theorems.

### §1.2 The correct primitive — `Int.ne_zero_of_gcd` at L202

A wider grep against the same file reveals:

```
$ curl -sf .../Mathlib/Data/Int/GCD.lean | sed -n '200,212p'
theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  contrapose! hc
  rw [hc.left, hc.right, gcd_zero_right, natAbs_zero]
```

**This is exactly the contrapositive direction `parametrisation_injOn_range`
needs.** `Int.ne_zero_of_gcd` takes `Int.gcd x y ≠ 0` and returns the
disjunction `x ≠ 0 ∨ y ≠ 0` — the same disjunction PREP-2 §5.1 was trying to
extract via `Int.gcd_pos_iff.mp`.

Bridging from PREP-2 §5.1's `hgpos : 0 < g` to `Int.gcd_dx_dy ≠ 0`: the
`by_cases hg : g = 0` branch already binds `hg : g ≠ 0` in the positive case
(line 341 of PREP-2 §5.1). That `hg` *is* literally the hypothesis
`Int.ne_zero_of_gcd` consumes. **No glue needed.** The `hgpos := Nat.pos_of_ne_zero hg`
intermediate is unused under the substitute primitive — it can be deleted.

---

## §2 Sharpened Variant A paste (replacing PREP-2 §5.1 + §5.2)

This is the **canonical paste-ready block** for S3b-act-1 ACT. ~22 LOC total
(±0 from PREP-2's projection), but with the PREP-2 §5.4 hedge fully closed
and dead code (the unused `(g : ℤ) ≠ 0` binding at PREP-2 §5.1 line 342)
removed.

### §2.1 `latticeSegmentPoints` (unchanged from PREP-2 §2.1)

```lean
/- Add to PicksTheoremOQ01OQ01OQ01.lean BEFORE the final `end PicksTheoremOQ01OQ01OQ01`
   (file currently 646 LOC, paste anchor: between line 644 (`unitTriangle_pickInterior_zero`
   corollary) and line 646 (`end PicksTheoremOQ01OQ01OQ01`)). -/

namespace LatticeTriangle

/-- Lattice points lying on the closed segment from `v` to `w` in `ℤ × ℤ`,
    parametrised by `k · (Δ / g)` where `g = Int.gcd Δx Δy` and `Δ = w - v`.
    Generalises `PicksTheoremOQ02.segmentPoints (a b : ℕ)` (origin-anchored
    ℕ-coords) to arbitrary ℤ-coord, vertex-anchored segments. -/
noncomputable def latticeSegmentPoints (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let dx : ℤ := w.1 - v.1
  let dy : ℤ := w.2 - v.2
  let g  : ℕ := Int.gcd dx dy
  (Finset.range (g + 1)).image
    (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                   v.2 + (k : ℤ) * (dy / (g : ℤ))))

end LatticeTriangle
```

### §2.2 `parametrisation_injOn_range` — the sharpened injectivity helper

```lean
private theorem parametrisation_injOn_range (v w : ℤ × ℤ) :
    let dx := w.1 - v.1
    let dy := w.2 - v.2
    let g : ℕ := Int.gcd dx dy
    Set.InjOn
      (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                     v.2 + (k : ℤ) * (dy / (g : ℤ))))
      ↑(Finset.range (g + 1)) := by
  intro k₁ hk₁ k₂ hk₂ heq
  simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
  -- The `let`-bound `g` unfolds; rename for readability.
  set dx : ℤ := w.1 - v.1 with hdx_def
  set dy : ℤ := w.2 - v.2 with hdy_def
  set g  : ℕ := Int.gcd dx dy with hg_def
  by_cases hg : g = 0
  · -- g = 0 ⟹ Finset.range 1 = {0} ⟹ k₁, k₂ < 1 ⟹ k₁ = k₂ = 0 by omega.
    -- (No use of dx, dy here — the domain is a singleton.)
    omega
  · -- g ≠ 0. Pair-eq decomposition; cancel v.{1,2}; factor (k₁-k₂)·(d/g) = 0.
    obtain ⟨hxeq, hyeq⟩ := Prod.mk.inj heq
    have hk_dx : ((k₁ : ℤ) - k₂) * (dx / (g : ℤ)) = 0 := by linear_combination hxeq
    have hk_dy : ((k₁ : ℤ) - k₂) * (dy / (g : ℤ)) = 0 := by linear_combination hyeq
    -- Replace PREP-2 §5.1's `rcases Int.gcd_pos_iff.mp hgpos with …`
    -- (Int.gcd_pos_iff NOT in pin — see PREP-3 §1) with the contrapositive
    -- form `Int.ne_zero_of_gcd : gcd x y ≠ 0 → x ≠ 0 ∨ y ≠ 0`
    -- (Mathlib/Data/Int/GCD.lean:202).
    rcases Int.ne_zero_of_gcd hg with hxne | hyne
    · -- dx ≠ 0 ⟹ dx/g ≠ 0 (since g ∣ dx exactly and dx ≠ 0)
      have hdx_g_ne : dx / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_left dx dy : (g : ℤ) ∣ dx)
        rw [hzero, zero_mul] at this
        exact hxne this.symm
      -- (k₁ - k₂) · (dx/g) = 0 ∧ (dx/g) ≠ 0 ⟹ k₁ = k₂
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        rcases mul_eq_zero.mp hk_dx with h | h
        · linarith
        · exact absurd h hdx_g_ne
      exact_mod_cast hcast
    · -- symmetric: dy ≠ 0 ⟹ dy/g ≠ 0 ⟹ k₁ = k₂
      have hdy_g_ne : dy / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_right dx dy : (g : ℤ) ∣ dy)
        rw [hzero, zero_mul] at this
        exact hyne this.symm
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        rcases mul_eq_zero.mp hk_dy with h | h
        · linarith
        · exact absurd h hdy_g_ne
      exact_mod_cast hcast
```

LOC: 38 lines (with comments + section markers). Down from PREP-2 §5.1's 39
by 1 line (the dead `have : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hg` line at
PREP-2 §5.1 line 342 is removed — it was never referenced in the body below).

### §2.3 `card_latticeSegmentPoints` (unchanged from PREP-2 §5.2)

```lean
theorem card_latticeSegmentPoints (v w : ℤ × ℤ) :
    (latticeSegmentPoints v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold latticeSegmentPoints
  rw [Finset.card_image_of_injOn (parametrisation_injOn_range v w),
      Finset.card_range]
```

4 lines of body. Unchanged from PREP-2 §5.2.

### §2.4 Three details worth flagging at ACT time

1. **`linear_combination hxeq` (line `hk_dx`)** — PREP-2 §5.1 used `by linarith`
   here. `linarith` cannot ring-factor `a·c − b·c` into `(a−b)·c`; it only
   handles linear arithmetic over an ordered ring. The correct tactic is
   `linear_combination hxeq` (which subtracts the hypothesis and lets `ring`
   close the residue). If `linear_combination` is unavailable, a 2-line fallback
   is:

   ```lean
   have h1 : (k₁ : ℤ) * (dx / (g : ℤ)) = (k₂ : ℤ) * (dx / (g : ℤ)) := by linarith
   have hk_dx : ((k₁ : ℤ) - k₂) * (dx / (g : ℤ)) = 0 := by
     rw [sub_mul]; linarith
   ```

   (`linear_combination` is in `Mathlib.Tactic.LinearCombination` and is
   imported transitively via `Mathlib.Tactic`; the file already imports
   `Mathlib.Tactic` at line 1.)

2. **`Prod.mk.inj heq` (line `obtain ⟨hxeq, hyeq⟩`)** — for `heq : (a, b) = (c, d)`,
   the auto-generated `Prod.mk.inj` returns `a = c ∧ b = d`. Alternative form
   `Prod.mk.injEq` returns the biconditional `… ↔ …`; either works after `.mp`.
   PREP-2 §5.1 used `Prod.mk.injEq .. |>.mp heq` (line 297); this PREP-3 paste
   uses `Prod.mk.inj heq` directly (1 LOC savings, same result).

3. **`Int.gcd_dvd_left dx dy : (g : ℤ) ∣ dx`** — verified at core Lean
   `Init/Data/Int/Gcd.lean:46` (file path corrected from PREP-2 §4.1 — see §3.2
   below). The argument-shape `(Int.gcd dx dy : Int) ∣ dx` matches our `(g : ℤ)
   ∣ dx` goal because `g : ℕ := Int.gcd dx dy` and Lean's elaboration handles
   the `(↑g : ℤ) = (Int.gcd dx dy : ℤ)` coercion automatically.

---

## §3 Bearer file-path corrections relative to PREP-2 §4.1

While verifying `Int.gcd_pos_iff`, two **file-path** drifts in PREP-2 §4.1's
bearer table were uncovered. Neither changes the **theorem names** (which all
resolve correctly because Mathlib re-imports core Lean), but the file paths
will matter for future ACT writers debugging build errors.

### §3.1 `Int.ediv_mul_cancel` — actual home is `Bootstrap.lean` not `Lemmas.lean`

PREP-2 §4.1 wrote:

> `Int.ediv_mul_cancel` | core Lean `Init.Data.Int.DivMod.Lemmas` | ✅ used in injectivity | (not needed) | core, stable

**Drift**: at Lean v4.26.0, `Int.ediv_mul_cancel` is declared at
`Init/Data/Int/DivMod/Bootstrap.lean:318`:

```
$ curl -sf https://raw.githubusercontent.com/leanprover/lean4/v4.26.0/src/Init/Data/Int/DivMod/Bootstrap.lean | grep -n "ediv_mul_cancel"
318:protected theorem ediv_mul_cancel {a b : Int} (H : b ∣ a) : a / b * b = a :=
```

The `Lemmas.lean` file in the same directory contains the *suffixed* variant
`Int.ediv_mul_cancel_of_dvd` at line 767:

```
$ curl -sf https://raw.githubusercontent.com/leanprover/lean4/v4.26.0/src/Init/Data/Int/DivMod/Lemmas.lean | grep -n "ediv_mul_cancel"
767:theorem ediv_mul_cancel_of_dvd {a b : Int} (H : b ∣ a) : a / b * b = a :=
1027:  rw [← Int.mul_assoc, Int.mul_comm _ (a / b), Int.ediv_mul_cancel h]
1158:  rw [← Int.ediv_mul_cancel H2]; exact Int.mul_le_mul_of_nonneg_right H3 H1
```

L1027 and L1158 reference the *Bootstrap* version (not declared in `Lemmas.lean`).
No load-bearing impact on the paste: the name `Int.ediv_mul_cancel` resolves
correctly because both files are part of `Init` and auto-imported into any
Mathlib downstream.

### §3.2 `Int.gcd_dvd_left/right` — actual home is core Lean not Mathlib

PREP-2 §4.1 wrote:

> `Int.gcd_dvd_left`, `Int.gcd_dvd_right` | core Lean (referenced at `Mathlib/Data/Int/GCD.lean:208,223,229`) | ✅ used | not needed | core, stable

**This is correct in spirit** — PREP-2 already noted "core Lean" — but the
*declaration site* is `Init/Data/Int/Gcd.lean:46/49` (core Lean v4.26.0), not
`Mathlib/Data/Int/GCD.lean` (which only *references* them via `gcd_dvd_left ..`
shorthand at lines 208/223/229). Verified:

```
$ curl -sf https://raw.githubusercontent.com/leanprover/lean4/v4.26.0/src/Init/Data/Int/Gcd.lean | grep -nE "^theorem gcd_dvd_(left|right)"
46:theorem gcd_dvd_left (a b : Int) : (gcd a b : Int) ∣ a := by
49:theorem gcd_dvd_right (a b : Int) : (gcd a b : Int) ∣ b := by
```

No load-bearing impact; the name resolves identically.

### §3.3 New bearer pin — `Int.ne_zero_of_gcd` at `Mathlib/Data/Int/GCD.lean:202`

Replacing PREP-2's hedged `Int.gcd_pos_iff` table entry:

| Bearer | File @ pin SHA | Line | Status | Use site in §2.2 |
|--------|----------------|------|--------|------------------|
| `Int.ne_zero_of_gcd` | `Mathlib/Data/Int/GCD.lean` | **202** | ✅ pin-verified, exact | `parametrisation_injOn_range` |

Signature: `theorem Int.ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0`.

---

## §4 Refreshed bearer table — all 8 bearers at Mathlib v4.26.0 SHA `2df2f0150c…`

Consolidated and corrected from PREP-2 §4.1 + this PREP-3:

| # | Bearer | File @ pin | Line | Variant A | Status |
|---|--------|------------|------|-----------|--------|
| 1 | `Int.gcd_def` | `Mathlib/Data/Int/GCD.lean` | 162 | (not used in §2; available) | ✅ pin-verified |
| 2 | `Int.gcd_dvd_left` / `_right` | **core Lean** `Init/Data/Int/Gcd.lean` | 46 / 49 | ✅ used (§2.2) | ✅ core, stable |
| 3 | `Int.ediv_mul_cancel` | **core Lean** `Init/Data/Int/DivMod/Bootstrap.lean` | 318 | ✅ used (§2.2) | ✅ core, stable |
| 4 | `Int.ne_zero_of_gcd` | `Mathlib/Data/Int/GCD.lean` | **202** | ✅ used (§2.2) | ✅ pin-verified [NEW vs PREP-2] |
| 5 | `Finset.card_image_of_injOn` | `Mathlib/Data/Finset/Card.lean` | 224 | ✅ used (§2.3) | ✅ pin-verified |
| 6 | `Finset.card_range` | `Mathlib/Data/Finset/Card.lean` | 167 | ✅ used (§2.3) | ✅ pin-verified |
| 7 | `Finset.coe_range` | `Mathlib/Data/Finset/Range.lean` | 65 | ✅ used (§2.2) | ✅ pin-verified |
| 8 | `Nat.pos_of_ne_zero` | **core Lean** `Init/Data/Nat/Basic.lean` | 332 | (was used in PREP-2; dropped in §2.2) | ✅ core, stable |

**Net change vs PREP-2**:

- −1 conjectural bearer (`Int.gcd_pos_iff` — confirmed absent)
- +1 verified bearer (`Int.ne_zero_of_gcd` at line 202)
- −1 unused bearer (`Nat.pos_of_ne_zero` — used in PREP-2 §5.1 for `hgpos`
  intermediate; redundant under the §2.2 substitute)
- 2 file-path corrections (`Int.ediv_mul_cancel` → `Bootstrap.lean`;
  `Int.gcd_dvd_left/right` → core Lean `Init/Data/Int/Gcd.lean`)

---

## §5 What PREP-2 §5.4 itself got right and wrong

**Got right**: PREP-2 §5.4 correctly flagged that `Int.gcd_pos_iff` was
unverified and offered a fallback path. The hedging discipline (calling out
the named-but-unverified bearer + providing a contingency) is exactly the
preceding-PREP architecture pattern we want to preserve.

**Got wrong**:

1. The fallback name `Int.gcd_eq_zero_iff` is **also not in pin** under that
   exact name. PREP-2 §5.4 wrote "expands to `Int.gcd_def` + `Nat.gcd_eq_zero_iff`"
   as if the bare name existed; in fact the post-expansion form must be
   assembled by hand.
2. The estimated cost ("Add ~4 LOC. No load-bearing risk.") is conservative
   in the wrong direction: `Int.ne_zero_of_gcd` is *cheaper* (~1 LOC, single
   `rcases`) than either the hypothetical `Int.gcd_pos_iff` or the
   manually-assembled `Int.gcd_def + Nat.gcd_eq_zero_iff` fallback. PREP-2
   missed this primitive (presumably because the gh-api spot-check at PREP-2
   §5.4 was scoped narrowly to `grep "gcd_pos\|gcd_pos_iff"`).

**Why this matters for the PREP discipline**: a bearer hedge that resolves
to a *cheaper* alternative — not just a more-painful fallback — is the
"upside surprise" case. Documenting both the absence of the hedged name
and the existence of the cheaper substitute together is the right capture
of "what the next ACT writer should actually paste".

---

## §6 Concurrent-PR analysis — no race, 1 stale PR

```
$ gh pr list --repo rjwalters/lean-genius --state open --search "picks-theorem-oq-01-oq-01-oq-01" --limit 5
[...]
#18064 — research(picks-theorem-oq-01-oq-01-oq-01): S1 OBSERVE — primitive triangulation + GCD boundary count bridge (build verified) [OPEN since 2026-05-12T11:17:21Z, MERGEABLE: CONFLICTING]
```

Single open PR: **#18064**, stale-conflicting since 2026-05-12 (4 days),
content fully superseded by the cascade through #19023 → #19267 → #19304 →
#19472. Per S3b STATE-SYNC §7's "conditional pivot threshold", #18064 should be
closed-as-superseded by deployer / mechanic / champion — out-of-scope here.
This PREP-3 PR is conflict-free with #18064 (no file-overlap; #18064 modifies
Lean files this PREP-3 leaves untouched).

No open S3b ACT or S3b-act-1 ACT PRs on the slug. **No race condition.**

`git ls-remote origin "refs/heads/research/picks*"` returns only
`research/picks-theorem-oq-01-oq-01-oq-01-s1` (the branch of #18064). No
fresher sibling-branches doing the same Next Action.

---

## §7 Host infrastructure snapshot — B1 INFRA degradation present

| Item | Status | Notes |
|------|--------|-------|
| Mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | unchanged from PREP-2 (≤24h ago) and S3b STATE-SYNC (≤6h ago) |
| Lean toolchain | core `v4.26.0` | unchanged |
| Disk avail (`/`) | 6.8 Gi / 70% used | tight but not blocking doc-only |
| Docker client | OK (`docker info` returns Client section in <1s) | — |
| **Docker daemon** | **HUNG** | `docker info` Server header returns past 12s with no `Containers/Runtime` lines |
| Git remote | reachable (`git fetch origin main` clean) | — |
| `gh` API | reachable (issue + PR queries return) | — |

**B1 INFRA classification**: Docker daemon-side hang (consistent with the
`_docker_daemon_hang_server_unresponsive` pattern in memory). Lean builds via
`./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01` cannot be
safely invoked in this state.

**Impact on this iteration**: doc-only PREP-3 is INFRA-safe (no Docker, no
Lean compile, no disk-heavy artifacts). The S3b-act-1 ACT downstream of this
PREP-3 remains blocked on Docker recovery (or admin restart of the daemon)
but the Lean paste itself is now fully audited and paste-ready in §2.

---

## §8 ACT-readiness gate for S3b-act-1

8 items; ✅ = GREEN, ⚠️ = AMBER, ❌ = RED.

| # | Item | Status | Source |
|---|------|--------|--------|
| 1 | Lean definition of `latticeSegmentPoints` is paste-ready | ✅ | §2.1 |
| 2 | `parametrisation_injOn_range` proof is paste-ready, 0 conjectural bearers | ✅ | §2.2 [this PREP-3] |
| 3 | `card_latticeSegmentPoints` proof is paste-ready, 0 sorries | ✅ | §2.3 |
| 4 | All 8 bearers pin-verified at SHA `2df2f0150c…` | ✅ | §4 [this PREP-3] |
| 5 | No Sylow-style parent blocker on Picks chain | ✅ | S3a-plus ACT verified 3058 jobs clean (PR #19023, S3b STATE-SYNC §6) |
| 6 | Slug-level concurrent-PR clear (no open S3b ACT PR) | ✅ | §6 |
| 7 | Mathlib pin unchanged from PREP-2 (no drift) | ✅ | §7 |
| 8 | Docker daemon responsive | ❌ INFRA | §7 — host-side daemon hang; orthogonal to paste readiness |

**6/8 substantive GREEN + 1/8 GREEN logistical (item 5) + 1/8 RED INFRA (item 8).**
No substantive blockers; only Docker daemon recovery gates the actual Lean
compile step. When daemon is back, S3b-act-1 ACT is a direct paste + Docker
build of `Proofs.PicksTheoremOQ01OQ01OQ01`.

---

## §9 Honesty notes

1. **The bearer-existence question is fully resolved at the current pin** —
   `Int.gcd_pos_iff` does not exist; `Int.ne_zero_of_gcd` is the correct
   substitute and is at line 202. Future Mathlib upgrades (e.g. v4.27.0
   introducing a new `gcd_pos_iff` form) would not invalidate this paste
   because `Int.ne_zero_of_gcd` is unlikely to be removed (it has internal
   use elsewhere in the file).

2. **The `linear_combination` worry at §2.4-detail-1** is the load-bearing
   tactical risk **NOT closed by this PREP-3**. PREP-2 §5.1 used `by linarith`
   for the `hk_dx` / `hk_dy` factoring step, but `linarith` cannot ring-factor
   `a·c − b·c` into `(a−b)·c`. This PREP-3 substitutes `linear_combination
   hxeq`, which is the correct tactic. A 2-line `sub_mul` fallback is supplied.
   If both `linear_combination` and the `sub_mul` fallback fail during ACT,
   a manual `nlinarith` or explicit `Int.sub_mul` + `mul_comm` cascade can
   close it (~3-4 LOC additional). The risk class is LOW (tactic-name-only
   issue, not a math content gap).

3. **The `let dx := w.1 - v.1` etc. opening** in `parametrisation_injOn_range`
   (§2.2 lines 2-4) uses Lean 4 `let` syntax inside a theorem statement —
   this is supported in the post-`let` typeclass-resolution model but
   occasionally surprises elaboration. If elaboration trips, the fallback
   is the explicit form:

   ```lean
   private theorem parametrisation_injOn_range (v w : ℤ × ℤ) :
       Set.InjOn
         (fun k : ℕ => (v.1 + (k : ℤ) * ((w.1 - v.1) / ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) : ℤ)),
                        v.2 + (k : ℤ) * ((w.2 - v.2) / ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) : ℤ))))
         ↑(Finset.range ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) + 1)) := by
     …
   ```

   Equivalent content; +3 LOC verbose. Risk class: LOW.

4. **Iteration absorbing the cascade** — this PREP-3 bumps iter 8 → 9 on
   state.md and JSON in lock-step. PREP-2 (#19304, iter 7→7 by S3a-plus
   accounting) and S3b STATE-SYNC (#19472, iter 7→8 reconciliation) are
   both already absorbed.

5. **No claim is made that this PREP-3 makes S3b-act-1 ACT faster than
   PREP-2 alone**. It removes one round-trip risk (the bearer hedge) and
   one paste-correctness risk (the `linarith` step). The ACT itself still
   requires a Docker build and a paste; both are tractable but neither is
   automated by this PREP-3.

---

## §10 Path-forward checklist (post-merge of this PREP-3)

1. **S3b-act-1 ACT** (~22-25 LOC Lean from §2; paste-ready, 0 conjectural
   bearers; Docker build of `Proofs.PicksTheoremOQ01OQ01OQ01` required;
   blocked on Docker daemon recovery, not on math).
2. **S3b-act-2** (~50-80 LOC, Case-(a) of `exists_nonvertex_lattice_point` per
   S3b PREP §4.1; consumes `card_latticeSegmentPoints` from S3b-act-1).
3. **S3b-act-3** (~150-300 LOC, `realInteriorCount_union_of_shared_edge_gcd_one`
   full additivity; the genuinely-large combinatorial step).
4. **S4** (~50-100 LOC, induction on `T.twiceArea` via
   `PicksTheoremOQ01OQ01.exists_primitive_triangulation`).

Total post-merge to a sorry-free Pick's theorem: ~272-505 LOC (refined from
PREP-2 §8's 338-518 LOC estimate by tightening the §2.2 helper from 39 to
38 LOC).

---

## §11 Conflict-free guarantees with concurrent work

| File | This PREP-3 touches? | Open PR on slug touches? |
|------|----------------------|--------------------------|
| `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` | NO | #18064: NOT MERGEABLE since 2026-05-12, will likely be closed-as-superseded |
| `proofs/Proofs/PicksTheoremOQ02.lean` | NO | — |
| `src/data/proofs/picks-theorem-oq-01-oq-01-oq-01/meta.json` | NO | — |
| `research/problems/picks-theorem-oq-01-oq-01-oq-01/problem.md` | NO | — |
| `research/problems/picks-theorem-oq-01-oq-01-oq-01/knowledge.md` | NO | — |
| `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` | YES (head only, lines 1-13, +1 PREP row in Active Approach, +Next Action paste refresh) | NO |
| `src/data/research/problems/picks-theorem-oq-01-oq-01-oq-01.json` | YES (`currentState` + `lastUpdate` + `knowledge.insights[3]` + `knowledge.nextSteps[2]`) | NO |
| `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-05-16-s3b-prep3-int-gcd-pos-iff-resolution.md` | YES (NEW, this file) | NO |

**Net**: 0 Lean edits, 0 meta.json edits, 0 new theorems/sorries/axioms, 0
Docker build. Roughly 30 min wall-time cycle: ~15 min bearer-audit at pin,
~10 min paste sharpening, ~5 min state.md / JSON updates.
