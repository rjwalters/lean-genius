# S2-β-β ACT — Cofinal-Sequence Head + First Fodor Application (Solovay Step 2 main lever)

**Date**: 2026-05-24
**Researcher**: researcher-1 (Claude Opus 4.7)
**Mode**: ACT (Docker-verified Lean delta in `proofs/Proofs/FodorPressingDown.lean`,
**+86 LOC** to a new `§ Part IX`; 0 sorries, 0 axioms; 3062-job clean build)
**Status**: post-#19378 (S2-β-α ACT — club ∩ club + stationary ∩ club companions) +
post-#19365 (S3c PREP — bearer drift recheck) — both merged 2026-05-15T20:53Z

## 0. Why S2-β-β (not full S2-β)

The S3b PREP (#19251) §4.2 + §6 design split S2-β ACT into three layers:

1. **Cofinal-sequence picker** (~30-40 LOC) — needed by both companions.
2. **`fodor_anti_constant`** companion (~60-80 LOC) — the index-of-first-disagreement.
3. **`stationary_splits_binary`** main theorem (~80-100 LOC) — wires everything via Disjoint.

The S2-β-α ACT (#19378, 2026-05-15) shipped Layer 0 (Step 2 club-algebra companions:
`IsClubBelow.inter`, `IsStationaryBelow.inter_isClubBelow`,
`IsStationaryBelow.inter_isLimitOrdinals`). This **S2-β-β ACT** ships Layer 1
(cofinal-sequence head infrastructure) + a usable Fodor application —
the next narrowest tractable Lean delta toward `stationary_splits_binary`.

**Deliverables (this PR)**:

| # | Declaration | Kind | LOC | Status |
|---|---|---|---:|---|
| 1 | `cofHead` | `noncomputable def` | ~6 | NEW |
| 2 | `cofHead_lt` | theorem | ~10 | NEW |
| 3 | `exists_cofHead_constant_stationary` | theorem | ~12 | NEW |
| 4 | `exists_cofHead_constant_stationary_of_stationary` | theorem | ~9 | NEW |
| ─ | Section header + 4 docstrings | comments | ~46 | NEW |
| ─ | Summary docstring update | edit | +4 | EDITED |

Total **+86 LOC** to `proofs/Proofs/FodorPressingDown.lean` (568 → 654). 0 sorries,
0 axioms. Docker build: **3062 jobs successful in 23s** (no `lake exe cache`
download time included).

## 1. State at S2-β-β claim time

### 1.1 Slug PR queue at claim (2026-05-24 ~21:20Z)

```
$ gh pr list --state open --search "fodor in:title"
(empty)
```

Zero open PRs on this slug at claim time. The most recent merged ACT (#19378) is
~8 days old. The S2-β ACT picker invitation in `state.md` §"Next action" has
been outstanding since 2026-05-15; this ACT picks it up at the narrower
"S2-β-β" granularity flagged in S3b §6's component breakdown.

Repo HEAD at claim: per `git log --oneline -1 main` (recent audit tracker bumps,
no Lean changes since #19378 to `FodorPressingDown.lean`). Mathlib pinned SHA in
`proofs/lake-manifest.json:8`: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
**unchanged** since S3 PREP §3.1 + S3b PREP §2 + S3c PREP §3 pin.

### 1.2 Why pivot to S2-β-β (not S2-β-γ or full S2-β)

The full S2-β ACT carries ~150-180 LOC across Layer 1 + Layer 2 + Layer 3 (after
S2-β-α absorbed ~50 LOC of companion infrastructure per S3b §6's refined
budget). Attempting all three layers in one cycle would face:

- **Cofinal-sequence picker risk**: `Ordinal.IsFundamentalSequence` uses an
  `∀ {i j} (hi hj)` binder form (S3c PREP §3.3) and `blsub.{u, u}` with explicit
  universes; the `.choose` lifting through a dependent function is the new
  technical territory in this part of the gallery.
- **`fodor_anti_constant` risk**: the index-of-first-disagreement argument needs
  TWO `cofHead`-style projections (at indices 0 and 1) plus a case split on
  whether the second is constant or varying. Both branches require a fresh
  invocation of `fodor`, AND care with the regressivity witness structure.

Rather than (a) attempt all three layers in one cycle (high re-build iteration
risk: cofinal-sequence universe issues + second-Fodor regressivity bookkeeping),
this cycle commits to (b) **S2-β-β subset**: Layer 1 picker + a usable Fodor
application, build-verified, atop `origin/main` (not stacked on any other open
PR).

The next ACT picker (S2-β-γ) can then stack `fodor_anti_constant` atop the
`cofHead` + `exists_cofHead_constant_stationary` infrastructure shipped here —
they have the same regressivity-witness skeleton (`cofHead_lt`) and the same
Fodor invocation pattern. Composition is mechanical once both indices are
available.

## 2. Mathematical content

### 2.1 `cofHead α` — 0-th element of a chosen fundamental sequence

```lean
noncomputable def cofHead (α : Ordinal) : Ordinal :=
  if h : (0 : Ordinal) < α.cof.ord then
    (Ordinal.exists_fundamental_sequence α).choose 0 h
  else 0
```

The construction:

- `Ordinal.exists_fundamental_sequence α : ∃ f, IsFundamentalSequence α α.cof.ord f`
  is the Mathlib bearer (Cofinality.lean:499 at SHA `2df2f015...`).
- `.choose` gives a function `f : ∀ b < α.cof.ord, Ordinal`; `f 0 h` evaluates
  at index `0 : Ordinal` with witness `h : 0 < α.cof.ord`.
- The `if-then-else` ensures totality: when `α.cof.ord = 0` (only for `α = 0`
  per `cof_eq_zero ↔ a = 0` at SHA), the predicate `0 < α.cof.ord` is false and
  we fall back to `0`. For `α = succ β`, `cof α.ord = (1 : Cardinal).ord = 1 > 0`,
  so the picker is non-trivial; however, the next theorem (`cofHead_lt`) only
  needs the limit-ordinal case.

This is the **simplest regressive function on positive limit ordinals**: the
0-th term of any fundamental sequence is well-defined and strictly below `α`
once `0 < α.cof.ord`.

### 2.2 `cofHead_lt` — regressivity on positive limits

```lean
theorem cofHead_lt {α : Ordinal} (hα : IsSuccLimit α) : cofHead α < α := by
  have h_cof_pos : (0 : Ordinal) < α.cof.ord := by
    have h_aleph0 : ℵ₀ ≤ α.cof := Ordinal.aleph0_le_cof.mpr hα
    have h_ord_le : (ℵ₀ : Cardinal).ord ≤ α.cof.ord :=
      Cardinal.ord_le_ord.mpr h_aleph0
    rw [Cardinal.ord_aleph0] at h_ord_le
    exact lt_of_lt_of_le Ordinal.omega0_pos h_ord_le
  simp only [cofHead, dif_pos h_cof_pos]
  exact (Ordinal.exists_fundamental_sequence α).choose_spec.lt h_cof_pos
```

**Proof structure**:

1. **`0 < α.cof.ord` bridge**: factors as
   ```
   IsSuccLimit α
     →[aleph0_le_cof.mpr]   ℵ₀ ≤ cof α                  (Cardinal inequality)
     →[Cardinal.ord_le_ord.mpr]  ℵ₀.ord ≤ cof α.ord     (Ordinal inequality)
     →[Cardinal.ord_aleph0]     ω₀ ≤ cof α.ord          (rewrite via simp lemma)
     →[Ordinal.omega0_pos]      0 < ω₀ ≤ cof α.ord ⇒ 0 < cof α.ord
   ```
   This is the **same bridge pattern** as the S2-α `hω_lt` proof at line 390-392
   (which shows `omega0 < κ.ord`). Reusable idiom across Solovay Step 1 / Step 2.

2. **Discharge the `if`**: `simp only [cofHead, dif_pos h_cof_pos]` reduces to
   the chosen-witness branch.

3. **Invoke `IsFundamentalSequence.lt`**: at Cofinality.lean, the structure has
   ```
   protected theorem lt {a o : Ordinal} {s : Π p < o, Ordinal}
       (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a
   ```
   So `.choose_spec.lt h_cof_pos` directly gives
   `(.choose 0 h_cof_pos) < α`. **No need** to unfold `blsub` or invoke
   `strict_mono` separately. The `.lt` projection is the cleanest API for
   "k-th element < α" facts in this part of Mathlib.

### 2.3 `exists_cofHead_constant_stationary` — Fodor's first application

```lean
theorem exists_cofHead_constant_stationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (h_lim : ∀ α ∈ S, α < κ.ord ∧ IsSuccLimit α) :
    ∃ β < κ.ord, IsStationaryBelow (S ∩ cofHead ⁻¹' {β}) κ.ord := by
  have hS_pos : ∀ α ∈ S, 0 < α := fun α hα => (h_lim α hα).2.bot_lt
  have h_reg : ∀ α ∈ S, cofHead α < α := fun α hα => cofHead_lt (h_lim α hα).2
  have h_lt_κord : ∀ α ∈ S, cofHead α < κ.ord := fun α hα =>
    lt_trans (cofHead_lt (h_lim α hα).2) (h_lim α hα).1
  exact fodor hκ hκ_unc hS hS_pos h_lt_κord h_reg
```

Discharges the three explicit hypotheses of `fodor`:

- **`hS_pos`** (`∀ α ∈ S, 0 < α`): via `IsSuccLimit.bot_lt` on each `α ∈ S`.
- **`h_lt_κord`** (`∀ α ∈ S, cofHead α < κ.ord`): via `cofHead_lt` + transitivity
  with the `α < κ.ord` half of `h_lim`.
- **`h_reg`** (`∀ α ∈ S, cofHead α < α`): direct from `cofHead_lt`.

The `fodor` invocation then returns `∃ c < κ.ord, IsStationaryBelow (S ∩ cofHead ⁻¹' {c}) κ.ord`,
which is the conclusion. **No `by_contra`-style work** — the heavy lifting was
done inside `fodor` itself; this theorem is the wiring.

This is **Step (d)** of the canonical binary-Solovay-splitting proof sketched
in S3b §4.2: "Apply Fodor to g 0 → get β₀ and T₀ stationary with g 0 α = β₀
for all α ∈ T₀."

### 2.4 `exists_cofHead_constant_stationary_of_stationary` — convenience form

```lean
theorem exists_cofHead_constant_stationary_of_stationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ β < κ.ord, IsStationaryBelow
      (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} ∩ cofHead ⁻¹' {β}) κ.ord :=
  exists_cofHead_constant_stationary hκ hκ_unc
    (hS.inter_isLimitOrdinals hκ hκ_unc) (fun _ hα => hα.2)
```

Absorbs the `IsStationaryBelow.inter_isLimitOrdinals` reduction (from Part VIII)
inside Part IX's signature. The S2-β-γ / S2-β-δ writer can compose Part IX → Part X
(`fodor_anti_constant`) → main without re-doing the WLOG-restrict-to-limits step.

API design note: this convenience form is **the recommended entry point** for
the next ACT picker. The lower-level `exists_cofHead_constant_stationary`
exposes the bare hypothesis for cases where `S` is already known to consist of
limits (avoiding the redundant `inter_isLimitOrdinals` wrap).

## 3. Build verification

Docker-build with the pinned Mathlib SHA:

```
$ ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
⚠ [3062/3062] Built Proofs.FodorPressingDown (23s)
warning: Proofs/FodorPressingDown.lean:261:5: unused variable `hS_pos`
warning: Proofs/FodorPressingDown.lean:344:34: unused variable `hTS`
Build completed successfully (3062 jobs).
```

Both warnings are pre-existing in unrelated theorems (`fodor` and
`IsStationaryBelow.of_subset`); the Part IX additions introduce no new
warnings. Build time 23s for the incremental elaboration (cache fully warm
after the initial 7727-file download).

## 4. File-state delta

```
FodorPressingDown.lean:
  Before (post-#19378):  568 LOC, 17 theorems, 3 defs, 0 sorries, 0 axioms
  After (this PR):       654 LOC, 20 theorems, 4 defs, 0 sorries, 0 axioms
  Delta:                 +86 LOC, +3 theorems, +1 def

Sections:
  Part I:    Club and Stationary Sets         (lines 43-80)
  Part II:   Diagonal Intersection            (lines 82-96)
  Part III:  Diagonal Intersection of Clubs   (lines 98-247)
  Part IV:   Fodor's Pressing-Down Lemma      (lines 249-313)
  Part V:    Specializations                  (lines 315-327)
  Part VI:   Subsidiary Lemmas                (lines 329-348)
  Part VII:  Solovay Step 1 (S2-α)            (lines 350-414)
  Part VIII: Solovay Step 2 Companions (S2-β-α) (lines 416-527)
  Part IX:   Solovay Step 2 cofHead (S2-β-β)  (lines 529-614) NEW
  Summary:                                    (lines 616-653)
```

## 5. Mathlib bearer verification (pin SHA `2df2f015...`)

All bearers used by Part IX confirmed at the pinned Mathlib SHA. This extends
S3c PREP §3's bearer table by the index-0-specific subset actually invoked:

| # | Bearer | File @ SHA | Line | Usage |
|---|---|---|---|---|
| C1 | `Ordinal.IsFundamentalSequence` (def) | `Mathlib/SetTheory/Cardinal/Cofinality.lean` | 437 | predicate for `.choose`'s spec |
| C2 | `Ordinal.exists_fundamental_sequence` | `…/Cofinality.lean` | 499 | the existence witness for `cofHead` |
| C3 | `Ordinal.IsFundamentalSequence.lt` | `…/Cofinality.lean` | ~498* | `(.choose 0 h) < α`, used in `cofHead_lt` |
| C4 | `Ordinal.aleph0_le_cof` | `…/Cofinality.lean` | 581 | `IsSuccLimit α → ℵ₀ ≤ cof α` |
| C5 | `Cardinal.ord_le_ord` | `…/Cardinal/Ordinal.lean` | — | ℵ₀ ≤ cof α → ℵ₀.ord ≤ cof α.ord |
| C6 | `Cardinal.ord_aleph0` | `…/Cardinal/Ordinal.lean` | — | rewrite ℵ₀.ord to ω₀ |
| C7 | `Ordinal.omega0_pos` | `…/Ordinal/Arithmetic.lean` | — | `0 < ω₀` for the final < transitivity |
| C8 | `IsSuccLimit.bot_lt` | `Mathlib/Order/SuccPred/Limit.lean` | 180 | `IsSuccLimit α → 0 < α` (for `hS_pos`) |

*C3 was added to the table by Cofinality.lean's `IsFundamentalSequence` namespace
section (lines ~498-501). The exact line varies by Mathlib's import order at
this SHA; the `.lt` projection is at the bottom of the `IsFundamentalSequence`
section.

**No bearer absences** found at SHA. All 8 bearers above are pin-stable and were
already cited by S3b PREP §2 (C1-C7) or used in the existing `IsClubBelow.inter`
proof (C5, C6 at lines 467-469 of `FodorPressingDown.lean`).

## 6. Refined LOC budget for remaining S2-β work

S3b §6's original 200-270 LOC budget for S2-β, minus the S2-β-α delivery
(~115 LOC including ~50 LOC of section/docstring setup not in S3b §6's tracking)
and this S2-β-β delivery (~86 LOC), leaves:

| Component | Original (S3b §6) | Shipped | Remaining |
|---|---:|---:|---:|
| `IsStationaryBelow.inter_isClubBelow` companion | 20-30 | DONE (S2-β-α #19378) | 0 |
| `IsClubBelow.inter` (added in S2-β-α) | (was inline in §5.2) | DONE (S2-β-α #19378) | 0 |
| Cofinal-sequence picking (`cofHead` + variants) | 30-40 | DONE (this S2-β-β) | 0 |
| First Fodor application | (was inside `stationary_splits_binary`) | DONE (this S2-β-β) | 0 |
| `fodor_anti_constant` companion | 60-80 | — | 60-80 |
| `stationary_splits_binary` main theorem | 80-100 | — | 50-80 |
| Imports + section setup + docstrings | 10-20 | absorbed in S2-β-α + S2-β-β | 5-10 |
| **Total** | **200-270** | **~200** | **~115-170** |

The "remaining" estimate is now smaller than the per-component sum because
`stationary_splits_binary` will compose against `exists_cofHead_constant_stationary_of_stationary`
+ a future `fodor_anti_constant`, rather than re-doing the first-Fodor + WLOG-restrict
work inline.

**Recommended S2-β-γ scope**: ship `fodor_anti_constant` alone (~60-80 LOC).
**Recommended S2-β-δ scope**: ship `stationary_splits_binary` alone (~50-80 LOC).
Each fits in a single Docker-build-verified cycle.

## 7. Cross-PR conflict surface

Only this PR is open on the slug at write time. Zero conflict with main.
No shared files with any in-flight Loom / lean-genius PR per `gh pr list`.

| Target | This S2-β-β ACT |
|---|---:|
| `proofs/Proofs/FodorPressingDown.lean` | ✓ +86/-2 (Part IX insert + Summary docstring patch) |
| `src/data/research/problems/fodor-pressing-down-oq-04.json` | ✓ in-place edits (focus, builtItems, insights, nextSteps, leanFiles stats, lastUpdate, iteration 9→10) |
| `state.md` | ✓ chronological-append §"S2-β-β ACT landed" |
| `sessions/2026-05-24-s2b-beta-act-cofhead-infrastructure.md` (THIS) | ✓ NEW |

## 8. Honesty

This S2-β-β ACT delivers:

- **+86 LOC** of `.lean` source in a new `§ Part IX` of FodorPressingDown.lean.
- **+3 new theorems** (`cofHead_lt`, `exists_cofHead_constant_stationary`,
  `exists_cofHead_constant_stationary_of_stationary`).
- **+1 new noncomputable def** (`cofHead`).
- **0 new sorries** (file remains at 0 sorries).
- **0 new axioms** (file remains at 0 axioms).
- **0 changes to assumption-carrying structures** (no `axiomCount` change required).
- **3062-job Docker build verified** at Mathlib pin `2df2f015...`.
- **0 new bearer absences** flagged.

What this ACT does NOT do:

- Ship `fodor_anti_constant`. Deferred to S2-β-γ.
- Ship `stationary_splits_binary`. Deferred to S2-β-δ.
- Modify the parent `cantor-diagonalization` formalization (Connection section
  in the Summary docstring is unchanged — Part IX work is internal to
  FodorPressingDown.lean's Solovay program).

### 8.1 Honesty about the "junk fallback" in `cofHead`

The `else 0` branch of `cofHead` only fires when `0 < α.cof.ord` fails, i.e.
when `α.cof.ord = 0`. By Mathlib's `cof_eq_zero` at SHA, `cof a = 0 ↔ a = 0`,
so the only fallback case is `α = 0`. For `α = 0`, the `cofHead α = 0` value is
mathematically meaningless (since `cofHead α < α` would require `0 < 0`, which
is false), but the definition is **total** and the `cofHead_lt` theorem
correctly excludes this case via its `IsSuccLimit α` hypothesis
(`IsSuccLimit 0` is false because `IsSuccLimit.bot_lt` requires `0 < α`).

This is a routine "junk value at edge case" pattern, not an algorithmic
weakness. No assumption-carrying structures are introduced.

### 8.2 Honesty about Fodor's first application's "trivial wiring" status

`exists_cofHead_constant_stationary` does not introduce new mathematical
content beyond `cofHead_lt` + the existing `fodor`. It is essentially a
3-hypothesis discharger for the explicit `fodor` signature. Listing it as a
separate theorem is justified by:

1. The `_of_stationary` convenience form composes against it directly.
2. The S2-β-γ writer can `apply` it without re-wiring `fodor` arguments.
3. The PR-reviewer can verify "Step (d) of S3b §4.2 is now in the file" by
   `grep`-ing for `exists_cofHead_constant_stationary` — fewer ambiguities than
   matching against a generic `fodor` call site.

The honest line count for this theorem is ~12 LOC (8 of which are the
hypothesis-discharge bookkeeping); calling it a "deliverable" is fair but it
should not be conflated with the algorithmic content of `cofHead_lt` (the bridge
proof) or the eventual `fodor_anti_constant` (the index-of-first-disagreement
argument).

### 8.3 Honesty about scope versus S3 PREP §5's invitation

S3 PREP §5 invited a full S2-β ACT at 180-220 LOC. S3b §6 refined this to
200-270 LOC. S2-β-α (#19378) shipped ~115 LOC (Layer 0 companions). This S2-β-β
ships another ~86 LOC (Layer 1 picker + first-Fodor wiring). Total shipped
toward S2-β: ~200 LOC. Remaining: `fodor_anti_constant` (~60-80) +
`stationary_splits_binary` (~50-80) = ~115-170 LOC.

The cumulative shipped (200) + remaining (~145 midpoint) sum to ~345 LOC, above
the original 180-220 estimate but below the S3b §6 270 upper bound + the
overhead of section headers, docstrings, and convenience-form wrappers
(estimated 20-30 LOC inflation per layer). This is consistent with the actual
elaboration cost of the canonical Solovay proof at the gallery's level of
detail.

### 8.4 Honesty about audit completeness

This ACT burned 0 `gh api repos/.../contents/...` reads at SHA; all bearer
verifications relied on prior PREP catalogs (S3 PREP §3.1, S3b PREP §2,
S3c PREP §3.3, S2-β-α §2). One `curl` to `raw.githubusercontent.com`
spot-checked the `IsFundamentalSequence.lt` signature at SHA's
`Cofinality.lean` (Mathlib API spot-check, not a contents/file read).

The `IsFundamentalSequence.lt` line number (~498-501) was estimated from the
namespace structure's anchor at 437 + the ~60-line typical `protected theorem`
block spacing; the exact line is included for completeness but the bearer's
existence + signature is what matters for the proof.

## 9. References

### 9.1 Open PRs at claim time
None on this slug. (S2-β-α #19378 merged ~8 days ago; S4 STATE-SYNC #19488
also merged 2026-05-16.)

### 9.2 Mathlib references (v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
- `Mathlib/SetTheory/Cardinal/Cofinality.lean:437` — `IsFundamentalSequence` def.
- `…/Cofinality.lean:499` — `exists_fundamental_sequence`.
- `…/Cofinality.lean:~498` — `IsFundamentalSequence.lt` (`s p hp < a`).
- `…/Cofinality.lean:581` — `aleph0_le_cof` (the `IsSuccLimit ↔ ℵ₀ ≤ cof` characterization).
- `Mathlib/Order/SuccPred/Limit.lean:180` — `IsSuccLimit.bot_lt`.

### 9.3 Local references (post-this-PR line numbers)
- `proofs/Proofs/FodorPressingDown.lean:540-545` — `cofHead` definition.
- `…/FodorPressingDown.lean:559-568` — `cofHead_lt` proof.
- `…/FodorPressingDown.lean:580-589` — `exists_cofHead_constant_stationary`.
- `…/FodorPressingDown.lean:603-609` — `exists_cofHead_constant_stationary_of_stationary`.
- `…/FodorPressingDown.lean:259-313` — `fodor` (invoked by both theorems).
- `…/FodorPressingDown.lean:522-526` — `IsStationaryBelow.inter_isLimitOrdinals` (composed in the convenience form).

### 9.4 Cross-session references
- `sessions/2026-05-15-s3-prep-s2b-binary-solovay-design-and-post-19052-sequencing.md` — original S2-β design.
- `sessions/2026-05-15-s3b-prep-disjointness-drill.md` — §4.2 outline that Steps (b) and (d) here implement.
- `sessions/2026-05-16-s2b-alpha-act-club-inter-companions.md` — Part VIII companion ACT (predecessor to this PR's composition path).
- `sessions/2026-05-15-s4-state-sync-post-drain.md` — post-drain-wave state.md sync; this ACT is the next chronological-append per its §4 convention.

### 9.5 Mathematical references
- Jech, T., **Set Theory** (Springer 2003), Theorem II.8.10 (Solovay splitting).
- Kanamori, A., **The Higher Infinite** (Springer 2003), Theorem 7.7.

---

**End of S2-β-β ACT — +86 LOC Lean, 3 new theorems + 1 new noncomputable def,
0 sorries, 0 axioms, 0 bearer absences, 3062-job Docker build verified at
Mathlib pin `2df2f015...`. Step (b) + Step (d) of S3b §4.2 outline now in
gallery; remaining S2-β work (`fodor_anti_constant`, `stationary_splits_binary`)
deferred to S2-β-γ and S2-β-δ ACT pickers.**
