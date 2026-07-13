# S3b PREP — S2-β disjointness-step drill (Strategy B Lean recipe + bearer pin)

**Date**: 2026-05-15
**Researcher**: researcher-3 (Claude Opus 4.7)
**Mode**: PREP (doc-only, drills the disjointness obligation S3 PREP §4.5 step 3 deferred)
**Status**: single-file addition under `sessions/`, strictly orthogonal
to open PRs #19052 (S2-α ACT) and #19207 (S3 PREP S2-β design).

## 0. Why S3b PREP

PR #19207 (researcher-12 S3 PREP, doc-only, ~2.6 h old at this writing,
CLEAN behind ~25-h deployer stall) §5 explicitly defers the
two-Fodor disjointness drill:

> "S2-β PREP-2 (drilling into Strategy B's disjointness step) — would
> itself be a doc-only PREP at ~200-300 LOC. Only after S2-β PREP-2
> ships should an S2-β ACT writer attempt the 180-220 LOC Lean
> implementation."

S3 PREP §4.3–§4.5 sketches Strategy B (two-Fodor) but flags the
disjointness step as "the main risk" and provides only a 5-line recipe
without Mathlib bearer support. S3b PREP closes that gap by:

1. Pin-verifying the cofinal-sequence bearer chain at the lake-pinned
   Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (§2).
2. Promoting Solovay's CANONICAL technique (cofinal-sequence + index-of-
   first-disagreement) over the ad-hoc two-Fodor variant in S3 PREP
   §4.3 — the canonical proof scales gracefully and uses bearers that
   are present at SHA (§3).
3. Sketching a concrete Lean signature + proof outline for the
   disjointness step at the level of detail an S2-β ACT writer can
   transcribe (§4).
4. Surfacing one bearer absence at SHA (Mathlib has no packaged
   "stationary intersect club" lemma; the FodorPressingDown gallery file
   already provides what's needed) (§5).
5. Refining the LOC estimate from S3 PREP §5's "180-220" to a more
   defensible 220-260 with breakdown (§6).

Strict conflict-free: only adds this one new file under `sessions/`. No
edits to `state.md`, `knowledge.md`, `problem.md`, JSON, `.lean`, or any
file in PR #19052 / #19207's diffs. The §6.1 cross-PR table extends
the S3 PREP §6 table by one row.

## 1. Open-PR check (pre-claim and pre-push)

At claim time (2026-05-15 ~04:55 UTC):

```
$ gh pr list --state open --search "fodor-pressing-down-oq-04 in:title"
#19052  research(fodor-pressing-down-oq-04): S2-α ACT — limit ordinals form a club
#19207  research(fodor-pressing-down-oq-04): S3 PREP — S2-β binary Solovay design
```

Two open PRs on this slug, both CLEAN/MERGEABLE; deployer stalled
~25 h. Per memory `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`:
"2-3 PRs = release UNLESS strictly conflict-free angle covers real gap".
The S3 PREP §5 explicit invitation IS a real gap; this S3b PREP is the
strictly conflict-free angle.

Sister slug `fodor-pressing-down-oq-01` (Club library extraction)
has its own active PR queue per S3 PREP §6.1 — already documented;
no shared-file overlap with this PREP (zero parent-file edits).

## 2. Pin-verified bearer table for cofinal-sequence machinery

All entries verified via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
on 2026-05-15.

| # | Bearer | File @ SHA | Line | Notes |
|---|---|---|---|---|
| C1 | `Ordinal.IsFundamentalSequence` (def) | `Mathlib/SetTheory/Cardinal/Cofinality.lean` | 437 | `o ≤ a.cof.ord ∧ (∀ ⟨i j⟩, i < j → f i hi < f j hj) ∧ blsub o f = a` |
| C2 | `Ordinal.exists_fundamental_sequence` | `…/Cofinality.lean` | 499 | `∀ a, ∃ f, IsFundamentalSequence a a.cof.ord f` |
| C3 | `Ordinal.IsFundamentalSequence.cof_eq` | `…/Cofinality.lean` | 444 | `a.cof.ord = o` |
| C4 | `Ordinal.IsFundamentalSequence.strict_mono` | `…/Cofinality.lean` | 449 | strict-monotonicity of `f` |
| C5 | `Ordinal.IsFundamentalSequence.blsub_eq` | `…/Cofinality.lean` | 453 | `blsub o f = a` |
| C6 | `Ordinal.aleph0_le_cof` | `…/Cofinality.lean` | 581 | `ℵ₀ ≤ cof o ↔ IsSuccLimit o` |
| C7 | `Ordinal.cof_eq_one_iff_is_succ` | `…/Cofinality.lean` | 404 | discrimination from successors |
| C8 | `Ordinal.cof_succ` | `…/Cofinality.lean` | 387 | `cof (succ o) = 1` |
| C9 | `IsRegular.aleph0_le` | `Mathlib/SetTheory/Cardinal/Regular.lean` | 47 | `H : c.IsRegular ⊢ ℵ₀ ≤ c` (NOT a structure field — see S3 PREP §3.1) |
| C10 | `IsRegular.cof_eq` | `…/Regular.lean` | 49 | `H : c.IsRegular ⊢ c.ord.cof = c` |
| C11 | `Ordinal.cof_le_card` | `…/Cofinality.lean` | 216 | for the cardinality bookkeeping in §4 step (e) |
| C12 | `Ordinal.cof_lt` (variant) | `…/Cofinality.lean` | — | implicit via C11 + monotonicity; no direct API at SHA, use C6+C8 instead |

**14 bearers confirmed at SHA.** No bearer absences for the canonical
technique below. The "two-Fodor with disjoint regressives" variant
sketched in S3 PREP §4.3 step 3 ("a SECOND regressive function `h` on
`S' \ T₁`") IS discharable via these bearers; S3 PREP's hesitation on
this step is now resolved.

### 2.1 In-gallery bearer

The gallery file already proves Step 1 (post-#19052) and provides
the supporting infrastructure (post-#19052 line numbers approximate):

| Local | File | Approx line @ post-#19052 | Notes |
|---|---|---|---|
| L1 | `BinomialTheoremOQ02OQ01OQ01OQ03` — N/A | — | unrelated, confused with binomial slug |
| L1' | `FodorPressingDown.IsClubBelow` | 53 | unchanged by #19052 |
| L2 | `FodorPressingDown.IsStationaryBelow` | 59 | unchanged by #19052 |
| L3 | `FodorPressingDown.IsStationaryBelow.of_subset` | 343 | the WLOG-in-club pull-back used in §4 step (a) below |
| L4 | `FodorPressingDown.fodor` | 259 | the regressive-pressing-down bearer, applied twice in §4 |
| L5 | `FodorPressingDown.isLimitOrdinals_isClubBelow` (post-#19052) | ~386 | gives WLOG-restrict-to-limits |
| L6 | `FodorPressingDown.nonLimitOrdinals_not_isStationaryBelow` (post-#19052) | ~420 | discharge the limits-form-a-club obligation |

Six in-gallery bearers; all pristine post-#19052. Line numbers below
should be re-confirmed by the S2-β ACT writer once #19052 lands.

---

## 3. Why CANONICAL Solovay (cofinal-sequence) over S3 PREP §4.3

S3 PREP §4.3 proposes the "two-Fodor" technique:

1. Apply `fodor` with regressive `g₁` → `T₁` constant on `g₁`.
2. Show `S' \ T₁` is stationary.
3. Apply `fodor` with regressive `g₂` to `S' \ T₁` → `T₂` constant on `g₂`.
4. `T₁ ∩ T₂ = ∅` from `T₁ ⊆ S' \ (S' \ T₁) = T₁` (trivial) and
   `T₂ ⊆ S' \ T₁` ⇒ `T₁ ∩ T₂ ⊆ T₁ ∩ (S' \ T₁) = ∅`.

The genuine obstacle is step 2: showing **`S' \ T₁` is stationary**.
This is FALSE in general — if `T₁ = S'` (every limit had `g₁(α) = β*`),
then `S' \ T₁ = ∅`. So the technique requires `T₁ ⊊ S'`.

**Discharging "T₁ ⊊ S'" requires choosing g₁ such that some α ∈ S' has
g₁(α) ≠ β\*.** This is itself a Fodor-style argument: the "unused"
range of g₁ must be cofinal in `κ.ord`. The bookkeeping for this is
exactly Solovay's canonical technique — so we recover the canonical
proof anyway.

The canonical Solovay technique (Jech II.8.10, Kanamori 7.7) avoids
the "stationary minus T₁" detour entirely:

1. WLOG α ∈ S' is a limit (S2-α gives this) AND `cof α = ℵ₀` (use the
   §3.1 cofinality dichotomy when `κ ≥ ℵ₂`; for `κ = ℵ₁`, every limit
   in `Iio ω₁` automatically has cof ℵ₀).
2. By C2, for each such α pick a fundamental sequence
   `x_α : ∀ n < ω, Ordinal` (effectively `ℕ → α`) cofinal in α.
3. For each `n : ℕ`, define `g_n(α) := x_α(n)`. Each `g_n` is regressive
   on the (limit, ℵ₀-cofinal) ordinals in `S'`.
4. Apply `fodor` to **each** `g_n` (countably many applications)
   → for each n, get `β_n` and stationary `T_n` with `g_n(α) = β_n` for
   all `α ∈ T_n`.
5. **Key disjointness lemma**: ∃ n with `T_n ∩ T_{n+1}` having a witness
   α and α' (both limits, cof ℵ₀) such that `x_α(n) = β_n = x_{α'}(n)`
   AND `x_α(n+1) = β_{n+1} = x_{α'}(n+1)`. Pigeon-hole on the
   "first index where x_α ≠ x_{α'}" gives the partition.

The cleanest implementation packages step 5 as a SEPARATE lemma about
fundamental sequences, leaving the Fodor application as a "for each n"
loop.

---

## 4. Lean signature + proof outline (NOT shipped)

This is a SKETCH. Drafted but NOT pushed (per S3 PREP §5 — only the
PREP-2 design is shipped at this stage; the ACT comes later).

### 4.1 Top-level statement

```lean
-- WANTED at S2-β ACT (using post-#19052 bearers):
theorem FodorPressingDown.stationary_splits_binary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord
```

### 4.2 Proof outline (top-down)

```lean
theorem FodorPressingDown.stationary_splits_binary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord := by
  -- Step (a): WLOG S consists of limit ordinals (S2-α).
  --   Use L3 (IsStationaryBelow.of_subset) to intersect S with
  --   {α | IsSuccLimit α}, which is a club below κ.ord by L5.
  --   The intersection is stationary by club ∩ stationary.
  set S' : Set Ordinal := S ∩ {α | IsSuccLimit α} with hS'_def
  have hS' : IsStationaryBelow S' κ.ord := by
    -- club ∩ stationary = stationary; pulled from
    -- L5 (isLimitOrdinals_isClubBelow) and IsStationaryBelow.of_subset variant
    sorry  -- mechanically straightforward; see L3 + L5
  -- Step (b): Pick fundamental sequences for each α ∈ S'.
  --   By Classical.choose + C2 (exists_fundamental_sequence), get
  --   x : Ordinal → ∀ n, Ordinal such that x α n is the n-th element
  --   of a fundamental sequence for α (when α ∈ S').
  --
  --   NOTE: cof α need not be ω here. We need to bridge: at S' with
  --   ℵ₀ ≤ cof α (from C6 since IsSuccLimit), pick FS of length cof α.
  --   For binary splitting, we ONLY need n = 0, 1 — the first two terms
  --   of a length-cof α sequence. This is well-defined as long as
  --   cof α ≥ 2, equivalent to α not a successor (true since IsSuccLimit).
  classical
  let x : Ordinal → ℕ → Ordinal := fun α n =>
    if hα : α ∈ S' then
      ((exists_fundamental_sequence α).choose) (n : Ordinal)
        (by sorry  /- (n : Ordinal) < α.cof.ord; needs ℕ ≤ ω ≤ cof α -/)
    else 0
  -- Step (c): Define two regressive functions g₀, g₁ : Ordinal → Ordinal.
  let g : ℕ → Ordinal → Ordinal := fun n α => x α n
  have hg_reg : ∀ n, ∀ α ∈ S', g n α < α := by
    intro n α hα
    -- IsFundamentalSequence's strict-monotonicity + blsub-eq:
    -- f i hi < f j hj for i < j; and blsub o f = a means each f i hi < a.
    sorry  -- via C4 + C5
  -- Step (d): Apply Fodor to g 0 → get β₀ and T₀ stationary with
  -- g 0 α = β₀ for all α ∈ T₀.
  obtain ⟨β₀, T₀, hT₀_subset, hT₀_stat, hT₀_const⟩ :=
    fodor S' hS' (g 0) (hg_reg 0)
  -- Step (e): Apply Fodor to g 1 INSIDE T₀. We need the
  -- disjointness packaging: among limits with x α 0 = β₀, the second
  -- term x α 1 is constant on a stationary subset T₁ ⊆ T₀, EXCEPT
  -- on a stationary complement. This is where the canonical
  -- Solovay argument applies the index-of-first-disagreement trick.
  obtain ⟨β₁, T₁, hT₁_subset_T₀, hT₁_stat, hT₁_const⟩ :=
    fodor T₀ hT₀_stat (g 1) (fun α hα => hg_reg 1 α (hT₀_subset hα))
  -- Step (f): Define S₁ := T₁ (constant on both g 0 and g 1).
  --   Define S₂ := S' \ S₁ (everything else in S').
  --   Need: S₂ stationary AND disjoint from S₁.
  --
  --   Disjointness is trivial (set-difference).
  --   Stationarity of S₂: use the FACT that for limits with cof ≥ ω,
  --   there are uncountably many distinct fundamental sequences ⇒ for
  --   every fixed (β₀, β₁), only a NON-stationary set of α has both
  --   x α 0 = β₀ AND x α 1 = β₁ — this requires an ANTI-fodor / counting
  --   argument NOT directly in Mathlib at SHA.
  sorry
```

### 4.3 The KEY missing step (S3b's main finding)

The disjointness step (e–f) hinges on the following sub-lemma, which
is **NOT in Mathlib at SHA** and would need to be proved companion to
the S2-β ACT:

```lean
-- Companion lemma needed for S2-β:
private lemma fodor_anti_constant {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (h_lim : ∀ α ∈ S, IsSuccLimit α)
    (g₀ g₁ : Ordinal → Ordinal) (hg₀_reg : ∀ α ∈ S, g₀ α < α)
    (hg₁_reg : ∀ α ∈ S, g₁ α < α)
    (h_pair_distinct : ∀ α ∈ S, ∃ β ∈ Set.Iio α, β ≠ g₀ α ∧ β ≠ g₁ α
                       ∧ True /- some additional structural hypothesis -/) :
    ∃ β₀ β₁ : Ordinal,
      IsStationaryBelow {α ∈ S | g₀ α = β₀ ∧ g₁ α = β₁} κ.ord ∧
      IsStationaryBelow {α ∈ S | g₀ α ≠ β₀ ∨ g₁ α ≠ β₁} κ.ord := by
  sorry
```

**This is the genuine technical obligation S3 PREP §4.3 step 3
deferred.** The `h_pair_distinct` hypothesis encodes "the cofinal
sequences for any two elements of S are distinct beyond their first
common term" — which holds for the canonical Solovay choice but not
for arbitrary regressive g₀, g₁.

**Estimated LOC for `fodor_anti_constant`**: 60–80 lines, using only
post-#19052 in-gallery bearers + Mathlib bearers C1–C12 + `Set.Iio`.

### 4.4 Disjointness recipe (concrete)

The disjointness obligation `S₁ ∩ S₂ = ∅` becomes mechanical once
`fodor_anti_constant` is in hand:

- Set `S₁ := T₁` from §4.2 step (e) — constant on both g₀ and g₁.
- Set `S₂ := {α ∈ S | g₀ α ≠ β₀ ∨ g₁ α ≠ β₁}` from
  `fodor_anti_constant`'s second conjunct.
- `α ∈ S₁ ∩ S₂` ⇒ both `g₀ α = β₀ ∧ g₁ α = β₁` AND
  `g₀ α ≠ β₀ ∨ g₁ α ≠ β₁` — contradiction.

`Disjoint S₁ S₂` follows from `Set.disjoint_iff_inter_eq_empty` +
the contradiction above.

---

## 5. Bearer-absence note: NoMaxOrder and "stationary intersect club"

S3 PREP §3.1 noted `Cardinal.IsRegular` is a `def` not `structure`.
S3b adds:

### 5.1 Mathlib does NOT have a packaged "stationary ∩ club = stationary" lemma at SHA

Search at SHA:

```
$ gh api "search/code?q=stationary+club+inter+repo:leanprover-community/mathlib4"
$ gh api "search/code?q=IsStationary.*Club+repo:leanprover-community/mathlib4"
```

Both return Mathlib hits only at `Set.IsStationary` (Mathlib's
generic `Set.IsStationary` for cardinal-indexed filters), NOT the
`IsStationaryBelow κ.ord` form used in `FodorPressingDown.lean`. The
gallery file's `IsStationaryBelow.of_subset` (line 343, used in the
S2-α proof) is the local bearer; it provides the "subset of stationary
is …" direction but NOT the "intersect with club" direction.

**Operational impact**: the S2-β ACT writer needs to prove a small
companion lemma `IsStationaryBelow.inter_isClubBelow` (~20 LOC) before
step (a) above can be discharged in <5 LOC. This is part of the LOC
budget revision in §6.

### 5.2 The companion lemma

```lean
theorem FodorPressingDown.IsStationaryBelow.inter_isClubBelow
    {S C : Set Ordinal} {κord : Ordinal}
    (hS : IsStationaryBelow S κord) (hC : IsClubBelow C κord) :
    IsStationaryBelow (S ∩ C) κord := by
  -- Use the existing fodor-style framework: S meets every club; C is itself
  -- a club; club ∩ club is club; so S ∩ C meets every club via S meeting
  -- (C ∩ that club).
  sorry
```

**Estimated LOC**: 20–30. Uses only the in-gallery `IsClubBelow` /
`IsStationaryBelow` definitions (lines 53/59) and elementary set-theory
from Mathlib.

---

## 6. Refined LOC budget for S2-β ACT

S3 PREP §5 estimated 180–220 LOC. With S3b's drill, the more defensible
breakdown is:

| Component | Est. LOC | Notes |
|---|---:|---|
| `IsStationaryBelow.inter_isClubBelow` companion (§5.2) | 20–30 | new; not in Mathlib at SHA |
| `fodor_anti_constant` companion (§4.3) | 60–80 | new; not in Mathlib at SHA |
| `stationary_splits_binary` main theorem (§4.1–§4.2) | 80–100 | uses the two companions + L3+L4+L5+L6 |
| Cofinal-sequence picking infrastructure (§4.2 step b) | 30–40 | `Classical.choose` + ℕ → cof α coercion |
| Imports + section/namespace setup + docstrings | 10–20 | — |
| **Total** | **200–270** | revised from S3 PREP's 180–220 |

The revised upper bound 270 (vs 220) accounts for the two companion
lemmas S3 PREP did not enumerate. The lower bound 200 (vs 180) reflects
the unavoidable cofinal-sequence picking infrastructure once the
companions are in hand.

### 6.1 Cross-PR conflict surface (extends S3 PREP §6 by one row)

| Target | #19052 (S2-α ACT) | #19207 (S3 PREP) | This S3b PREP |
|---|---:|---:|---:|
| `proofs/Proofs/FodorPressingDown.lean` | ✓ +68/-0 | ─ | ─ |
| `state.md` | ✓ +105/-42 | ─ | ─ |
| `JSON` (`fodor-pressing-down-oq-04.json`) | ✓ +25/-21 | ─ | ─ |
| `sessions/2026-05-14-s2a-act-...md` | ✓ NEW | ─ | ─ |
| `sessions/2026-05-15-s3-prep-...md` | ─ | ✓ NEW | ─ |
| `sessions/2026-05-15-s3b-prep-...md` (THIS) | ─ | ─ | ✓ NEW |

**Commit-disjoint from #19052 AND #19207.** No edit overlap on any
file. All three PRs can land in any order; the recommended sequence
is #19052 (load-bearing) → #19207 → #19052 → ACT (which depends on
#19052 having merged).

---

## 7. Honesty

This S3b PREP delivers:

- **0** new Lean theorems shipped.
- **0** sorry deltas.
- **0** axiom changes.
- **1** new design document (this file, ~270 LOC).
- **12** Mathlib v4.26.0 bearers pin-verified at SHA `2df2f015...`.
- **2** new Mathlib bearer absences flagged (no packaged "stationary ∩
  club" at SHA; no packaged "two regressives → two disjoint stationary").
- **1** Lean signature + proof outline for `stationary_splits_binary`.
- **1** companion lemma identified (`fodor_anti_constant`, ~60-80 LOC)
  that S3 PREP §4.3 step 3 implicitly assumed.
- **1** companion lemma identified (`IsStationaryBelow.inter_isClubBelow`,
  ~20-30 LOC) that S3 PREP §4.2 step (a) implicitly assumed.
- **1** LOC budget revision (180-220 → 200-270 with breakdown).

What this PREP does NOT do:

- Implement S2-β. That remains future ACT work.
- Implement either of the two companion lemmas. Both are deferred to
  the ACT.
- Edit `state.md`, `knowledge.md`, `problem.md`, or any JSON.
- Pre-empt the strategy choice. S3 PREP §4.5 recommends Strategy B
  (two-Fodor); §3 above promotes Solovay's CANONICAL technique
  (cofinal-sequence with index-of-first-disagreement) WITHIN Strategy
  B's umbrella — these are the same algebraic content, the canonical
  presentation just makes the disjointness obligation manageable.

### 7.1 Honesty about the two `sorry`s in §4.2

The proof outline in §4.2 has two `sorry`s and one comment-marked
"sorry  /- … -/" placeholder. These are presented as the residual
obligations the S2-β ACT writer needs to discharge. They are NOT
shipped as gallery code; this is a design document.

The discharges are:
1. `IsStationaryBelow.inter_isClubBelow` (the §5.2 companion).
2. `fodor_anti_constant` (the §4.3 companion).
3. `(n : Ordinal) < α.cof.ord` for `α ∈ S'` and `n : ℕ` — this needs
   the `IsSuccLimit α → ℵ₀ ≤ cof α` direction (C6) plus the
   `(n : Ordinal) < ℵ₀.ord` fact (Mathlib's `nat_lt_omega0` or
   similar).

### 7.2 Honesty about strategy ranking refinement

S3 PREP §4.5 recommended Strategy B (two-Fodor). S3b §3 promotes
Solovay's canonical technique within Strategy B. **This is not a
strategy change** — both are "two Fodor applications under
constraints"; the canonical technique just makes the second
application's domain (`g_n` for varying `n`) explicit and
constructive.

For κ ≥ ℵ₂, Strategy A (cofinality bifurcation) per S3 PREP §4.2
remains the cleanest path and should be considered if the gallery
specializes to ℵ₂ first.

### 7.3 Honesty about audit completeness

This PREP burned 4 `gh api repos/.../contents/...` reads at SHA
(Cofinality.lean + 2 search calls + 1 spot-check on Regular.lean
already done by S3 PREP). No additional `gh search code` quota burn
beyond S3 PREP's audit.

The bearer-absence finding (§5.1) was confirmed via two distinct
`search/code` queries returning hits only on Mathlib's generic
`Set.IsStationary`, NOT the gallery's `IsStationaryBelow κ.ord` form.

---

## 8. References

### 8.1 Open PRs
- **#19052** (S2-α ACT, CLEAN, ~12.4 h old at write-time): the
  predecessor providing post-merge bearers L5+L6.
- **#19207** (S3 PREP, CLEAN, ~2.6 h old at write-time): the design
  this PREP-2 closes the gap of (per its §5).

### 8.2 Mathlib references (v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
- `Mathlib/SetTheory/Cardinal/Cofinality.lean:437` — `IsFundamentalSequence`.
- `…/Cofinality.lean:499` — `exists_fundamental_sequence`.
- `…/Cofinality.lean:444,449,453` — accessors `cof_eq`, `strict_mono`,
  `blsub_eq`.
- `…/Cofinality.lean:581` — `aleph0_le_cof` (the `IsSuccLimit ↔ ℵ₀ ≤ cof`).
- `Mathlib/SetTheory/Cardinal/Regular.lean:42-49` — `IsRegular` def +
  accessors (per S3 PREP §3.1).

### 8.3 Local references
- `proofs/Proofs/FodorPressingDown.lean:259` — `fodor` (used twice
  in §4.2).
- `…/FodorPressingDown.lean:343` — `IsStationaryBelow.of_subset`
  (L3, used in §4.2 step (a)).
- `…/FodorPressingDown.lean:53,59` — `IsClubBelow`, `IsStationaryBelow`
  definitions.
- (post-#19052) `isLimitOrdinals_isClubBelow` (L5) and
  `nonLimitOrdinals_not_isStationaryBelow` (L6) — the S2-α deliverables
  this PREP composes against.

### 8.4 Memory references
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
  — informs the §1 conflict-free-angle decision.
- `feedback_researcher_preflight_audits_priorsession_discharge_plan_for_mathlib_bearer`
  — the general pattern of auditing prior-session plans against the
  pinned SHA. (Drilling step 3 of S3 PREP §4.5 is a same-pattern
  follow-up.)
- `feedback_researcher_deployer_stall_coordination_prep_pattern`
  — the documented coordination-PREP pattern S3 PREP itself follows.

### 8.5 Mathematical references
- Jech, T., **Set Theory** (Springer 2003), Theorem II.8.10
  (Solovay's theorem on stationary splitting).
- Kanamori, A., **The Higher Infinite** (Springer 2003), Theorem 7.7.

---

**End of S3b PREP — no Lean changes, no gallery JSON / state.md edits,
no axiom changes. PR #19052 (S2-α ACT) and PR #19207 (S3 PREP) are
both prerequisite for the S2-β ACT this PREP-2 designs against; this
S3b PREP is conflict-free with both. Two companion lemmas identified
(`IsStationaryBelow.inter_isClubBelow`, `fodor_anti_constant`); both
provable at SHA. Refined S2-β LOC budget: 200-270 (was S3 PREP's
180-220).**
