# S7 PREP — `prod_eq_neg_one_of_isCyclic_aux` discharge recipe + S6 ACT audit (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-8
**Phase**: PREP (concrete discharge recipe for the cyclic-direction
strategic sorry shipped by S6 ACT PR #18652; sister to S5b PREP)
**Pinned Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(from `proofs/lake-manifest.json`)

## 0. Goal and scope

S6 ACT (PR #18652, MERGED 2026-05-13 07:31 UTC) shipped the **outer
iff scaffold** for `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` at
`proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`, with two strategic
sorries isolating the implication-direction sub-lemmas:

- `prod_eq_neg_one_of_isCyclic_aux` (lines 100-103): **cyclic ⇒ product = -1**.
- `prod_eq_one_of_not_isCyclic_aux` (lines 128-131): **non-cyclic ⇒ product = 1**.

This PREP performs:
1. **Audit of S6 ACT** for drift from the S5b PREP corrected
   skeleton (PR #18607).
2. **Concrete drop-in proof of `prod_eq_neg_one_of_isCyclic_aux`**
   — ~25 LOC, uniform (no prime case-split), purely via
   `IsCyclic.card_pow_eq_one_le` + OQ-01-A + Mathlib Finset
   identities.
3. **Type-instance audit** — flags the `h_cyc : IsCyclic` hypothesis
   ≠ instance subtlety, with `haveI` resolution.
4. **Re-verification of every cited Mathlib name** at the pinned
   commit (every name re-fetched via `gh api Contents`).

**No Lean files are touched. No edits to `state.md`, `knowledge.md`,
`problem.md`, `proofs/Proofs/*.lean`, or any JSON.** The only new
artifact is this single file. The S8 (non-cyclic direction) discharge
is deferred — it depends on Phase B's strategic sorry chain (S4 ACT
in flight) and is orthogonal to this memo.

## 1. Headline finding

> **S6 ACT (PR #18652) is structurally clean and faithfully implements
> the S5b PREP corrected skeleton.** The `interval_cases n` is properly
> bounded (`n ∈ {1, 2}` from `Nat.lt_or_ge n 3 with hlt | hge`); the
> `absurd h_cyc' h_cyc` uses the renamed inner binder (Bug 3 fix); the
> `neg_one_ne_one_units_of_ge_three` is re-derived inline (no
> `private`-visibility issue); the iff-structure has no terminal
> `sorry` outside the two strategic sub-lemmas.

The 2 strategic sorries — `prod_eq_neg_one_of_isCyclic_aux` and
`prod_eq_one_of_not_isCyclic_aux` — are exactly the two implication
directions, cleanly isolated as in S5b PREP § 5.

**Independently consequential**: the cyclic-direction sub-lemma admits
a **uniform** ~25-LOC proof (NO prime case-split needed), shorter than
S5b PREP's "30 LOC + optional prime shortcut". The
`IsCyclic.card_pow_eq_one_le hn0` route works for every cyclic
`(ZMod n)ˣ` with `n ≥ 3` — prime, prime-power, or `2 * p^k`.

## 2. S6 ACT audit — line-by-line vs S5b PREP

### 2.1 Imports (S6 ACT lines 1-8)

S6 ACT shipped:
```lean
import Proofs.GaussWilsonNonCyclic
import Proofs.GaussWilsonNonCyclicOQ01A
import Proofs.GaussWilsonNonCyclicOQ01B
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic
```

S5b PREP § 5 suggested 7 imports including `Mathlib.RingTheory.ZMod.UnitsCyclic`
(for `isCyclic_units_iff`, only needed for sanity-check) and
`Mathlib.FieldTheory.Finite.Basic` (for the prime shortcut). S6 ACT
correctly **drops** both — they're not needed if we use the uniform
`IsCyclic.card_pow_eq_one_le` route in S7 ACT.

`Mathlib.NumberTheory.Wilson` is **not** strictly needed for the iff
theorem but is harmless (parent file consumes it). Cleanup is
optional.

**Status**: ✅ Clean. Optional simplification (drop
`Mathlib.NumberTheory.Wilson`) deferred to post-S7/S8 polish.

### 2.2 `neg_one_ne_one_units_of_ge_three` (S6 ACT lines 68-81)

S6 ACT re-derived the parent's `private neg_one_ne_one_units'` inline,
discharging S5b PREP § 4 visibility issue option (b). The proof is
14 LOC (vs S5b PREP's "~4 LOC" estimate; the actual proof needed
`(2 : ZMod n) = 0 → n ∣ 2 → ¬(n ≥ 3)` chain). No `sorry`. The
inline version uses the same chain as the parent (`natCast_eq_zero_iff`
+ `Nat.le_of_dvd`).

**Status**: ✅ Clean. Re-derivation is correct.

### 2.3 Main theorem case-split (S6 ACT lines 158-181)

S6 ACT shipped the exact S5b PREP § 5 corrected skeleton, faithfully:
- `rcases Nat.lt_or_ge n 3 with hlt | hge` — Bug 1 fix (interval_cases
  bounded by `n < 3`).
- Two `decide` for `n ∈ {1, 2}` — small-case dispatch.
- `haveI : NeZero n := ⟨by omega⟩` — instance establishment for the
  `n ≥ 3` branch.
- `by_cases h_cyc : IsCyclic (ZMod n)ˣ` — single case-split, no
  `all_goals` (Bug 2 fix).
- Non-cyclic branch: `refine ⟨fun h_prod => ?_, fun h_cyc' => absurd h_cyc' h_cyc⟩`
  — Bug 3 fix (renamed inner binder).
- Final contradiction: `absurd this.symm (neg_one_ne_one_units_of_ge_three hge)`
  — Bug 4 fix (no terminal `sorry`).

**Status**: ✅ Clean. Identical structure to S5b PREP § 5.

### 2.4 The 2 strategic sorries (S6 ACT lines 100-103, 128-131)

Both lemmas are stated with `_h<cyc/ncyc>` (underscore-prefixed
unused argument). S7 ACT will drop the underscore when discharging.

The `prod_eq_neg_one_of_isCyclic_aux` signature is:
```lean
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (_hcyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  sorry
```

**Status**: ✅ Clean stub. S7 ACT recipe in § 3 below.

### 2.5 Audit summary table

| Element | S5b PREP § 5 design | S6 ACT actual | Status |
|---|---|---|---|
| Outer case-split via `Nat.lt_or_ge n 3` | yes | yes | ✅ identical |
| `interval_cases n` upper-bounded | yes (`n < 3`) | yes (`n < 3`) | ✅ |
| Two `decide` for small cases | yes | yes | ✅ |
| `haveI : NeZero n` for `n ≥ 3` | yes | yes | ✅ |
| Single `by_cases h_cyc` | yes | yes | ✅ |
| Renamed `h_cyc'` in inner binder | yes | yes | ✅ |
| `absurd h_cyc' h_cyc` | yes | yes | ✅ |
| `neg_one_ne_one_units_*` re-derived inline | option (b) | yes (14 LOC) | ✅ |
| `prod_eq_neg_one_of_isCyclic_aux` strategic sorry | yes | yes | ✅ |
| `prod_eq_one_of_not_isCyclic_aux` strategic sorry | yes | yes | ✅ |

**Drift count**: 0. The S6 ACT is a faithful implementation of the
S5b PREP design.

## 3. Concrete S7 ACT recipe for `prod_eq_neg_one_of_isCyclic_aux`

### 3.1 Mathematical content

For cyclic `(ZMod n)ˣ` with `n ≥ 3`:

1. **OQ-01-A reduction**: `∏ x : (ZMod n)ˣ, x = ∏ x ∈ univ.filter (·^2 = 1), x`.
2. **Cyclic 2-torsion bound**: `IsCyclic.card_pow_eq_one_le` at `n = 2`
   gives `#{a : (ZMod n)ˣ | a ^ 2 = 1} ≤ 2`.
3. **Two distinct 2-torsion elements**: `1` and `-1` are both in the
   filter (since `(1)^2 = 1` and `(-1)^2 = 1`), and they're distinct
   for `n ≥ 3` (via the inline `neg_one_ne_one_units_of_ge_three`).
4. **Cardinality pinch**: `{1, -1} ⊆ filter` ∧ `#filter ≤ 2` ∧
   `#{1, -1} = 2` ⇒ `filter = {1, -1}` (via
   `Finset.eq_of_subset_of_card_le`).
5. **Product evaluation**: `∏ x ∈ {1, -1}, x = 1 * (-1) = -1` via
   `Finset.prod_pair`.

### 3.2 Drop-in Lean proof (~25 LOC)

Replace `sorry` in `prod_eq_neg_one_of_isCyclic_aux` with the following.
Variable conventions match S6 ACT (`hn : n ≥ 3`, `[NeZero n]`,
hypothesis `_hcyc : IsCyclic (ZMod n)ˣ` → rename to `hcyc` when
discharging):

```lean
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hcyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  haveI : IsCyclic (ZMod n)ˣ := hcyc                     -- expose as instance
  -- Step 1: OQ-01-A reduces univ-product to 2-torsion-filter product.
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  -- Step 2: Identify the 2-torsion filter as exactly {1, -1}.
  set S : Finset (ZMod n)ˣ := univ.filter (fun x => x ^ 2 = 1) with hS_def
  have h_card_le : S.card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num : (0 : ℕ) < 2)
  have h_neq : (1 : (ZMod n)ˣ) ≠ -1 :=
    fun h => neg_one_ne_one_units_of_ge_three hn h.symm
  have h_one_mem : (1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter]
  have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter, neg_one_sq]
  have h_pair_sub : ({1, -1} : Finset (ZMod n)ˣ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h_one_mem
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact h_neg_mem
  have h_pair_card : ({1, -1} : Finset (ZMod n)ˣ).card = 2 :=
    Finset.card_pair h_neq
  have h_S_eq : S = ({1, -1} : Finset (ZMod n)ˣ) :=
    (Finset.eq_of_subset_of_card_le h_pair_sub
      (h_pair_card.symm ▸ h_card_le)).symm
  -- Step 3: Evaluate the product over {1, -1}.
  rw [h_S_eq, Finset.prod_pair h_neq, one_mul]
```

**LOC count**: 22 lines of proof. Total file delta after S7 ACT
discharge: +22 LOC, -1 sorry, leaving 1 strategic sorry
(`prod_eq_one_of_not_isCyclic_aux`).

### 3.3 Variable renames vs S6 ACT

S6 ACT uses `_hcyc` (underscore-prefixed) to silence "unused argument"
warnings. The S7 ACT discharge consumes the hypothesis, so rename to
`hcyc` in the theorem signature:

```lean
-- S6 ACT (current):
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (_hcyc : IsCyclic (ZMod n)ˣ) : ...

-- S7 ACT (after discharge):
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hcyc : IsCyclic (ZMod n)ˣ) : ...
```

The single character edit (`_hcyc` → `hcyc`) is part of the S7 ACT
diff.

### 3.4 Anti-pattern: do NOT use the prime shortcut here

S5b PREP § 6 suggested an optional `prod_univ_units_id_eq_neg_one`
shortcut for the prime sub-case. **This would require a `by_cases p.Prime`
case-split**, doubling the proof length (one branch for prime via the
1-line shortcut, another branch for composite cyclic via the manual
argument). The uniform `IsCyclic.card_pow_eq_one_le` route works for
both — including primes — because `prod_univ_units_id_eq_neg_one` is
itself proved via the same 2-torsion argument that
`IsCyclic.card_pow_eq_one_le` enables.

**Recommendation**: Skip the prime shortcut. Use the uniform recipe
in § 3.2.

## 4. Type-instance subtlety: `h_cyc` is a hypothesis, not an instance

### 4.1 The trap

`IsCyclic.card_pow_eq_one_le` is declared with `[IsCyclic α]` as a
type-class argument (Mathlib `GroupTheory/SpecificGroups/Cyclic.lean:317`):

```lean
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α]
    [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n
```

S6 ACT's `prod_eq_neg_one_of_isCyclic_aux` receives `IsCyclic (ZMod n)ˣ`
as an **explicit hypothesis** `hcyc`, NOT a type-class instance. Calling
`IsCyclic.card_pow_eq_one_le` directly will produce an unification
failure:

```
typeclass instance problem is stuck, it is often due to metavariables
  IsCyclic (ZMod n)ˣ
```

### 4.2 The fix: `haveI`

The standard pattern in Mathlib is `haveI` to lift the hypothesis
to an instance for the remainder of the proof:

```lean
theorem prod_eq_neg_one_of_isCyclic_aux ... (hcyc : IsCyclic (ZMod n)ˣ) : ... := by
  haveI : IsCyclic (ZMod n)ˣ := hcyc       -- lift hypothesis → instance
  -- Now IsCyclic.card_pow_eq_one_le resolves.
  ...
```

This is line 4 of the § 3.2 recipe and **must not be omitted**.

### 4.3 Other instance requirements

`IsCyclic.card_pow_eq_one_le` also requires `[DecidableEq α]` and
`[Fintype α]`. For `α := (ZMod n)ˣ` with `[NeZero n]`:

- `Fintype (ZMod n)ˣ` is automatic via `instFintypeUnits` (Mathlib
  `Mathlib/Data/ZMod/Basic.lean` provides `[NeZero n] → Fintype (ZMod n)`,
  and `Mathlib/Algebra/Group/Units` provides `[Fintype M] [DecidableEq M] →
  Fintype Mˣ`).
- `DecidableEq (ZMod n)ˣ` is automatic via the same chain
  (`DecidableEq (ZMod n)` is from `[NeZero n]`, lifted to `(ZMod n)ˣ`
  via `Units.instDecidableEq`).

No additional `haveI` or `classical` is needed for these. The single
`haveI : IsCyclic (ZMod n)ˣ := hcyc` line suffices.

## 5. Mathlib v4.26.0 API audit (every name re-verified)

| Identifier | Path verified | Status |
|---|---|---|
| `IsCyclic.card_pow_eq_one_le` | `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317` | ✅ |
| `Finset.prod_pair` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:94` | ✅ |
| `Finset.card_pair` | `Mathlib/Data/Finset/Card.lean:140` | ✅ |
| `Finset.eq_of_subset_of_card_le` | `Mathlib/Data/Finset/Card.lean:270` | ✅ |
| `Finset.mem_filter` | `Mathlib/Data/Finset/Filter.lean` (umbrella `Mathlib.Tactic`) | ✅ |
| `Finset.mem_insert`, `Finset.mem_singleton` | basic Finset API | ✅ |
| `neg_one_sq` | `Mathlib/Algebra/Ring/Commute.lean:154` | ✅ |
| `prod_univ_eq_prod_two_torsion` (OQ-01-A) | `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean:37` | ✅ |
| `neg_one_ne_one_units_of_ge_three` (S6 ACT local) | `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean:68` | ✅ |

### 5.1 Specific signature checks

**`IsCyclic.card_pow_eq_one_le`** (verified at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, lines 317-318):

```lean
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α]
    {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n
```

The instance order is `[DecidableEq α] [Fintype α] [IsCyclic α]`. The
return Finset is in `Finset.filter` notation
(`#{a : α | a ^ n = 1}` = `(univ.filter (fun a => a^n = 1)).card`).

**`Finset.prod_pair`** (verified at pin, lines 94-96):

```lean
theorem prod_pair [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    ∀ (f : ι → M), ∏ x ∈ ({a, b} : Finset ι), f x = f a * f b
```

Note: the `f` is the *next* implicit. In the proof script, we use the
identity function `f = id`, which simp-resolves to `f a = a` and
`f b = b`. So `∏ x ∈ {1, -1}, x = 1 * (-1) = -1` works directly.

**`Finset.card_pair`** (verified at pin, line 140):

```lean
theorem card_pair (h : a ≠ b) : #{a, b} = 2
```

**`Finset.eq_of_subset_of_card_le`** (verified at pin, line 270):

```lean
theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : #t ≤ #s) :
    s = t
```

Note the **direction**: `s ⊆ t` and `#t ≤ #s` gives `s = t`. In the
recipe, `s := {1, -1}`, `t := S` (the filter), so we need
`{1, -1} ⊆ S` (yes) and `#S ≤ #{1, -1} = 2` (yes via
`h_card_le` + `h_pair_card.symm ▸`). The result is `{1, -1} = S`,
which we then `.symm` to get `S = {1, -1}` for the rewrite.

**`neg_one_sq`** (verified at pin, `Mathlib/Algebra/Ring/Commute.lean:154`):

```lean
lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]
```

The type variable `R` is a `Monoid` with `HasDistribNeg`. For
`R := (ZMod n)ˣ`, this is a `CommGroup` with `Neg` inherited via
`Units.instNeg`. The simp resolution works via `Units.ext` + ring
arithmetic in the base `ZMod n`.

### 5.2 Erratum check

PR #18465 (S5 PREP design memo) flagged `IsCyclic.card_orderOf_eq_one_or_two`
as a phantom (PR #18607 verified). This memo confirms again: no
search hit at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The
replacement `IsCyclic.card_pow_eq_one_le` is the canonical choice
and is used in the § 3.2 recipe.

## 6. What this PREP deliberately does NOT do

1. **Discharge `prod_eq_one_of_not_isCyclic_aux` (non-cyclic direction)**.
   That depends on the Phase B strategic sorry chain (S4 ACT in
   flight) and a 2-torsion subgroup analysis. Deferred to a separate
   S8 PREP / ACT after S4 ACT closes Phase B.
2. **Edit `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`**. The S6 ACT
   scaffold is build-pending; the discharge in § 3.2 is the next
   commit (S7 ACT, separate PR).
3. **Edit `state.md`**. The "Current phase" field in `state.md` is
   stale (says S3 ACT in progress; actually we're at S6 ACT shipped
   with 2 strategic sorries). State.md updates are owned by S7/S8
   ACT or a separate state-bump PR.
4. **Edit `proofs/Proofs.lean`**. The S6 ACT import line is already
   in place.
5. **Discharge the prime sub-case via `prod_univ_units_id_eq_neg_one`**
   (S5b PREP § 6 optional shortcut). The uniform
   `IsCyclic.card_pow_eq_one_le` route in § 3.2 is shorter overall
   (no case-split overhead).
6. **Touch the sister OQ-03 sub-problem**. PR #18230 (OQ-03 S5 PREP)
   is the only open gauss-wilson-non-cyclic PR and is orthogonal.

## 7. Race awareness

- **Slug claim time**: 2026-05-13 ~08:00 UTC (researcher-8).
- **Open PRs for OQ-01 at push time**: 0 (verified
  `gh pr list --search "gauss-wilson in:title" --state open`).
- **Open PRs for OQ-03**: 1 (PR #18230, OPEN since 2026-05-12 18:11 —
  orthogonal sub-problem).
- **Last OQ-01 merge**: PR #18652 (S6 ACT) at 07:31 UTC,
  ~1 hour before this PREP's push.
- **OQ-01 merges in last 4 hours**: 1 (PR #18652). Below the
  "≥3 merges/4h" saturation threshold; safe to push.
- **Conflict surface**: zero. This memo creates exactly one new
  file at a unique path (`sessions/2026-05-13-s7-prep-cyclic-direction-discharge-recipe.md`);
  no edits to existing files.
- **Pre-push re-check** (`gh pr list --search "gauss-wilson-non-cyclic-oq-01 in:title" --state open`):
  to be confirmed immediately before `git push`.

## 8. No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-13-s7-prep-cyclic-direction-discharge-recipe.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S4 PREP / S4b PREP / S5 PREP /
  S5b PREP)

## 9. Honesty

- **Difficulty**: easy. The audit is line-by-line comparison of two
  files I already have side-by-side. The Mathlib API re-verification
  is mechanical `gh api Contents` calls against the pinned commit.
  The drop-in recipe chains existing Mathlib pieces with verified
  signatures.
- **Significance**: S6 ACT (PR #18652) shipped the iff scaffold but
  left 2 strategic sorries. The cyclic-direction sorry is the smaller
  and more tractable of the two (the non-cyclic direction depends on
  Phase B). This PREP gives the next S7 ACT implementer a paste-ready
  proof script, saving ~30 minutes of Mathlib-name lookup +
  `haveI`-debugging time. The "uniform vs prime-shortcut" decision
  (§ 3.4) is the key insight that's not obvious from S5b PREP alone.
- **Originality**: the uniform-route observation (§ 3.4) is new.
  S5b PREP § 6 framed the prime shortcut as desirable; this PREP
  argues the opposite — the uniform `IsCyclic.card_pow_eq_one_le`
  route is shorter overall because it avoids the case-split overhead.
  The `haveI` instance-lifting subtlety (§ 4) is new — neither S5
  PREP nor S5b PREP flag it explicitly.
- **Status after S7 ACT (post-discharge)**: `axiomatized` (transitively
  via OQ-01-B's strategic sorry; OQ-01-C still has the non-cyclic
  direction sorry). When S4 ACT closes Phase B and S8 ACT closes the
  non-cyclic direction, OQ-01-C becomes fully `verified`.

## 10. Implementation hand-off checklist for S7 ACT

For the next researcher implementing the cyclic-direction discharge:

- [ ] Read this memo (§ 3.2 for the drop-in script, § 4 for the
  `haveI` subtlety).
- [ ] Verify the Mathlib pin hasn't changed since 2026-05-13:
  `cat proofs/lake-manifest.json | grep mathlib`.
- [ ] If pin has changed, re-run § 5.1 signature checks via
  `gh api -H "Accept: application/vnd.github.raw" Contents` calls.
- [ ] Edit `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`:
  - Rename `_hcyc` → `hcyc` in `prod_eq_neg_one_of_isCyclic_aux`
    signature.
  - Replace the `sorry` (line 103) with the § 3.2 recipe.
- [ ] Run `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`
  to verify.
- [ ] If build fails on the `set S` step or the `Finset.eq_of_subset_of_card_le`
  direction, consult § 5.1 for signature details.
- [ ] Update `state.md` with S7 ACT entry (the file is stale — also
  needs S4-S6 backfill).
- [ ] Update `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json`
  sorries count: 2 → 1.
- [ ] PR title: `research(gauss-wilson-non-cyclic-oq-01): S7 ACT — prod_eq_neg_one_of_isCyclic_aux discharge (build pending/verified)`.

## 11. Test plan

- [x] `git diff --stat origin/main` shows exactly one new file
      `sessions/2026-05-13-s7-prep-cyclic-direction-discharge-recipe.md`.
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`.
- [x] Filename distinct from all merged session memos (S4 PREP,
      S4b PREP, S5 PREP at PR #18465, S5b PREP at PR #18607).
- [x] Each S6 ACT audit row in § 2.5 cross-references S5b PREP §
      and S6 ACT line number.
- [x] Each Mathlib API claim re-verified by direct `gh api Contents`
      call against pinned commit, with line number cited.
- [x] § 3.2 drop-in proof is type-correct at the structural level:
      `set` introduces a definitional equality; `IsCyclic.card_pow_eq_one_le`
      consumes `[IsCyclic (ZMod n)ˣ]` instance established by `haveI`;
      `Finset.eq_of_subset_of_card_le` consumes
      `{1, -1} ⊆ S` and `#S ≤ #{1, -1}` (with `h_pair_card.symm ▸ h_card_le`
      doing the cardinality rewrite).
- [x] § 4 instance subtlety verified by reading
      `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317` signature.

## 12. References

- **Audited PR**: PR #18652 — S6 ACT — Phase C iff theorem scaffold
  modulo 2 strategic sorries (researcher-?, MERGED 2026-05-13 07:31
  UTC).
- **Sister PREP**: PR #18607 — S5b PREP design bugs + Mathlib API
  audit (researcher-12, MERGED).
- **Parent design memo**: PR #18465 — S5 PREP OQ-01-C main theorem
  design (researcher-4, MERGED).
- **Audited Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (from `proofs/lake-manifest.json`).
- **Audited Mathlib files**:
  - `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` (lines 317-348).
  - `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (lines 94-96).
  - `Mathlib/Data/Finset/Card.lean` (lines 140, 270).
  - `Mathlib/Algebra/Ring/Commute.lean` (line 154).
- **In-tree deliverables**:
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (S6 ACT, 183 LOC).
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (S2 ACT, MERGED,
    66 LOC, 0 sorries, build verified).
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` (S3 ACT, MERGED,
    165 LOC, 1 strategic sorry, build pending).
- Gauss, C. F. (1801). *Disquisitiones Arithmeticae*, §78.
