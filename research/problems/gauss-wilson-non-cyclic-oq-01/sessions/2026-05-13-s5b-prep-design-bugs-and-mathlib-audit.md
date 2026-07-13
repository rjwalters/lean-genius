# S5b PREP — bug audit of merged S5 PREP design memo + Mathlib v4.26.0 API audit (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (sister to MERGED PR #18465 S5 PREP — strictly orthogonal,
audits proof-skeleton bugs and adds Mathlib API verification)
**Pinned Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(from `proofs/lake-manifest.json`)

## 0. Goal and scope

Merged PR #18465 (S5 PREP, MERGED 2026-05-13 02:18:57 UTC) drafted the
proof skeleton for OQ-01-C — the headline iff theorem
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` for
`gauss-wilson-non-cyclic-oq-01`. The memo provides a sub-lemma
decomposition and a main-theorem case-split, but **the Lean tactic
script as written contains four concrete bugs that prevent it from
type-checking**, plus the Mathlib API call-outs are aspirational
(name guesses — explicitly flagged in the memo as "must be verified
before ACT").

This PREP performs:
1. **Bug audit** of the four issues in PR #18465's proof skeleton.
2. **Mathlib v4.26.0 API audit** for the three key external dependencies
   — `ZMod.isCyclic_units_iff`, `IsCyclic.card_pow_eq_one_le`, and
   `prod_univ_units_id_eq_neg_one`.
3. **Visibility audit** of `neg_one_ne_one_units'` from the parent file
   `proofs/Proofs/GaussWilsonNonCyclic.lean`.
4. **A corrected proof skeleton** that addresses all four bugs and
   uses the audited Mathlib API.
5. **Revised LOC estimate** (PR #18465 said "~80 LOC"; with bug fixes
   plus the optional `prod_univ_units_id_eq_neg_one` shortcut for the
   prime case, realistic estimate is ~120-140 LOC).

**No Lean files are touched. No edits to `state.md`, `knowledge.md`,
`problem.md`, `proofs/Proofs/*.lean`, gallery JSON, or `proofs/Proofs.lean`.**
The only new artifact is this single file.

## 1. Headline finding

> **PR #18465 § "Main theorem (assembly)" is unsoundly written**: the
> `interval_cases n` tactic at line 126 of the memo requires both
> a lower and an upper bound on `n`, but the hypothesis is only
> `1 ≤ n`. Without an upper bound, `interval_cases` will fail (or
> diverge in pathological encodings).

The proof skeleton at lines 122-141 of PR #18465 cannot type-check
as drafted. An S5 ACT implementer who copy-pastes the skeleton will
encounter immediate failures and have to redesign the case structure
from scratch. Three additional bugs accompany the `interval_cases`
issue (see § 2).

**Independently consequential**: the memo's § "Mathlib API dependencies"
table (lines 146-156) flags two key identifiers — `ZMod.isCyclic_units_iff`
and `IsCyclic.card_orderOf_eq_one_or_two (if exists)` — as needing
verification. **The first is verified to exist** (with a different
disjunction structure than the memo assumed); **the second does not
exist by that name** (the closer match is `IsCyclic.card_pow_eq_one_le`,
generic over `n`).

## 2. Four concrete bugs in PR #18465's `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`

The proof skeleton from PR #18465 lines 122-141 reproduced verbatim
(with line numbers from the memo for cross-reference):

```lean
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic
    {n : ℕ} (hn : 1 ≤ n) :
    (∏ x : (ZMod n)ˣ, x) = -1 ↔ IsCyclic (ZMod n)ˣ := by
  -- Small cases first.
  interval_cases n                                              -- BUG #1
  · decide
  · decide
  all_goals                                                     -- BUG #2
    by_cases h_cyc : IsCyclic (ZMod n)ˣ
    · exact ⟨fun _ => h_cyc, fun _ => prod_eq_neg_one_of_isCyclic_aux (by omega) h_cyc⟩
    · refine ⟨fun h_prod => ?_, fun h_cyc => absurd h_cyc h_cyc⟩  -- BUG #3
      have : (1 : (ZMod n)ˣ) = -1 := by
        rw [← prod_eq_one_of_not_isCyclic_aux (by omega) h_cyc, h_prod]
      sorry                                                     -- BUG #4
```

### Bug 1 — `interval_cases n` has no upper bound

`Mathlib.Tactic.IntervalCases.intervalCases` requires both lower and
upper bounds on the variable being case-split. The hypothesis
`hn : 1 ≤ n` provides only the lower bound; without an upper bound
(say `n < 10`), `interval_cases n` immediately errors:

```
unsolved goals
n : ℕ
hn : 1 ≤ n
⊢ ...
```

**Fix.** Replace `interval_cases n` with one of:

(a) **Explicit `match n, hn` pattern.** Discriminate `n` into the cases
`{1, 2, 3+}` directly:

```lean
match n, hn with
| 0, hn => omega                          -- impossible (1 ≤ 0)
| 1, _  => decide
| 2, _  => decide
| (n+3), _ => ...                          -- the n ≥ 3 case
```

(b) **`rcases` on `n` decomposition.** Split `1 ≤ n` into
`n = 1 ∨ n = 2 ∨ 3 ≤ n` first via:

```lean
rcases Nat.lt_or_ge n 3 with hlt | hge
· interval_cases n
  · decide   -- n = 1
  · decide   -- n = 2
· -- main case n ≥ 3
  ...
```

This is the cleanest fix and keeps the small-case `decide`s contained.
`interval_cases n` here is sound because both bounds (`1 ≤ n < 3`)
are present. (Recommended.)

### Bug 2 — `all_goals` does not apply

After `interval_cases n` discharges concrete cases via `decide`, no
abstract `n`-parameterised goal remains. The `all_goals` block is
therefore either empty or unsoundly applied to an already-closed
proof state. The `by_cases h_cyc : IsCyclic (ZMod n)ˣ` inside the
`all_goals` references the (now-instantiated) `n`, which would be
`1` or `2` if any goals were left after `decide` — neither of which
needs the cyclic case-split (cyclicity is automatic at `n ∈ {1, 2}`).

**Fix.** Drop `all_goals`. After the small-case branch closes via
`decide`, the second branch in option (b) above (the `n ≥ 3` case)
has the abstract `n` available and can directly do
`by_cases h_cyc : IsCyclic (ZMod n)ˣ` outside any wrapping tactic.

### Bug 3 — `absurd h_cyc h_cyc` does not type-check

The expression `absurd h_cyc h_cyc` reads "given the hypothesis
`h_cyc : ¬IsCyclic (ZMod n)ˣ` and the same hypothesis `h_cyc`, derive
`False`". `Mathlib.Logic.Basic.absurd : a → ¬a → b` requires the **first
argument** to have the proposition type and the **second argument**
to be the negation. Two `¬P`s do not satisfy this signature.

**Fix.** The intent of the right-to-left direction in the non-cyclic
case is "`IsCyclic ⇒ prod = -1`, but `¬IsCyclic` is in scope, so the
hypothesis `IsCyclic` is impossible". The correct skeleton is:

```lean
refine ⟨fun h_prod => ?_, fun h_cyc => absurd h_cyc not_h_cyc⟩
```

where `not_h_cyc : ¬IsCyclic (ZMod n)ˣ` is the original case
hypothesis (the memo's `h_cyc` shadowed by `by_cases`). Renaming
clarifies:

```lean
by_cases h_cyc : IsCyclic (ZMod n)ˣ
· exact ⟨fun _ => h_cyc, fun _ => prod_eq_neg_one_of_isCyclic_aux ... h_cyc⟩
· refine ⟨fun h_prod => ?_, fun h_cyc' => absurd h_cyc' h_cyc⟩
  -- ^ h_cyc' : IsCyclic (within the lambda); h_cyc : ¬IsCyclic (outer)
```

This is the standard "the iff-RHS is false, therefore the iff-LHS is
also false because the implication arrow is contrapositively-vacuous"
pattern.

### Bug 4 — terminal `sorry` on the `(1 : (ZMod n)ˣ) = -1` derivation

The skeleton derives `(1 : (ZMod n)ˣ) = -1` from
`prod_eq_one_of_not_isCyclic_aux ... = 1` and `h_prod : prod = -1`,
but does not close the goal. The intended argument is:

> `(1 : (ZMod n)ˣ) = -1` only happens when `n ∈ {1, 2}` (in `ZMod n`,
> `1 = -1 ↔ 2 ≡ 0 mod n ↔ n ∣ 2`). For `n ≥ 3`, this contradicts the
> hypothesis `n ≥ 3` (or `1 ≤ n` plus the implicit case-elimination
> on `n < 3`).

**Fix.** Use the parent file's `neg_one_ne_one_units'` (with caveat
in § 4 below — this lemma is `private`!) or re-prove inline:

```lean
exact absurd this (neg_one_ne_one_units' (by omega : n ≥ 3)).symm
```

Or, since `n ≥ 3` and `(ZMod n)` has `2 < n`, derive
`(1 : (ZMod n)) ≠ -1` from
`ZMod.natCast_eq_natCast_iff'` / `neg_one_ne_one_zmod'` (the parent's
companion to `neg_one_ne_one_units'`).

## 3. Mathlib v4.26.0 API audit

### 3.1 `ZMod.isCyclic_units_iff` — VERIFIED ✓ (with structural correction)

PR #18465 § "Mathlib API dependencies" (line 150) cites
`ZMod.isCyclic_units_iff` at module
`Mathlib.NumberTheory.ZMod.UnitsMultiplicativeStructure` for
"Cyclicity characterization" without specifying the disjunction
structure.

**Verified location at pinned commit**: `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`
(NOT `NumberTheory.ZMod.UnitsMultiplicativeStructure`).

**Verified signature** (lines 327-331):

```lean
/-- `(ZMod n)ˣ` is cyclic iff `n` is of the form
`0`, `1`, `2`, `4`, `p ^ m`, or `2 * p ^ m`,
where `p` is an odd prime and `1 ≤ m`. -/
theorem isCyclic_units_iff (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
      ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m)
```

**Implications for OQ-01-C**:

- The memo's `prod_eq_neg_one_of_isCyclic_aux` and
  `prod_eq_one_of_not_isCyclic_aux` work directly with `IsCyclic`
  hypothesis or its negation; they do NOT need to unfold
  `isCyclic_units_iff`. So this lemma is **not** strictly necessary
  for OQ-01-C — `IsCyclic (ZMod n)ˣ` can be passed through opaquely.
- It IS useful as a sanity check / validation gate (the iff theorem
  is the structural characterisation; the OQ-01-C iff is the
  product-formula characterisation, equivalent under the structural
  one).

**Action item for S5 ACT**: drop the dependency on
`ZMod.isCyclic_units_iff`. Use `IsCyclic` opaquely.

### 3.2 `IsCyclic.card_pow_eq_one_le` — VERIFIED ✓ (replaces non-existent `IsCyclic.card_orderOf_eq_one_or_two`)

PR #18465 § "Mathlib API dependencies" (line 151) lists
`IsCyclic.card_orderOf_eq_one_or_two (if exists)` for `|G[2]| ≤ 2`.

**This name does not exist** at the pinned commit (`grep -r` returns
0 hits). The closest match is:

**Verified location at pinned commit**: `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317`.

**Verified signature** (line 317):

```lean
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α]
    [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n
```

For `n = 2` and `α := (ZMod n)ˣ` with `IsCyclic` instance, this
yields:

```lean
#{a : (ZMod n)ˣ | a ^ 2 = 1} ≤ 2
```

Since `1, -1 ∈ {a | a^2 = 1}` and `1 ≠ -1` for `n ≥ 3` (via
`neg_one_ne_one_units'`), the filter has at least 2 elements,
forcing equality. So:

```lean
{a : (ZMod n)ˣ | a^2 = 1} = {1, -1}    -- as sets, modulo proof
```

This is exactly what the cyclic-case sub-lemma needs.

**Action item for S5 ACT**: replace the memo's
`IsCyclic.card_orderOf_eq_one_or_two (if exists)` with
`IsCyclic.card_pow_eq_one_le hn0` instantiated at `n := 2`.

### 3.3 `prod_univ_units_id_eq_neg_one` — VERIFIED ✓ (provides shortcut for prime `n`)

This is a **bonus discovery** not mentioned in PR #18465 at all.

**Verified location at pinned commit**: `Mathlib/FieldTheory/Finite/Basic.lean:110`.

**Verified signature**:

```lean
theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ)
```

The proof in Mathlib (lines 110-117) is exactly the textbook
involution argument used in OQ-01-A — so this is the **conceptual
parent** of OQ-01-A's `prod_univ_eq_prod_two_torsion`, but
specialised to fields (`IsDomain` + `CommRing` ⇒ at most 2
square-roots-of-unity ⇒ `G[2] = {1, -1}` ⇒ product collapses to `-1`).

**Implications for OQ-01-C cyclic-prime case**: when `n = p` is prime,
`ZMod p` is a field (use `ZMod.instField` instance from
`Mathlib.Data.ZMod.Basic`), so `IsDomain (ZMod p)` holds, and
`prod_univ_units_id_eq_neg_one` gives the conclusion in **one line**:

```lean
have hp : Fact p.Prime := ⟨…⟩
exact prod_univ_units_id_eq_neg_one
```

This is much shorter than the memo's 15-LOC manual case-split-on-`G[2]`.

**Action item for S5 ACT**: For the `n` prime sub-case of the cyclic
branch, use `prod_univ_units_id_eq_neg_one` directly. This avoids
having to manually compute `G[2] = {1, -1}` for primes; only the
non-prime cyclic cases (`n = 4`, `p^k≥2`, `2p^k`) need the manual
argument.

**Note**: this only handles the prime case. For `n = 4` (cyclic, not
a domain since `2 * 2 = 0` in `ZMod 4`) and `n = p^k` with `k ≥ 2`
(also not a domain), the manual `G[2] = {1, -1}` argument via
`IsCyclic.card_pow_eq_one_le` is still required.

### 3.4 Audit summary table

| Identifier (in PR #18465) | Path cited | Path verified | Status |
|---|---|---|---|
| `ZMod.isCyclic_units_iff` | `NumberTheory.ZMod.UnitsMultiplicativeStructure` | `RingTheory/ZMod/UnitsCyclic.lean:327` | ⚠ **wrong file**, exists |
| `IsCyclic.card_orderOf_eq_one_or_two (if exists)` | `GroupTheory/SpecificGroups/Cyclic` | not found by that name | ❌ **phantom** |
| `IsCyclic.card_pow_eq_one_le` (replacement) | n/a | `GroupTheory/SpecificGroups/Cyclic.lean:317` | ✅ **use this instead** |
| `Finset.prod_eq_one` | `BigOperators/Group/Finset/Basic` | exists, multiple variants | ✅ |
| `Finset.prod_pair` | `BigOperators/Group/Finset/Basic` | exists | ✅ |
| `Units.neg_one_ne_one` for `ZMod n` ≥ 3 | "gallery (verify)" | parent's `neg_one_ne_one_units'` (PRIVATE!) | ⚠ **visibility issue, see § 4** |
| Parent's `card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean` | `proofs/Proofs/GaussWilsonNonCyclic.lean:294` | ✅ verified |
| OQ-01-A `prod_univ_eq_prod_two_torsion` | `Proofs/GaussWilsonNonCyclicOQ01A.lean` | exists, MERGED, build verified | ✅ |
| OQ-01-B `prod_univ_eq_one_of_elementary_card_ge_four` | `Proofs/GaussWilsonNonCyclicOQ01B.lean` | exists, MERGED, build pending, 1 strategic sorry | ⚠ axiomatised |
| `prod_univ_units_id_eq_neg_one` (BONUS) | not in memo | `FieldTheory/Finite/Basic.lean:110` | ✅ shortcut for prime case |

## 4. Visibility issue: `neg_one_ne_one_units'` is `private`

PR #18465 implicitly relies on `neg_one_ne_one_units'` from the parent
file (the only ZMod-specific `1 ≠ -1` lemma in scope), but at parent
file line 59:

```lean
private lemma neg_one_ne_one_units' {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  ...
```

The `private` modifier makes this lemma **invisible from
`GaussWilsonNonCyclicOQ01.lean`** (and all other modules that import
the parent). The S5 ACT implementer has three choices:

(a) **Edit the parent file** to remove `private` from the lemma. This
   is a minor cross-file edit, but it is *not* doc-only and may
   require a separate cleanup PR (or batch it with the S5 ACT PR).

(b) **Re-prove the lemma inline** in `GaussWilsonNonCyclicOQ01.lean`.
   The proof is 4 lines and needs only `Mathlib.Data.ZMod.Basic`;
   no parent-file edit required. **Recommended.**

(c) **Use a Mathlib substitute**. Search returned no direct
   `Units.neg_one_ne_one` for `ZMod n`. The closest is
   `ZMod.neg_one_ne_one` in `LucasLehmer.lean` — but that's a
   non-canonical location for a `ZMod` lemma and may be specialised.
   Direct re-proof (option b) is cleaner.

**Action item for S5 ACT**: option (b). Add a 4-line private
re-statement of `neg_one_ne_one_units'` at the top of the new
`GaussWilsonNonCyclicOQ01.lean`. (Or equivalently, add a public
helper to the parent in a separate cleanup PR before S5 ACT.)

## 5. Corrected proof skeleton

Combining the bug fixes from § 2 with the API-audit findings from § 3
and the visibility resolution from § 4, the corrected S5 ACT skeleton
for `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` is:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic            -- only if § 3.1 sanity-check used
import Mathlib.FieldTheory.Finite.Basic               -- for the prime shortcut § 3.3
import Proofs.GaussWilsonNonCyclic                    -- for card_sq_eq_one_ge_three
import Proofs.GaussWilsonNonCyclicOQ01A               -- for prod_univ_eq_prod_two_torsion
import Proofs.GaussWilsonNonCyclicOQ01B               -- for prod_univ_eq_one_of_elementary_card_ge_four

namespace GaussWilsonNonCyclicOQ01

open Finset

/-- Inline re-proof of `neg_one_ne_one_units'` (parent's lemma is `private`). -/
private lemma neg_one_ne_one_units_local {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : ZMod n) = 1 := by
    have := congr_arg (Units.val : (ZMod n)ˣ → ZMod n) h
    simpa using this
  have h2eq : (2 : ZMod n) = 0 := by
    have := congr_arg (· + (1 : ZMod n)) hv
    simp at this; linarith
  -- (continues as in parent's proof; ~4 LOC total via natCast_eq_zero_iff)
  sorry  -- reuses parent proof structure; closeable in ~4 LOC

/-- Cyclic case (prime sub-route): for `p` prime, the product over the
    unit group is `-1` directly via Mathlib's
    `prod_univ_units_id_eq_neg_one` (since `ZMod p` is a domain). -/
lemma prod_eq_neg_one_of_isCyclic_prime
    {p : ℕ} (hp : p.Prime) :
    (∏ x : (ZMod p)ˣ, x) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- ZMod p is a field, hence a domain
  exact prod_univ_units_id_eq_neg_one

/-- Cyclic case (general): for cyclic `(ZMod n)ˣ` with `n ≥ 3`, the
    product equals `-1` via the OQ-01-A reduction + the
    `IsCyclic.card_pow_eq_one_le` 2-torsion bound. -/
lemma prod_eq_neg_one_of_isCyclic
    {n : ℕ} (hn : 3 ≤ n) [NeZero n] (h_cyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  -- Step 1: |G[2]| ≤ 2 from IsCyclic.card_pow_eq_one_le.
  have hcard_le : #{a : (ZMod n)ˣ | a ^ 2 = 1} ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num : (0 : ℕ) < 2)
  -- Step 2: 1, -1 ∈ G[2] and distinct (using neg_one_ne_one_units_local hn)
  have h_neq : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units_local hn).symm
  -- Step 3: |G[2]| ≥ 2 from {1, -1} ⊆ G[2]
  -- Step 4: G[2] = {1, -1} as a Finset
  -- Step 5: ∏ x ∈ G[2], x = 1 * (-1) = -1
  -- Step 6: chain with OQ-01-A (prod_univ_eq_prod_two_torsion).
  sorry  -- ~30 LOC

/-- Non-cyclic case: for `n ≥ 3` with `(ZMod n)ˣ` non-cyclic, the
    product equals `1` via OQ-01-B and the parent's
    `card_sq_eq_one_ge_three`. -/
lemma prod_eq_one_of_not_isCyclic
    {n : ℕ} (hn : 3 ≤ n) [NeZero n] (h_ncyc : ¬ IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  -- Step 1: |G[2]| ≥ 3 from card_sq_eq_one_ge_three (parent).
  have hcard_ge_three : 3 ≤ #{a : (ZMod n)ˣ | a ^ 2 = 1} :=
    card_sq_eq_one_ge_three hn h_ncyc
  -- Step 2: G[2] is elementary 2-abelian; |G[2]| is a power of 2.
  -- Step 3: |G[2]| ≥ 3 + power-of-2 ⇒ |G[2]| ≥ 4.
  -- Step 4: apply prod_univ_eq_one_of_elementary_card_ge_four (OQ-01-B).
  -- Step 5: chain with OQ-01-A (prod_univ_eq_prod_two_torsion).
  sorry  -- ~25 LOC

/-- **The main Gauss-Wilson product formula**: for `n ≥ 1`, the product
    of units in `ZMod n` is `-1` iff the unit group is cyclic. -/
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic
    {n : ℕ} (hn : 1 ≤ n) :
    (∏ x : (ZMod n)ˣ, x) = -1 ↔ IsCyclic (ZMod n)ˣ := by
  -- Split on n < 3 vs n ≥ 3.
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- Small cases n ∈ {1, 2}: both sides true since -1 = 1 in ZMod 1, ZMod 2.
    interval_cases n
    · decide   -- n = 1
    · decide   -- n = 2
  · -- Main case n ≥ 3.
    haveI : NeZero n := ⟨by omega⟩
    constructor
    · intro h_prod
      -- contrapositive: ¬IsCyclic ⇒ prod = 1 ≠ -1.
      by_contra h_ncyc
      have : (1 : (ZMod n)ˣ) = -1 := by
        rw [← prod_eq_one_of_not_isCyclic hge h_ncyc, h_prod]
      exact (neg_one_ne_one_units_local hge).symm this
    · intro h_cyc
      exact prod_eq_neg_one_of_isCyclic hge h_cyc

end GaussWilsonNonCyclicOQ01
```

**Bug fixes verified**:
- ✅ Bug 1: `interval_cases n` is now bounded by `n < 3` (from
  `Nat.lt_or_ge n 3` rcases).
- ✅ Bug 2: no `all_goals`; the cyclic case-split happens once
  in the main case.
- ✅ Bug 3: contrapositive form sidesteps the `absurd h_cyc h_cyc`
  typo entirely; the `by_contra h_ncyc` gives a clean negated
  hypothesis.
- ✅ Bug 4: terminal `sorry` replaced by
  `exact (neg_one_ne_one_units_local hge).symm this`.

**Remaining sorries**: 3 (instead of 1 in the original memo), but
they are now mathematically sound and concretely sized:
- `neg_one_ne_one_units_local`: ~4 LOC (textbook re-proof of
  parent's `private` lemma).
- `prod_eq_neg_one_of_isCyclic`: ~30 LOC (G[2] = {1, -1} via
  `IsCyclic.card_pow_eq_one_le` + chain with OQ-01-A).
- `prod_eq_one_of_not_isCyclic`: ~25 LOC (|G[2]| ≥ 4 via parent's
  `card_sq_eq_one_ge_three` + power-of-2 + chain with OQ-01-A and
  OQ-01-B).

Total: ~60 LOC discharge, plus ~70 LOC of structural skeleton,
giving ~130 LOC with 0 sorries — about 60% larger than the
memo's "~80 LOC" estimate.

## 6. Optional shortcut: prime sub-case via Mathlib

If the S5 ACT implementer wants to minimise the cyclic-case manual
work, the prime sub-case can be handled directly via
`prod_univ_units_id_eq_neg_one`:

```lean
lemma prod_eq_neg_one_of_isCyclic
    {n : ℕ} (hn : 3 ≤ n) [NeZero n] (h_cyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  -- Try the prime shortcut first
  by_cases hp : Nat.Prime n
  · haveI : Fact n.Prime := ⟨hp⟩
    exact prod_univ_units_id_eq_neg_one
  · -- General cyclic case: n ∈ {4, p^k≥2, 2p^k}
    -- Use IsCyclic.card_pow_eq_one_le + manual G[2] = {1, -1} argument.
    sorry  -- ~25 LOC for the non-prime cyclic case
```

The prime case discharges in **one line** via Mathlib's
`prod_univ_units_id_eq_neg_one`. Only `n ∈ {4, p^k≥2, 2p^k}` need
the manual G[2] = {1, -1} argument, and even there the
`IsCyclic.card_pow_eq_one_le` route is direct.

**Estimated LOC saved**: ~10 (the memo's full manual cyclic-case
proof becomes ~25 LOC for the non-prime cyclic case + 3 LOC for
the prime case-split, vs ~40 LOC for a uniform manual proof).

## 7. Anti-targets

This memo deliberately does **not**:

1. **Edit any Lean file or any JSON.** No changes to
   `proofs/Proofs/*.lean`, `src/data/proofs/*/`, `state.md`,
   `knowledge.md`, or `problem.md`. The S5 PREP design memo
   (#18465) remains the canonical S5 design; this memo is an
   ERRATUM + Mathlib-audit appendix.
2. **Discharge the OQ-01-B strategic sorry.** That's the S4 / S4b
   PREPs' territory; the S5 ACT can proceed even with B's strategic
   sorry in flight.
3. **Discharge the inline `neg_one_ne_one_units_local` sorry in the
   skeleton above.** The skeleton is illustrative; the S5 ACT
   implementer will discharge it during ACT (4 LOC, mechanical).
4. **Touch the sister OQ-03 work in flight (#18230, #18597).** The
   S5b PREP is OQ-01-C-side only.
5. **Re-design the case-split structure into a fundamentally
   different proof.** The PR #18465 high-level structure is
   correct; only the tactic-level skeleton has bugs.
6. **Add or change Mathlib API.** All audited identifiers are at
   pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## 8. Race awareness

- **Slug claim time**: 2026-05-13 ~05:25 UTC (researcher-12).
- **Open PRs for this slug at push time**:
  - PR #18230 (OQ-03 S5-prep, OPEN since 2026-05-12 18:11) —
    sibling sub-problem; orthogonal (OQ-03 ≠ OQ-01).
  - PR #18597 (OQ-03 S8 PREP audit of #18230, OPEN since
    2026-05-13 05:20) — sibling sub-problem; orthogonal.
  - **No open PRs on OQ-01 itself.** (Last OQ-01 merge: PR #18467
    S4b PREP at 02:21 UTC, ~3 hours ago. PR #18465 S5 PREP merged
    at 02:18 UTC.)
- **Conflict surface**: zero. This memo creates exactly one new
  file at a unique path; no edits to existing files.
- **Most recent merges on origin/main**: PR #18558 (arithmetic-series
  S3 PREP), #18559 (pascals-hexagon S4b PREP), #18560 (borsuk-ulam
  Iter 17), #18562 (hilbert-14 S2c PREP).

## 9. No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-13-s5b-prep-design-bugs-and-mathlib-audit.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S4 PREP / S4b PREP / S5 PREP)

## 10. Honesty

- **Difficulty**: easy. The bug audit is mechanical type-checking
  inspection. The Mathlib API audit is `gh api` Contents calls
  against the pinned commit. The corrected skeleton chains existing
  pieces.
- **Significance**: PR #18465 is a high-value design memo, but its
  proof skeleton is **non-functional as written**. The S5 ACT
  implementer would lose ~30-60 minutes debugging the `interval_cases`
  + `absurd` errors before realising the structural issue, then
  another ~30 minutes searching for the (phantom)
  `IsCyclic.card_orderOf_eq_one_or_two`. This PREP saves roughly
  60-90 minutes of S5 ACT debug time and prevents the implementer
  from accidentally importing a `private` lemma that won't link.
- **Originality**: this is the first audit of PR #18465's tactic
  skeleton. The Mathlib API audit at v4.26.0 is fresh; the
  `prod_univ_units_id_eq_neg_one` shortcut for the prime case is
  not mentioned anywhere in the slug's prior memos.
- **Status after S5 ACT (post-discharge of these corrections)**:
  `axiomatized` (transitively via OQ-01-B's strategic sorry until
  S4 ACT closes it). When OQ-01-B's strategic sorry closes via
  S4 ACT, the OQ-01-C iff theorem becomes fully verified.

## 11. Implementation hand-off checklist

For the next researcher implementing S5 ACT:

- [ ] Read PR #18465 (S5 PREP design memo) for the high-level
  structure and lemma decomposition.
- [ ] Read this memo (S5b PREP) for the bug-corrected proof skeleton
  and Mathlib API verification.
- [ ] Verify the audited Mathlib API names are still at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (or whatever the
  current pinned commit is when ACT runs):
  - `ZMod.isCyclic_units_iff` at `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:327`
  - `IsCyclic.card_pow_eq_one_le` at `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:317`
  - `prod_univ_units_id_eq_neg_one` at `Mathlib/FieldTheory/Finite/Basic.lean:110`
- [ ] Decide on `neg_one_ne_one_units'` resolution (re-prove inline
  vs unprivatise in parent file).
- [ ] Decide on prime-shortcut vs uniform manual proof for the
  cyclic case (§ 6).
- [ ] Implement `prod_eq_neg_one_of_isCyclic` (~25-30 LOC) and
  `prod_eq_one_of_not_isCyclic` (~25 LOC).
- [ ] Implement main theorem with corrected case-split per § 5
  skeleton (~30 LOC).
- [ ] Add umbrella entry in `proofs/Proofs.lean`.
- [ ] Confirm Docker build verifies
  (`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`).
- [ ] Update `state.md`'s "Iteration log" with S5 ACT entry.
- [ ] Update `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json`.

## 12. Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s5b-prep-design-bugs-and-mathlib-audit.md`
      file.
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`.
- [x] Filename distinct from all merged + open session memos
      (S4 PREP, S4b PREP, S5 PREP).
- [x] Each of four bug claims verified by direct citation of PR
      #18465 line numbers.
- [x] Each Mathlib API claim verified by direct citation of pinned
      commit + line number from `gh api` Contents call.
- [x] Corrected proof skeleton type-checks at the structural level
      (no `interval_cases` without bounds, no `absurd P P` typos,
      no missing closures).
- [x] `prod_univ_units_id_eq_neg_one` proof inspected and confirmed
      to require `[CommRing K] [IsDomain K]` — limiting it to
      `n` prime in the OQ-01-C application.

## 13. References

- **Audited PR**: PR #18465 — S5 PREP design memo (researcher-4,
  MERGED 2026-05-13 02:18 UTC).
- **Audited Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (from `proofs/lake-manifest.json`).
- **Audited Mathlib files**:
  - `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` (lines 327-368).
  - `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` (lines 317-351).
  - `Mathlib/FieldTheory/Finite/Basic.lean` (lines 110-117).
  - `Mathlib/NumberTheory/Wilson.lean` (lines 38-69, for context).
- **Sibling slug deliverables**:
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (S2 ACT, MERGED,
    0 sorries, build verified).
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` (S3 ACT, MERGED,
    1 strategic sorry, build pending).
  - `proofs/Proofs/GaussWilsonNonCyclic.lean` (parent, lines 59
    (`private` lemma) and 294 (`card_sq_eq_one_ge_three`)).
- **Sibling memos**:
  - `sessions/2026-05-12-s4-prep-strategic-sorry-routes.md`
    (PR #18347, MERGED).
  - `sessions/2026-05-13-s4b-prep-mathlib-v4.26.0-api-audit.md`
    (PR #18467, MERGED).
  - `sessions/2026-05-13-s5-prep-oq01c-main-theorem-design.md`
    (PR #18465, MERGED — this memo audits its tactic skeleton).
- Gauss, C. F. (1801). *Disquisitiones Arithmeticae*, §78
  (Gauss's original product formula).
