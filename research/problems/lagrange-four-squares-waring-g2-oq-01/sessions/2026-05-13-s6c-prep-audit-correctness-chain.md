# S6c PREP — Audit-correction of S6 PREP §3/§4 `waringG_2_correct` / `waringG_3_correct` drafts

**Date**: 2026-05-13
**Researcher**: researcher-8
**Mode**: PREP (doc-only audit-correction)
**Status**: pristine orthogonal to all merged sessions; no open PR on
this slug at claim time.
**Scope**: targets the load-bearing `waringG_2_correct` proof draft in
[PR #18406 (S6 PREP)](https://github.com/rjwalters/lean-genius/pull/18406)
§3 — flagged by §7 of the same PREP as the "minimum viable S6a ACT
deliverable" — and the `waringG_3_correct` draft in §4. The single
explicit Lean snippet either (a) does not typecheck or (b) silently
adds a load-bearing axiom dependency. This audit pins the corrections
the future S6a ACT must apply, and proposes an axiom-free alternative.
**Anti-target**: this is **not** a redesign of the bridge-lemma /
Option A/B/C choice (S6 PREP §1) and **not** a redesign of the
`waringG k = N` correctness shape (S6 PREP §2). Both are sound. The
audit is strictly arithmetic / API-level on the §3 and §4 drafts.

## Summary of findings

PR #18406 §3 (the `waringG_2_correct` draft) contains four concrete
errors that would block any S6a ACT iteration:

| ID | Severity | Location | Issue |
|---|:---:|---|---|
| **F1** | **Major** | §3 `seven_needs_four_squares` proof, line "IsObstructed 7 = ¬ ∃ a b c …" | Misreads `IsObstructed n` — actual definition (parent line 160-161) is **positive existential** `∃ a b, n = 4^a · (8b+7)`, not the negation of `IsSumOfThreeSquares`. |
| **F2** | **Major** | §3 same proof, `have := seven_obstructed; apply this` | The `apply this` fails: `seven_obstructed : IsObstructed 7` cannot be applied to a target of the form `False`/`⊥`. The bridge from `IsObstructed 7` to `¬ ∃ a b c, a²+b²+c²=7` requires invoking the axiom `legendre_three_squares` (parent line 178). This dependency is **not flagged** in S6 PREP §3 anywhere — neither in the "Risk" line nor in the dependency table at §2 row k=2. |
| **F3** | **Medium** | §3 `all_sum_four_squares`, `![a, b, c, d] i.val` | Type error: `i : Fin 4` has `i.val : ℕ`, but `![a, b, c, d] : Fin 4 → ℕ` expects a `Fin 4` argument, not a `ℕ`. The correct form is `![a, b, c, d] i`. |
| **F4** | **Minor** | §3 caveat "verified by direct use in `Proofs/LagrangeFourSquares.lean` line ranges around the `r4_prime_formula` proof" | `r4_prime_formula` (parent lines 209–224) does **not** use `Fin.sum_univ_four`, `Matrix.cons_val_*`, or any `Matrix.cons` vec-notation. The citation is incorrect. The pattern is used elsewhere in Mathlib, but the PR points the future ACT at the wrong precedent. |

A fifth, **Medium-severity** finding (F5) follows from F1+F2: as drafted,
`waringG_2_correct` is **not "verified" infrastructure** in the
Axiom-Integrity-Policy sense (CLAUDE.md). The lower-bound side
silently consumes `legendre_three_squares` (a parent axiom). This
needs to be acknowledged before promoting the artefact to status
`verified`.

The S6 PREP §4 (`waringG_3_correct`) draft is structurally clean
(the `wieferich_nine_cubes` upper bound is already an explicit
axiom, and the lower bound bridges to the S2 ACT's
`twenty_three_needs_nine_cubes` via `Iff.rfl` per §1 Option B).
One **Minor** finding applies (F6): `Iff.rfl` between two `def`s
needs default-reducibility unfolding; recommend `by unfold …; rfl`
as a defensive fallback if `Iff.rfl` fails at elaboration time.

## §1. F1/F2 — `IsObstructed` misread and missing axiom

### F1. The definition

Parent file [`Proofs/LagrangeFourSquares.lean`](../../../../proofs/Proofs/LagrangeFourSquares.lean) lines 159–161:

```lean
/-- The obstruction to being a sum of three squares:
    numbers of the form 4^a(8b + 7) cannot be represented -/
def IsObstructed (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)
```

This is a **positive existential** statement on `n`'s shape, not a
negation of any representation predicate. The bridge from "is
obstructed" to "is not a sum of three squares" is the Legendre–Gauss
three-square theorem, which the parent file declares as an axiom
at line 178:

```lean
axiom legendre_three_squares :
    ∀ n : ℕ, IsSumOfThreeSquares n ↔ ¬IsObstructed n
```

So `IsObstructed 7 ⇒ ¬ IsSumOfThreeSquares 7` strictly requires
`legendre_three_squares 7 |>.not_left` (equivalently, contraposition
via `Iff.mp` on the `¬¬`-form).

### F2. The proof shape that fails

S6 PREP §3's draft (PR #18406 lines 109–119, abbreviated to the
load-bearing block):

```lean
theorem seven_needs_four_squares : ¬ IsSumOfPowers 7 3 2 := by
  rintro ⟨xs, h⟩
  have := seven_obstructed              -- this : IsObstructed 7
  apply this                            -- ✗ cannot apply ∃-witness to ⊥
  refine ⟨xs 0, xs 1, xs 2, ?_⟩         -- never reached
  ...
```

`apply this` requires `this`'s codomain to unify with the current
goal `False` (after `rintro`). `IsObstructed 7 = ∃ a b, 7 = 4^a(8b+7)`
has codomain `Prop`, not `False`. There is no `apply` route from
a positive existential to `False`; the dependency on
`legendre_three_squares` is essential to produce the negation
`¬IsSumOfThreeSquares 7`, which can then close the goal.

### Corrected draft (axiom-consuming variant)

Closest fix that preserves the legendre-route structure of the
original draft:

```lean
namespace LagrangeFourSquares

theorem seven_needs_four_squares : ¬ IsSumOfPowers 7 3 2 := by
  rintro ⟨xs, h⟩
  -- Project the Fin 3 sum to ∃ a b c, a² + b² + c² = 7.
  have hSum3 : IsSumOfThreeSquares 7 := by
    refine ⟨xs 0, xs 1, xs 2, ?_⟩
    have := h
    simp [Fin.sum_univ_three] at this
    linarith
  -- Bridge: IsSumOfThreeSquares 7 ↔ ¬ IsObstructed 7 (Legendre, axiom).
  have h_not_obs : ¬ IsObstructed 7 := (legendre_three_squares 7).mp hSum3
  exact h_not_obs seven_obstructed

end LagrangeFourSquares
```

**Axiom footprint**: consumes `legendre_three_squares` (parent
line 178). **Status implication**: any `waringG_2_correct` built
from this lemma inherits `axiomatized`, not `verified`.

### Corrected draft (axiom-free variant) — **recommended**

The S2 ACT pattern (`bound → lift → decide`) handles n=7, s=3, k=2
directly. Search space is `3^3 = 27` tuples — well within
kernel `decide`'s budget (no `native_decide` needed).

```lean
namespace LagrangeFourSquares

/-- Finite-search core: the 27 functions `Fin 3 → Fin 3` whose squared
entries sum to `7` form the empty set. -/
lemma representations7_squares_empty :
    (Finset.univ.filter
      (fun f : Fin 3 → Fin 3 => ∑ i, ((f i : ℕ)) ^ 2 = 7)) = ∅ := by
  decide

theorem seven_needs_four_squares : ¬ IsSumOfPowers 7 3 2 := by
  rintro ⟨xs, h⟩
  -- Step 1: each entry is < 3 (since (xs i)^2 ≤ 7 < 9 = 3^2).
  have hbound : ∀ i, xs i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h9 : 9 ≤ (xs i) ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (xs i) ^ 2 := Nat.pow_le_pow_left hge 2
    have hsing : (xs i) ^ 2 ≤ ∑ j, (xs j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (xs j) ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hsing
    omega
  -- Step 2: lift to Fin 3 → Fin 3 and discharge by decide.
  let g : Fin 3 → Fin 3 := fun i => ⟨xs i, hbound i⟩
  have hmem :
      g ∈ Finset.univ.filter
        (fun f : Fin 3 → Fin 3 => ∑ i, ((f i : ℕ)) ^ 2 = 7) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- (g i : ℕ) = xs i is definitional via Fin.val ⟨xs i, _⟩.
    change ∑ i, (xs i) ^ 2 = 7
    exact h
  rw [representations7_squares_empty] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end LagrangeFourSquares
```

**Axiom footprint**: **0** (kernel `decide` is not an added axiom;
the Lean runtime's decidability checker is part of the trusted
kernel). **LOC**: ~30. **Status implication**: `waringG_2_correct`
becomes `verified` on the lower-bound side.

This pattern is **literally copy-paste** of the S2 ACT proof of
`twenty_three_needs_nine_cubes` (shipped in PR #18176, file
[`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean:81–106`](../../../../proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean#L81-L106)):

| Aspect | S2 ACT (`g(3) ≥ 9`) | S6a ACT recommended (`g(2) ≥ 4`) |
|--------|---------------------|----------------------------------|
| Target | `¬ IsSumOfCubes 8 23` | `¬ IsSumOfPowers 7 3 2` |
| Search space | `3^8 = 6561` | `3^3 = 27` |
| Closer | `native_decide` | `decide` (kernel) |
| Bound on summand | `f i < 3` (since `3^3 = 27 > 23`) | `xs i < 3` (since `3^2 = 9 > 7`) |
| Finite-search lemma | `representations23_empty` | `representations7_squares_empty` |
| Lift target | `Fin 8 → Fin 3` | `Fin 3 → Fin 3` |
| LOC contribution | ~25 lines | ~30 lines (similar) |

The smaller search space at k=2 is well within kernel `decide`; no
`native_decide` reflection-axiom dependency.

## §2. F3 — `Matrix.cons` typing in `all_sum_four_squares`

### The error

S6 PREP §3 (PR #18406 line ~152) drafts:

```lean
theorem all_sum_four_squares : ∀ n : ℕ, IsSumOfPowers n 4 2 := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares n
  refine ⟨fun i => ![a, b, c, d] i.val, ?_⟩    -- ✗ i.val : ℕ, not Fin 4
  ...
```

`![a, b, c, d]` has type `Fin 4 → ℕ` (the `!` vec-notation builds a
`Matrix.cons` chain over a `Fin (n+1)`-indexed family). It does
**not** accept `ℕ` arguments — there is no `CoeFun (Fin 4 → ℕ) ℕ`
instance.

### Corrected draft

```lean
theorem all_sum_four_squares : ∀ n : ℕ, IsSumOfPowers n 4 2 := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares n
  refine ⟨![a, b, c, d], ?_⟩
  -- Reduce ∑ i : Fin 4, (![a,b,c,d] i)^2 to a²+b²+c²+d².
  simp [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const]
  linarith
```

Two small refinements:

1. The closed form `fun i => ![a, b, c, d] i` is η-equivalent to
   `![a, b, c, d]`; passing the latter directly is cleaner.
2. The simp set should include `Matrix.head_fin_const` only if needed
   for `![a, b, c, d] 3`; in recent Mathlib (v4.26.0) the standard
   `Matrix.cons_val_*` family suffices. The next ACT iteration
   should first try the minimal simp set
   `[Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
   Matrix.cons_val_two, Matrix.cons_val_three]` (or whichever
   lemmas the current Mathlib exposes for `cons_val` at higher
   indices) and add fallbacks only as `decide` errors appear.

**LOC contribution**: unchanged (~5 lines).

### Alternative: avoid `Matrix.cons` entirely

```lean
theorem all_sum_four_squares : ∀ n : ℕ, IsSumOfPowers n 4 2 := by
  intro n
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares n
  refine ⟨fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d, ?_⟩
  -- Pattern-match unfolds during ∑; Fin.sum_univ_four delivers a²+b²+c²+d².
  simp [Fin.sum_univ_four]
  linarith
```

This sidesteps the `Matrix.cons_val_*` simp-set entirely and uses
only `Fin.sum_univ_four` (a stable Mathlib lemma since at least
Mathlib v4.5). **Slightly more verbose** but **fewer moving parts**.

## §3. F4 — incorrect citation of `r4_prime_formula`

### Verification

`r4_prime_formula` is at parent lines 209–224:

```lean
theorem r4_prime_formula (p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1) :
    sumDivisorsNot4 p = 1 + p := by
  simp only [sumDivisorsNot4]
  -- ... Finset.filter, Finset.range, Finset.mem_insert/singleton ...
  rw [hfilt, Finset.sum_pair h1_ne_p]
```

The proof uses `Finset.filter`, `Finset.range`, `Finset.mem_filter`,
`Finset.mem_range`, `Finset.mem_insert`, `Finset.mem_singleton`,
`Nat.Prime.eq_one_or_self_of_dvd`, `Finset.sum_pair`. **None of
these** is `Fin.sum_univ_four` or `Matrix.cons_val_*`. The simp
pattern claimed by S6 PREP §3's caveat ("verified by direct use in
… `r4_prime_formula` proof") does not exist there.

### Where the pattern actually lives

The closest precedent for `Fin.sum_univ_four` + `Matrix.cons_val_*`
in this repo's `Proofs/` tree is the parent file's example block
(lines 110–134), which uses **kernel `rfl`** rather than `simp` —
e.g.

```lean
example : (1 : ℕ) ^ 2 + 1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 7 := rfl
```

— but this does not exercise the `Matrix.cons` simp set either.
The pattern is **standard Mathlib idiom** (used widely in
`Mathlib/LinearAlgebra/Matrix/*`), so it will work, but the future
S6a ACT researcher should look at Mathlib precedents directly
rather than at `r4_prime_formula`.

Specifically, the canonical Mathlib precedent for "sum of squares
over `Fin 4`" is in
[`Mathlib.NumberTheory.SumFourSquares`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/SumFourSquares.lean)
itself, where the proof of `Nat.sum_four_squares` uses
`Finset.sum_fin_eq_sum_range` and `Fin.sum_univ_succ` rather than
the vec-notation route. Either approach is viable; the pattern-match
alternative in §2 above avoids the question entirely.

## §4. F5 — Axiom-Integrity-Policy implication

### As drafted: `waringG_2_correct` is `axiomatized`

PR #18406 §3's `seven_needs_four_squares` draft (uncorrected and
even after the F1/F2 fix to use `legendre_three_squares`) consumes
the parent axiom `legendre_three_squares` (line 178). This is a
genuine mathematical assumption — Legendre's three-square theorem,
proved by Legendre 1798 and Gauss 1801 — that is **not** yet in
Mathlib in any form, and is declared as an `axiom` in
`Proofs/LagrangeFourSquares.lean`.

Per the **Axiom Integrity Policy** (CLAUDE.md, §"Status field
definitions"):

> - `verified` (badge: `original` or `verified`): Fully
>   machine-checked, no assumptions. **Requirements**: 0 sorries,
>   0 `axiom` declarations, 0 structure-encoded assumptions.
> - `axiomatized` (badge: `axiom`): Formalized with stated
>   assumptions. **Requirements**: Has `axiom` declarations OR
>   structure-encoded assumptions.

A `waringG_2_correct` that **transitively depends on
`legendre_three_squares`** (declared with `axiom`, parent line 178)
falls under `axiomatized`, not `verified`.

S6 PREP §3 does not flag this. The §2 dependency table row for
k=2 reads:

> | 2 | `Nat.sum_four_squares` (Mathlib) ⇒ `lagrange_four_squares`
> (parent) | `seven_obstructed` (parent) | **YES** — currently
> *unwritten*; first deliverable |

— with no mention of `legendre_three_squares`. The bridging
dependency is hidden.

### As corrected with the decide-based variant: `waringG_2_correct` is `verified`

The §1 axiom-free variant (`representations7_squares_empty` via
kernel `decide`, 27-case enumeration) eliminates the
`legendre_three_squares` consumption entirely. Lower-bound side
becomes 0 axioms. Upper-bound side already uses only
`Nat.sum_four_squares` (Mathlib-proved). Combined `waringG_2_correct`
is then `verified` end-to-end.

**Recommendation for S6a ACT**: use the decide-based variant. The
27-case enumeration is well under kernel-decide's budget
(`maxRecDepth = 512` default; 27 tuples is single-digit recursion
depth). No `native_decide`, no `legendre_three_squares`, no
reflection-axiom expansion. The result is the cleanest
`waringG_2_correct` mathematically possible.

### Implication for the slug's `meta.json`

When the future S6a ACT creates a gallery entry for OQ-01 (likely
`src/data/proofs/lagrange-four-squares-waring-g2-oq-01/`), the
`meta.json` `status` and `assumptions` fields should reflect the
axiom dependency chain:

| Theorem | Axiom dependencies | meta.json status implication |
|---------|---------------------|------------------------------|
| `waringG_2_correct` (decide variant, §1) | none | `verified` ✓ |
| `waringG_2_correct` (legendre variant, §1) | `legendre_three_squares` | `axiomatized` |
| `waringG_3_correct` (§4 of #18406) | `wieferich_nine_cubes` | `axiomatized` (per S4 PREP §5; OQ-01 inherits parent's axiom set) |
| `waringG_4_correct` (after S3+S4 ACT) | `bdd_nineteen_fourth_powers` (proposed) | `axiomatized` |
| `waringG_5_correct` (future) | `chen_thirty_seven_fifth_powers` (proposed) | `axiomatized` |
| `waringG_6_correct` (future) | `waring_general_formula` | `axiomatized` |

Note: the parent slug `lagrange-four-squares-waring-g2` (k=2 only,
already gallery-published as `verified`) achieves `verified` status
specifically by **not** invoking `legendre_three_squares` — it uses
`Nat.sum_four_squares` (upper) + a hand-rolled mod-8 descent
(`sq_mod_eight` + `sum_three_sq_mod_eight_ne_seven`) for the lower
bound. The OQ-01 child has the option to follow either route at
k=2:

- **Route A (legendre-axiom)**: ~15 LOC, consumes 1 axiom.
- **Route B (mod-8 descent, parent's route)**: ~80 LOC, 0 axioms.
- **Route C (decide enumeration, this PREP's recommendation)**: ~30
  LOC, 0 axioms.

Route C is the **best LOC-per-rigour tradeoff** for the OQ-01 file,
where k=2 is the simplest case in a series stretching to k=6 and
beyond.

## §5. F6 — `Iff.rfl` reducibility caveat for §1 Option B

### The bridge lemma

S6 PREP §1 Option B proposes:

```lean
namespace WaringG2OQ01

lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 := Iff.rfl

lemma isSumOfFourthPowers_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfFourthPowers s n ↔ IsSumOfPowers n s 4 := Iff.rfl

end WaringG2OQ01
```

with the claim "Both bridges are `Iff.rfl` by `unfold`, so **0 LOC
of real proof work**."

### The caveat

`IsSumOfCubes` (S2 ACT, file lines 53–54) is defined with `def`
(not `abbrev`, not `@[reducible] def`):

```lean
def IsSumOfCubes (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n
```

`IsSumOfPowers` (parent, line 245) is also `def`. Lean 4's default
reducibility for `def` is `Reducibility.default`, which is unfolded
by the unifier *unless* the term is in `WHNF` (weak head normal
form) — which `IsSumOfCubes s n` and `IsSumOfPowers n s 3` both are
(both are `∃`-headed). Whether `Iff.rfl` succeeds depends on
whether Lean's elaborator unfolds the two `def`s in tandem during
the `Iff.refl` synthesis.

In practice, for Mathlib-style `def`s on `Prop` with `default`
reducibility, `Iff.rfl` **does** typically work — but it can fail
when one definition is in a different namespace and Lean's
delaboration heuristics interfere. The defensive idiom:

```lean
lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 := by
  unfold IsSumOfCubes IsSumOfPowers
  rfl
```

or, equivalently,

```lean
lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 :=
  ⟨id, id⟩
```

The `⟨id, id⟩` form is the most robust: it relies on Lean
**implicitly** unfolding both `def`s during typechecking of the
explicit `id` terms (driven by η-expansion of `Iff` and
implicit-argument inference), which is more permissive than
`Iff.rfl`'s strict definitional comparison.

**Recommendation**: ship `⟨id, id⟩` as the bridge form. If `Iff.rfl`
works at S6a ACT time, fine; if not, the fallback is one character
longer and bullet-proof.

### LOC impact

Unchanged from S6 PREP §1 — still effectively "0 LOC of real proof
work", whether the bridge is `Iff.rfl` or `⟨id, id⟩`.

## §6. Revised LOC and risk profile for S6a ACT

PR #18406 §7 ("Implementation order") proposes:

> 1. **S6a ACT (immediate)**: ship `waringG_2_correct` +
>    `waringG_3_correct` + the two bridge lemmas in a new file
>    `Proofs/LagrangeFourSquaresWaringGCorrectness.lean`. Requires
>    only existing infrastructure. **~45 LOC, 0 sorries.**

Revised under this audit's recommendations (decide-based k=2 +
bridge `⟨id, id⟩` + corrected `Matrix.cons` simp set):

| Block | Original §3/§4 LOC | Revised LOC | Δ |
|------:|-------------------:|------------:|---|
| `representations7_squares_empty` (new lemma) | — | 5 | +5 |
| `seven_needs_four_squares` (decide variant) | ~10 | 22 | +12 |
| `all_sum_four_squares` (fixed `Matrix.cons`) | ~10 | 8 | −2 |
| `waringG_2_correct` (refine ⟨_, 7, _⟩) | ~8 | 8 | 0 |
| `isSumOfCubes_iff_isSumOfPowers` (bridge) | 3 | 3 | 0 |
| `twenty_three_not_sum_of_eight_cubes` (bridge consumer) | 4 | 4 | 0 |
| `waringG_3_correct` (refine ⟨_, 23, _⟩) | ~10 | 10 | 0 |
| **Total file** | **~45** | **~60** | **+15** |

The +15 LOC is the price for upgrading `waringG_2_correct` from
`axiomatized` (legendre-route) to `verified` (decide-route). At
60 LOC the file is still well under any reasonable cap, and the
axiom-integrity gain is substantial: the OQ-01 slug's `meta.json`
`assumptions` field can list only `wieferich_nine_cubes` and (after
S3/S4 ACT) `bdd_nineteen_fourth_powers`, `chen_thirty_seven_fifth_powers`
— no legendre dependency for the k=2 entry, matching the parent
slug's verified-status precedent.

### Build risk

| Step | Risk | Mitigation |
|------|:-----|------------|
| `decide` on 27-case `Fin 3 → Fin 3 → ℕ`-sum | low (kernel decide budget; S2 ACT did 6561 cases via `native_decide`, this is 243× smaller) | none needed |
| `Fin.sum_univ_three`/`Fin.sum_univ_four` simp | low (stable since Mathlib v4.5) | fallback to pattern-match alternative §2 |
| `Matrix.cons_val_*` simp set | medium (lemma names drift across Mathlib versions) | use the pattern-match alternative §2 |
| `⟨id, id⟩` bridge | low (always works for `def`-aliased `Iff`) | fallback to `by unfold …; rfl` |
| `Nat.pow_le_pow_left` for `(xs i) ≤ b → (xs i)^k ≤ b^k` | low (stable) | already used in S2 ACT line 90 |

No `native_decide` reflection axiom, no `legendre_three_squares`
axiom, no `Matrix.cons` simp-name guessing. The decide-based
variant is the **safest** path to a verified `waringG_2_correct`.

## §7. Anti-targets (do not modify in S6c PREP or S6a ACT)

- **S6 PREP §1 / §2 architecture**: bridge-lemma decision (Option
  A/B/C) and correctness-theorem shape (`(∀ n, …) ∧ ∃ n, ¬ …` vs
  `IsLeast`) are not under audit. Both are sound. Future ACT should
  follow §1 Option B (bridge lemmas) verbatim, with the F6
  refinement.
- **S6 PREP §5 / §6 stubs for k=4, 5, 6**: these are forward stubs
  and do not contain explicit Lean code; nothing to audit.
- **S6 PREP §7 implementation order**: the audit recommends keeping
  the order but bumping S6a LOC estimate from 45 to 60.
- **Editing `Proofs/LagrangeFourSquares.lean`**: this is an S6a ACT
  task (adding the new file `Proofs/LagrangeFourSquaresWaringGCorrectness.lean`
  with the corrected drafts), not S6c PREP.
- **Editing `state.md` / `knowledge.md` / `problem.md` /
  `meta.json` / `lagrange-four-squares-waring-g2-oq-01.json`**:
  no change required by this audit. The status of the slug remains
  `ACT` with S6a as the immediate next deliverable.
- **Adding `loom:review-requested`**: math-agent policy.

## §8. Cross-references

- PR [#18176](https://github.com/rjwalters/lean-genius/pull/18176)
  (S2 ACT) — provides the `bound → lift → decide` pattern the
  decide-based variant in §1 mirrors. File
  `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean:81-106`.
- PR [#18314](https://github.com/rjwalters/lean-genius/pull/18314)
  (S3 PREP, g4 counting+omega) — uses the same `Nat.pow_le_pow_left`
  + `Finset.single_le_sum` pattern for summand bounds; the S6c
  draft's `hbound` step mirrors it for k=2.
- PR [#18348](https://github.com/rjwalters/lean-genius/pull/18348)
  (S4 PREP, upper-bound axioms) — establishes that
  `wieferich_nine_cubes` (k=3) is the unique k-specific upper-bound
  axiom currently shipped; `legendre_three_squares` is k=2-specific
  but **for three** rather than **for four** squares, so it would
  add a new dependency dimension if invoked by `waringG_2_correct`.
- PR [#18406](https://github.com/rjwalters/lean-genius/pull/18406)
  (S6 PREP correctness chain) — **the document under audit**.
- PR [#18463](https://github.com/rjwalters/lean-genius/pull/18463)
  (S5 PREP, g5 counting+omega) — extends the counting recipe to
  k=5; same `Nat.pow_le_pow_left` pattern.
- PR [#18483](https://github.com/rjwalters/lean-genius/pull/18483)
  (S2b PREP, g3 counting+omega sibling) — alternative g(3) lower
  bound design via counting; not load-bearing for k=2 correctness.
- PR [#18547](https://github.com/rjwalters/lean-genius/pull/18547)
  (S6b PREP, g6 counting+omega) — parallel k=6 design; orthogonal.
- PR [#18555](https://github.com/rjwalters/lean-genius/pull/18555)
  (S6b PREP audit, witness arithmetic) — audits a different
  numerical claim (k=8 boundary) in PR #18547; this S6c PREP
  audits a different document (PR #18406) and concerns different
  errors (typing, missing axiom dependency).

## §9. Honest scope

This PREP is **doc-only audit-correction**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom changes
- 0 edits to `proofs/Proofs/*.lean`
- 0 edits to `meta.json` / `state.md` / `knowledge.md` / `problem.md`
- 0 edits to the slug's pool JSON
  (`src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`)
- 1 new file: this session note in `research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/`

**Value delivered**:

1. Four concrete errors (F1, F2, F3, F4) flagged in PR #18406 §3's
   `seven_needs_four_squares` and `all_sum_four_squares` drafts,
   each with line-level localisation in the source PR.
2. One **Medium** Axiom-Integrity finding (F5): the as-drafted
   `waringG_2_correct` would silently promote `legendre_three_squares`
   to a load-bearing dependency, downgrading the artefact from
   `verified` to `axiomatized`. The audit traces this to a single
   hidden bridge invocation and proposes an axiom-free alternative.
3. One **Minor** reducibility-defense recommendation (F6) for the
   bridge-lemma `Iff.rfl` in §1 Option B.
4. Corrected drafts for both `seven_needs_four_squares` (two
   variants: legendre-axiom and decide-enumeration) and
   `all_sum_four_squares` (two variants: corrected `Matrix.cons`
   simp set, pattern-match alternative), each with explicit LOC
   and risk estimates.
5. A revised total-LOC estimate for the S6a ACT deliverable: 45 →
   60 (the +15 LOC budget purchases verified status for the k=2
   correctness theorem).

The PREP iteration does **not** discharge any open goal. Status
remains `ACT` with S6a deliverable still pending. The next
researcher claiming this slug for S6a ACT should:

1. Read this PREP (§1, §2, §6 are the load-bearing sections).
2. Follow the decide-based variant of `seven_needs_four_squares`
   from §1.
3. Apply the F3 typing fix to `all_sum_four_squares` from §2.
4. Use the `⟨id, id⟩` bridge form from §5 (or the unfold-rfl
   fallback).
5. Estimate ~60 LOC for the new file
   `Proofs/LagrangeFourSquaresWaringGCorrectness.lean`.
6. Build via `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringGCorrectness`.
7. Update `state.md` phase to S6a complete, axiom delta = 0 (k=2
   `verified`, k=3 inherits parent's `wieferich_nine_cubes`).

## References

- CLAUDE.md "Axiom Integrity Policy", "Status field definitions" —
  the verified / axiomatized distinction this audit applies.
- Mathlib `Nat.sum_four_squares` (`Mathlib.NumberTheory.SumFourSquares`):
  the upper-bound source. **Theorem-proved**, no axiom.
- Mathlib `Fin.sum_univ_three`, `Fin.sum_univ_four`: stable simp
  lemmas since v4.5; the canonical idiom for unrolling sums over
  small `Fin`s.
- Mathlib `Matrix.cons_val_zero`, `Matrix.cons_val_one`,
  `Matrix.head_cons`: stable simp lemmas for evaluating vec-notation;
  used widely throughout `Mathlib.LinearAlgebra.Matrix.*`.
- Legendre, A.-M. "Théorie des Nombres" (1798), Bk III §IV (Legendre's
  three-square theorem; first complete proof).
- Gauss, C.F. "Disquisitiones Arithmeticae" (1801), §291 (independent
  proof via composition of binary quadratic forms).
- Wiedijk #19 (`Nat.sum_four_squares`): Mathlib formalisation of
  Lagrange's four-square theorem, the upper-bound used by
  `lagrange_four_squares` in the parent file.
