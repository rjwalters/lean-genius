# S6 PREP — `waringG k = N` correctness-chain bridging lower/upper bounds

**Date**: 2026-05-12
**Researcher**: researcher-12
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to all prior PRs for this slug
(#18152 S1 OBSERVE merged, #18176 S2 ACT merged, #18314 S3 PREP
merged, #18335 S4 PREP merged)

## Why this PREP, why now

The slug currently has four merged deliverables but **no end-to-end
correctness theorem** for any `k ≥ 3`. Specifically:

- **S2 ACT** (#18176) shipped `WaringG2OQ01.twenty_three_needs_nine_cubes
  : ¬ IsSumOfCubes 8 23` — but `IsSumOfCubes` is a **local
  definition** in the `WaringG2OQ01` namespace, not the
  parent's `IsSumOfPowers`.
- **S3 PREP** (#18314) designs `g4_lower : ¬ IsSumOfFourthPowers 18 79`
  — but, again, plans a **local definition** `IsSumOfFourthPowers`
  rather than reusing `IsSumOfPowers n 18 4`.
- **S4 PREP** (#18335) proposes two new axioms
  `bdd_nineteen_fourth_powers` and `chen_thirty_seven_fifth_powers`
  using the parent's `IsSumOfPowers n s k` predicate.
- Parent's `waringG k : ℕ` is **match-defined** at lines 249–259 of
  `Proofs/LagrangeFourSquares.lean`. `lagrange_is_waring_2 :
  waringG 2 = 4 := rfl` is *purely definitional* — it does **not**
  semantically certify that 4 is the smallest `s` such that every
  `n : ℕ` is a sum of `s` squares.

**The gap.** The definitional bridge between
- `WaringG2OQ01.IsSumOfCubes` (S2 ACT, local) and
- `IsSumOfPowers _ _ 3` (parent, public)
is **missing**, so the lower-bound deliverable from S2 ACT cannot be
*directly* combined with the upper-bound axiom
`wieferich_nine_cubes : ∀ n, IsSumOfPowers n 9 3` to derive
`waringG 3 = 9` as a *correctness* statement (i.e. as a witness that
`waringG 3` matches its semantic characterisation).

This S6 PREP scopes the **correctness chain** that closes the gap:
bridge lemmas + per-k correctness theorems + implementation order.

## 1. Definitional zoo — current state

The repo currently exposes three "is-a-sum-of-k-th-powers"
predicates across the slug:

| Predicate | Scope | Signature | Source |
|-----------|-------|-----------|--------|
| `IsSumOfPowers` | global | `(n s k : ℕ) → Prop` | `Proofs/LagrangeFourSquares.lean:245` |
| `WaringG2OQ01.IsSumOfCubes` | local | `(s n : ℕ) → Prop` | `Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT) |
| `WaringG2OQ01.IsSumOfFourthPowers` | local | `(s n : ℕ) → Prop` | S3 PREP design (#18314 §"Lean realisation"), not yet shipped |

Note the **argument-order mismatch**: parent uses `(n s k)`, S2 ACT
uses `(s n)`. Both definitions unfold to
`∃ f : Fin s → ℕ, ∑ i, (f i) ^ k = n`, so the predicates are
literally identical up to argument order and the fixed `k = 3` / `k = 4`.

Three options for unification:

### Option A — Rewrite S2/S3 ACTs to use parent's `IsSumOfPowers`

Drop `IsSumOfCubes` / `IsSumOfFourthPowers` entirely. Restate
`twenty_three_needs_nine_cubes` as
`¬ IsSumOfPowers 23 8 3`. Direct, but **invasive** — requires
amending the S2 ACT file post-merge (a doctor / mechanic task) and
rebasing the S3 PREP design memo.

### Option B — Add bridge lemmas, keep local defs

Ship a single `Bridges` lemma block:

```lean
namespace WaringG2OQ01

lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 := Iff.rfl

lemma isSumOfFourthPowers_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfFourthPowers s n ↔ IsSumOfPowers n s 4 := Iff.rfl

end WaringG2OQ01
```

Both bridges are `Iff.rfl` by `unfold`, so **0 LOC of real proof
work**. Pedagogically clear and **non-invasive**.

### Option C — Inline the bridge in each correctness theorem

Skip the bridge lemmas; spell out
`twenty_three_needs_nine_cubes` ⇒ `¬ IsSumOfPowers 23 8 3` inline
inside the `waringG_3_correct` proof via `show ... from h`. Saves
the named lemma but **clutters** the correctness theorem.

### Recommendation

**Option B.** The bridge lemmas cost ~5 LOC total (definitional
`Iff.rfl`), keep S2/S3 ACT files immutable, and document the
unification explicitly. They serve as the contract surface between
the slug's local predicates and the parent's public API.

## 2. Correctness theorems — target shapes

For each `k`, the natural correctness statement is a **two-sided
bound** witnessing that `waringG k` matches its semantic
characterisation:

```lean
theorem waringG_k_correct :
    -- Upper bound: every n is a sum of (waringG k) k-th powers.
    (∀ n : ℕ, IsSumOfPowers n (waringG k) k) ∧
    -- Lower bound: there exists an n that is NOT a sum of
    -- (waringG k - 1) k-th powers.
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG k - 1) k)
```

Equivalently in `IsLeast` form (closer to the textbook definition):

```lean
theorem waringG_k_isLeast :
    IsLeast { s : ℕ | ∀ n : ℕ, IsSumOfPowers n s k } (waringG k)
```

The `IsLeast` form is **standard Mathlib** (`Mathlib.Order.Bounds.Basic`)
and unwraps to the same two conjuncts. Both forms are useful; ship
the conjunction form per-k and a separate `IsLeast` adapter.

### Per-k availability (after S2/S3 ACT and existing axioms)

| `k` | Upper bound source | Lower bound source | Correctness derivable? |
|---:|-------------------|--------------------|------------------------|
| 2 | `Nat.sum_four_squares` (Mathlib) ⇒ `lagrange_four_squares` (parent) | `seven_obstructed` (parent) | **YES** — currently *unwritten*; first deliverable |
| 3 | `wieferich_nine_cubes` (parent axiom, line 271) | `twenty_three_needs_nine_cubes` (S2 ACT, MERGED) | **YES** — *blocked* on bridge lemma + waringG-3 conjunction |
| 4 | **GAP** (S4 PREP proposes `bdd_nineteen_fourth_powers`) | `seventy_nine_needs_nineteen_fourth_powers` (S3 PREP design, **not yet shipped**) | **blocked** on both S3 ACT and S4 ACT axioms |
| 5 | **GAP** (S4 PREP proposes `chen_thirty_seven_fifth_powers`) | not yet designed | **blocked** on lower + upper |
| 6 | `waring_general_formula 6` (parent axiom, $k \ge 6$ formula) | not yet designed | **blocked** on lower bound |
| ≥ 7 | same axiom | not yet designed | **blocked** |

**Immediate harvest**: `waringG_2_correct` and `waringG_3_correct`
can be shipped *immediately* (k=2 from existing parent infra, k=3
after adding the bridge lemma). These two correctness theorems are
**the minimum viable S6 deliverable**.

## 3. `waringG_2_correct` (k = 2) — full draft

The k=2 case uses only parent-file infrastructure:

```lean
namespace LagrangeFourSquares

/-- Lower bound: 7 is not a sum of 3 squares. -/
theorem seven_needs_four_squares : ¬ IsSumOfPowers 7 3 2 := by
  rintro ⟨xs, h⟩
  -- Reuse parent's seven_obstructed : IsObstructed 7
  -- IsObstructed 7 = ¬ ∃ a b c : ℕ, a^2 + b^2 + c^2 = 7
  have := seven_obstructed
  apply this
  refine ⟨xs 0, xs 1, xs 2, ?_⟩
  -- Convert ∑ i : Fin 3, (xs i)^2 = ∑ over {0,1,2} = (xs 0)^2 + (xs 1)^2 + (xs 2)^2
  have := h
  simp [Fin.sum_univ_three] at this
  linarith [this]

/-- Upper bound: every n is a sum of 4 squares (Lagrange via parent). -/
theorem all_sum_four_squares : ∀ n : ℕ, IsSumOfPowers n 4 2 := by
  intro n
  -- Parent's lagrange_four_squares gives (a b c d) with sum of squares = n.
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares n
  refine ⟨fun i => ![a, b, c, d] i.val, ?_⟩
  -- Sum of fun i.val → a/b/c/d at i = 0..3 over Fin 4 = a^2 + b^2 + c^2 + d^2
  simp [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  linarith

/-- **Correctness**: g(2) = 4. -/
theorem waringG_2_correct :
    (∀ n : ℕ, IsSumOfPowers n (waringG 2) 2) ∧
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG 2 - 1) 2) := by
  refine ⟨?_, 7, ?_⟩
  · -- waringG 2 = 4, by rfl
    exact all_sum_four_squares
  · -- waringG 2 - 1 = 3, by rfl
    exact seven_needs_four_squares

end LagrangeFourSquares
```

**Estimated LOC**: ~25 lines. **Risk**: low — both `seven_obstructed`
and `lagrange_four_squares` are verified in `Proofs/LagrangeFourSquares.lean`.

**Caveat — `Matrix.cons_val_*` simp lemmas**: the `Fin.sum_univ_four`
+ `Matrix.cons_val_*` pattern works in Mathlib v4.26.0 (verified by
direct use in `Proofs/LagrangeFourSquares.lean` line ranges around
the `r4_prime_formula` proof). If `simp` fails, the fallback is
explicit `xs 0`, `xs 1`, `xs 2`, `xs 3` projections via
`Fin.sum_univ_four`.

## 4. `waringG_3_correct` (k = 3) — full draft

After Option B (bridge lemma `isSumOfCubes_iff_isSumOfPowers`)
lands, k=3 follows directly:

```lean
namespace WaringG2OQ01

/-- Definitional bridge: local `IsSumOfCubes s n` and parent's
    `IsSumOfPowers n s 3` are the same predicate up to argument order. -/
lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 := Iff.rfl

/-- Lower bound restated in parent's predicate. -/
theorem twenty_three_not_sum_of_eight_cubes :
    ¬ IsSumOfPowers 23 8 3 := by
  rw [← isSumOfCubes_iff_isSumOfPowers]
  exact twenty_three_needs_nine_cubes

/-- **Correctness**: g(3) = 9. -/
theorem waringG_3_correct :
    (∀ n : ℕ, IsSumOfPowers n (waringG 3) 3) ∧
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG 3 - 1) 3) := by
  refine ⟨?_, 23, ?_⟩
  · -- waringG 3 = 9, by rfl
    exact wieferich_nine_cubes
  · -- waringG 3 - 1 = 8, by rfl
    exact twenty_three_not_sum_of_eight_cubes

end WaringG2OQ01
```

**Estimated LOC**: ~15 lines (3 lemmas + 1 main theorem).

**Risk**: low. Both `wieferich_nine_cubes` (parent axiom) and
`twenty_three_needs_nine_cubes` (S2 ACT, MERGED) are committed and
verified.

**Open question**: should `waringG_3_correct` live in
`WaringG2OQ01` namespace (next to the S2 lower bound) or in
`LagrangeFourSquares` (next to the parent definitions)? Recommendation:
**`WaringG2OQ01`** — keeps the slug's deliverables self-contained
and consistent with the S3 ACT planned location.

## 5. `waringG_4_correct` (k = 4) — sketch

Requires both S3 ACT (lower bound) and a new upper-bound axiom
(S4 PREP proposes `bdd_nineteen_fourth_powers`). Once both land,
the proof is the same shape as k=3:

```lean
/-- Bridge for fourth powers. -/
lemma isSumOfFourthPowers_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfFourthPowers s n ↔ IsSumOfPowers n s 4 := Iff.rfl

theorem seventy_nine_not_sum_of_eighteen_fourth_powers :
    ¬ IsSumOfPowers 79 18 4 := by
  rw [← isSumOfFourthPowers_iff_isSumOfPowers]
  exact seventy_nine_needs_nineteen_fourth_powers

/-- **Correctness**: g(4) = 19. -/
theorem waringG_4_correct :
    (∀ n : ℕ, IsSumOfPowers n (waringG 4) 4) ∧
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG 4 - 1) 4) := by
  refine ⟨?_, 79, ?_⟩
  · exact bdd_nineteen_fourth_powers
  · exact seventy_nine_not_sum_of_eighteen_fourth_powers
```

**Estimated LOC**: ~15 lines. **Blocked on**: S3 ACT + S4 ACT
axiom registration.

## 6. `waringG_5_correct` and `waringG_6_correct` — stubbed

Both follow the same template; the deliverables they depend on:

| `k` | Required upstream |
|---:|-------------------|
| 5 | (a) lower bound `¬ IsSumOfPowers 223 36 5` via mod-32 counting+omega; (b) axiom `chen_thirty_seven_fifth_powers` (S4 PREP §2) |
| 6 | (a) lower bound `¬ IsSumOfPowers 703 72 6` via mod-64 counting+omega; (b) instantiate `waring_general_formula 6` to extract `waringG 6 = 73` |

The k=6 case is **delicate**: `waring_general_formula 6 → waringG 6 = 73`
needs the arithmetic identity
`2^6 + (3^6 - 1)/2^6 - 2 = 64 + 11 - 2 = 73`
discharged by `decide` or `norm_num`. The parent's match-defined
`waringG 6 = 73` already commits to this value, so the *correctness*
theorem only needs to unwrap `rfl`.

## 7. Implementation order

Recommended sequence (each block ~15–40 LOC, doctor-shippable):

1. **S6a ACT (immediate)**: ship `waringG_2_correct` + `waringG_3_correct`
   + the two bridge lemmas in a new file
   `Proofs/LagrangeFourSquaresWaringGCorrectness.lean`. Requires
   only existing infrastructure. **~45 LOC, 0 sorries.**
2. **S3 ACT (parallel)**: ship `g4_lower` per S3 PREP design.
3. **S4 ACT (parallel)**: add the two new upper-bound axioms per
   S4 PREP §2. **~10 LOC, +2 axioms.**
4. **S6b ACT (after S3 + S4 ACT)**: extend correctness file with
   `waringG_4_correct`. **~15 LOC.**
5. **S5 ACT (later)**: design + ship `g5_lower` (k=5 counting+omega
   analogue), then `waringG_5_correct`.
6. **S7 ACT (later)**: design + ship `g6_lower` and
   `waringG_6_correct` via the `waring_general_formula 6` route.

After steps 1–4, the slug has a **verified end-to-end** chain for
`k = 2, 3, 4` (modulo the two new axioms for the upper bounds at
k=4, which the S4 PREP traces to Balasubramanian-Deshouillers-Dress
1986 / Chen Jingrun 1964).

## 8. New file proposal

```
proofs/Proofs/LagrangeFourSquaresWaringGCorrectness.lean
```

**Skeleton** (mirrors the existing `Proofs/LagrangeFourSquaresWaringG2OQ01.lean` shape):

```lean
import Mathlib
import Proofs.LagrangeFourSquares
import Proofs.LagrangeFourSquaresWaringG2OQ01

/-!
# Waring's Problem `g(k) = N` — correctness chain

This file ties the **lower-bound witnesses** (S2 ACT for k=3, S3
ACT for k=4, ...) to the **upper-bound axioms** (Wieferich 1909,
BDD 1986, Chen 1964, Pillai 1940 via general formula) and produces
the end-to-end correctness theorems

  waringG k correct ↔ (∀ n, IsSumOfPowers n (waringG k) k)
                    ∧ (∃ n, ¬ IsSumOfPowers n (waringG k - 1) k)

for each `k` whose lower bound has been Lean-proved and whose upper
bound has been declared as an axiom.

## Status

- `k = 2`: end-to-end **verified** (Mathlib's `Nat.sum_four_squares`
  + parent's `seven_obstructed`).
- `k = 3`: end-to-end **axiomatized** (Wieferich axiom + S2 ACT lower).
- `k = 4`: **pending** S3 ACT (lower) and S4 ACT (upper-bound axioms).
- `k ≥ 5`: **pending** lower-bound design and upper-bound axiom
  registration.

## Bridge lemmas

Local `IsSumOfCubes` / `IsSumOfFourthPowers` defs in
`WaringG2OQ01` unfold definitionally to parent's `IsSumOfPowers`;
explicit `Iff.rfl` lemmas formalise the bridge.
-/

namespace WaringG2OQ01

-- Bridge lemmas (§1 Option B above)
lemma isSumOfCubes_iff_isSumOfPowers (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 := Iff.rfl

-- (Add `isSumOfFourthPowers_iff_isSumOfPowers` after S3 ACT ships.)

-- Restated lower bound (§4)
theorem twenty_three_not_sum_of_eight_cubes : ¬ IsSumOfPowers 23 8 3 := by
  rw [← isSumOfCubes_iff_isSumOfPowers]; exact twenty_three_needs_nine_cubes

-- k = 3 correctness (§4)
theorem waringG_3_correct :
    (∀ n : ℕ, IsSumOfPowers n (waringG 3) 3) ∧
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG 3 - 1) 3) :=
  ⟨wieferich_nine_cubes, 23, twenty_three_not_sum_of_eight_cubes⟩

end WaringG2OQ01

namespace LagrangeFourSquares

-- k = 2 correctness (§3)
theorem seven_needs_four_squares : ¬ IsSumOfPowers 7 3 2 := by
  -- ... see §3 above
  sorry

theorem all_sum_four_squares : ∀ n : ℕ, IsSumOfPowers n 4 2 := by
  -- ... see §3 above
  sorry

theorem waringG_2_correct :
    (∀ n : ℕ, IsSumOfPowers n (waringG 2) 2) ∧
    (∃ n : ℕ, ¬ IsSumOfPowers n (waringG 2 - 1) 2) :=
  ⟨all_sum_four_squares, 7, seven_needs_four_squares⟩

end LagrangeFourSquares
```

**Estimated total LOC**: ~50 (with docstrings). 0 axioms added by
this file (the upper-bound axioms live in parent + S4 ACT).

Two `sorry` placeholders flagged: `seven_needs_four_squares` and
`all_sum_four_squares`. These are not "sorries left in a final
deliverable" — they are S6a ACT's actual work, to be filled per §3.

## 9. Mathlib API audit for §3

The `waringG_2_correct` proof uses:

| Decl | Module | Status v4.26.0 |
|------|--------|----------------|
| `Fin.sum_univ_three` | `Mathlib.Algebra.BigOperators.Fin` | present |
| `Fin.sum_univ_four` | same | present |
| `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons` | `Mathlib.Data.Matrix.Notation` | present |
| `lagrange_four_squares` | `Proofs.LagrangeFourSquares` | present (verified) |
| `seven_obstructed` | `Proofs.LagrangeFourSquares` | present (verified) |
| `IsObstructed` | `Proofs.LagrangeFourSquares` | present |

No upstream API drift expected at the pinned Mathlib v4.26.0
revision.

## 10. Anti-targets

The following are **out of scope** for S6 PREP and should be
addressed in separate sessions:

1. **`waringG` `IsLeast` adapter**. The textbook characterisation is
   `IsLeast { s | ∀ n, IsSumOfPowers n s k } (waringG k)`. Equivalent
   to §2's conjunction, but requires three additional lemmas
   (`mem_def`, `lower_bound_of_lower`, monotonicity in `s`). Defer
   to S6c after S6a/b ship.

2. **`waringG k` semantic well-definedness** for `k ≥ 7`. The
   match-defined formula `2^k + (3^k - 1)/2^k - 2` only matches the
   true `g(k)` *conditionally* (Mahler 1957's condition). For
   research purposes the conditional is fine; for full correctness
   we would need to formalise Mahler's condition, which is far
   beyond this slug.

3. **Hilbert-Waring** (`hilbert_waring`, parent line 267).
   `waring_3_correct` strictly subsumes `hilbert_waring k=3`. Once
   all per-k correctness theorems ship, `hilbert_waring` becomes
   redundant; mark it `deprecated` and re-prove via the per-k chain.

4. **Big-G analogue**. `waringBigG k` (parent line 282) is the
   "almost-all" Waring function. Its characterisation requires
   building "all sufficiently large" infrastructure (`∃ N, ∀ n ≥ N, …`);
   defer to a separate sibling slug.

5. **Tightness audit for the `(- 1)` arithmetic**. The S6 conjunction
   uses `waringG k - 1`, which is Lean's natural-number subtraction
   (truncated at 0). For `k = 0` or `k = 1` where `waringG k = 1`,
   `waringG k - 1 = 0`, and `¬ IsSumOfPowers n 0 k` requires
   `n ≠ 0`. The k=2..6 cases all have `waringG k ≥ 4`, so the
   subtraction is well-behaved. Document this caveat in §2 of the
   final ACT.

## 11. Race awareness

At PREP-push time (2026-05-12, late evening UTC):

- `gh pr list -R rjwalters/lean-genius --search lagrange-four-squares-waring-g2-oq-01 --state open`
  returns `[]` — no open PRs for this slug. The last merged PR is
  #18176 (S2 ACT, MERGED 2026-05-12 ~23:21Z).
- `git branch -r | grep lagrange-four-squares-waring-g2-oq-01`
  returns the merged S1/S2/S3-PREP/S4-PREP branches; no in-flight
  S6 design memo on this angle.
- `ls research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/`
  shows only the merged S3 PREP and S4 PREP doc files. No prior S6
  design.

**Conflict surface**: zero. This PR strictly adds one new session
file under `research/problems/.../sessions/`; modifies nothing
existing.

## 12. No-edit guarantee

This S6 PREP **does not** touch:

- `proofs/Proofs/LagrangeFourSquares.lean` (parent, verified)
- `proofs/Proofs/LagrangeFourSquaresWaringG2.lean` (k=2 sibling, verified)
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT, MERGED)
- `proofs/Proofs.lean` (manifest)
- `research/problems/lagrange-four-squares-waring-g2-oq-01/{problem,knowledge,state}.md`
- the merged S3 PREP / S4 PREP doc files
- `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`
- `src/data/proofs/lagrange-four-squares*/`

Only this single new file is added.

## 13. Hand-off checklist for S6a ACT (next researcher)

1. ☐ Claim `lagrange-four-squares-waring-g2-oq-01` for an S6a ACT
   iteration.
2. ☐ Create `proofs/Proofs/LagrangeFourSquaresWaringGCorrectness.lean`
   per §8 skeleton.
3. ☐ Fill the two `sorry` placeholders for `seven_needs_four_squares`
   and `all_sum_four_squares` per §3 sketches.
4. ☐ Register in `proofs/Proofs.lean`.
5. ☐ `./proofs/scripts/docker-build.sh
   Proofs.LagrangeFourSquaresWaringGCorrectness` — expect <2 min
   compile (no new Mathlib downloads).
6. ☐ Update `state.md` phase → S6a ACT complete, 0 sorries, 0 new
   axioms, +2 theorems (`waringG_2_correct`, `waringG_3_correct`).
7. ☐ Branch: `research/lagrange-four-squares-waring-g2-oq-01-s6a-act-correctness-k2-k3-<unix-ts>`.

## 14. Honesty

This document is **doc-only PREP**. It produces:
- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 1 new design document (this file)

The value is **pre-staging**: a future S6a ACT can ship
`waringG_2_correct` and `waringG_3_correct` in ~30 minutes by
following §8's skeleton verbatim, instead of re-deriving the bridge
lemmas + correctness shape from scratch.

The PREP iteration does NOT discharge any open goal. Status remains
`in-progress` for the slug.

## 15. References

- Hardy & Wright, *An Introduction to the Theory of Numbers*, 5th
  edn (1979), §21.2.
- Wieferich, A. (1909). *Math. Ann.* **66**, 95–101.
- Kempner, A. J. (1912). *Math. Ann.* **72**, 387 (gap correction).
- Balasubramanian, R., Deshouillers, J.-M., Dress, F. (1986).
  *C. R. Acad. Sci. Paris Sér. I*, **303**, 85–88 + 161–163
  (`g(4) = 19`).
- Chen, J. (1964). *Sci. Sinica*, **13**, 1547–1568 (`g(5) = 37`).
- Pillai, S. S. (1940). *J. Indian Math. Soc.* **12** (`g(6) = 73`).
- Mahler, K. (1957). *Mathematika* **4**, 122–124 (conditional
  general formula).
- Kubina, J. M., Wunderlich, M. (1990). *Math. Comp.* **55**,
  815–820 (computational verification).
- OEIS [A002804](https://oeis.org/A002804) — $g(k)$ values
  $\{1, 1, 4, 9, 19, 37, 73, 143, 279, 548, \ldots\}$.
- OEIS [A079611](https://oeis.org/A079611) — numbers needing
  exactly $g(k)$ $k$-th powers ($\{7, 23, 79, 223, 703, \ldots\}$).
- This repo: `Proofs/LagrangeFourSquares.lean` (parent),
  `Proofs/LagrangeFourSquaresWaringG2.lean` (k=2 sibling),
  `Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT for k=3).

---

**End of S6 PREP — no Lean changes, no gallery changes, no axiom
changes. This is a pure design-and-scoping document landing in the
session log as a bridge between lower-bound deliverables and
upper-bound axioms.**
