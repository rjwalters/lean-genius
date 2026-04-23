# Knowledge Base: lebesgue-measure-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

The Banach-Tarski paradox (1924) is the statement that the unit ball B³ ⊂ ℝ³ can be
decomposed into finitely many disjoint pieces that reassemble into two unit balls under
rigid motions. The paradox relies on non-measurable sets (hence is not a contradiction
of Lebesgue measure) and the Axiom of Choice.

**Research goal**: Formally state the theorem in Lean 4 and identify exactly what Mathlib
infrastructure is needed. A statement-level formalization (with key lemmas sorry'd) is
achievable; a complete proof would require the Hausdorff paradox.

---

## Key Mathematical Facts

### The Proof Strategy (Hausdorff → Banach-Tarski)

1. **Hausdorff paradox** (1914): The unit sphere S² can be partitioned into four sets
   A, B, C, D where D is countable and {A, B, C} is a "paradoxical triplet":
   - A and B∪C are congruent (under some rotation)
   - B and C are congruent (under some rotation)
   This follows from the free subgroup of SO(3).

2. **Free subgroup of SO(3)**: The rotations
   - φ = rotation by arccos(1/3) around the z-axis
   - ψ = rotation by arccos(1/3) around the x-axis
   generate a free group F₂ inside SO(3). This is the algebraic heart of the paradox.

3. **Paradoxical decomposition of F₂**: The free group on 2 generators {a, b} satisfies:
   F₂ = F₂·a ⊔ F₂·b ⊔ {e} (as sets, via a Cayley graph argument).
   From this one constructs a decomposition of S² into 3 pieces each congruent to the whole.

4. **Extension to B³**: By adding the origin and using a "expanding sphere" argument,
   the S² paradox extends to B³.

### Tarski's Equivalence Theorem
The Banach-Tarski paradox is equivalent (via Tarski's theorem) to the statement:
- B³ is **paradoxically decomposable** with respect to the isometry group of ℝ³
- Equivalently: there is no finitely additive, isometry-invariant measure on all subsets of ℝ³
  that agrees with Lebesgue measure on measurable sets.

---

## Mathlib Status

### What Mathlib Has

- `Matrix.SpecialOrthogonalGroup ℝ (Fin 3)`: The SO(3) group
- `Isometry`, `IsometryEquiv`: Isometries of metric spaces
- `EuclideanSpace ℝ (Fin 3)`: ℝ³ as a Euclidean space
- `MeasureTheory.Measure.Lebesgue.Basic`: Lebesgue measure
- `MeasureTheory.Measure.NullMeasurableSet`: Non-measurable set concept
- `FreeGroup`: Free groups in Mathlib
- `Subgroup.IsFreeGroup`: Free subgroups

### What's Missing / Needs Investigation

- **Free subgroup of SO(3)**: Does Mathlib have the fact that SO(3) contains F₂?
  Check: `Mathlib.GroupTheory.FreeProduct`, free subgroups of Lie groups.
- **Hausdorff paradox**: No known Lean 4 formalization found yet.
- **Paradoxical decomposability**: The `IsParadoxicallyDecomposable` predicate needs
  to be defined (not in Mathlib).
- **Rigid motions = SE(3)**: The semidirect product SO(3) ⋊ ℝ³ may need to be set up.

---

## Insights

### Lean 4 Build Fixes (2026-04-23)

The original file had never successfully compiled. Fixed the following issues:

1. **`ℝ≥0∞` notation requires `open ENNReal`**: Added to the `open` statement. Without it,
   the `∞` symbol fails to parse with "expected token" errors.

2. **Set SMul requires `open scoped Pointwise`**: `g • (Set α)` in the `Equidecomposable`
   definition and in `IsAmenable` fails without this. Added `open scoped Pointwise NNReal`.

3. **Forward reference bug**: `paradoxical_no_finite_measure` called a private lemma
   (`ENNReal.eq_zero_or_top_of_add_eq_self`) that was defined AFTER it. Lean 4 doesn't
   allow forward references. Fixed by moving the helper lemma before its caller.

4. **`Set.union_sdiff_of_subset` → `Set.union_diff_cancel`**: Wrong Lean 4 name.
   `Set.union_diff_cancel (h : s ⊆ t) : s ∪ (t \ s) = t`.

5. **Notation parsing issue with `A ≃ᴳ[G] B → P`**: The custom notation consumed the `→`
   and everything after `B` as part of the RHS argument. Fixed by wrapping `(A ≃ᴳ[G] S)`
   in parentheses in the `hμ_equi` parameter.

6. **`linarith` on ℝ≥0 requires cast to ℝ**: To prove `a = 0` from `a + a = a` in NNReal,
   must lift to ℝ≥0, `norm_cast`, then cast to ℝ before `linarith`.

7. **`le_add_right` signature in Lean 4 Mathlib**: Takes a proof `h : a ≤ b` as first
   explicit argument. Use `le_add_right le_rfl` to get `a ≤ a + c`.

8. **`[MulAction.IsPretransitive G α]` is unnecessary** for `equidecomposable_refl`.
   Removed. Reflexivity proof uses `Subsingleton.elim` for disjointness (since `Fin 1`
   has exactly one element), and `Set.iUnion_const` + `one_smul` for the union goals.

### Build Status
File now compiles with exactly 5 intentional `sorry`s:
- `hausdorff_free_subgroup` (needs explicit rotation matrix freeness proof)
- `banach_tarski` (needs full 800-line proof via Hausdorff paradox)
- `banach_tarski_pieces_nonmeasurable` (follows from banach_tarski + measure theory)
- `int_amenable` (needs Cesàro mean / Banach limit construction)
- `free_group_not_amenable` (needs paradoxical decomposition of F₂)

---

## Dead Ends

### `equidecomposable_refl` with `[MulAction.IsPretransitive G α]`
The original proof tried to use `Fin.eq_of_val_eq` for the disjointness subgoal.
This is fragile and unnecessarily constrains the signature. `Subsingleton.elim i j`
directly gives `i = j` for `i j : Fin 1` without needing any extra hypotheses.

---

## Session 2026-04-23 (Session 2) — free_group_not_amenable PROVED

**Mode**: REVISIT (ACT phase)
**Outcome**: proof completed — `free_group_not_amenable` fully proved, sorry count 5 → 4

### What I Did

Proved `free_group_not_amenable : ¬ IsAmenable (FreeGroup (Fin 2))` via explicit
paradoxical decomposition of F₂. Key components:

1. **W_a_two_cover**: `univ = W_a ∪ (a • W_ainv)` — words starting with `a` plus
   left-multiplied words starting with `a⁻¹` cover F₂. Proved by `ext g`, case split on
   whether `g.toWord.head? = some (0, true)`.

2. **W_a_smul_disj**: `Disjoint W_a (a • W_ainv)` — no word can start with both `a` and
   have its `a`-shifted preimage start with `a⁻¹`. Proved using `FreeGroup.Red.Step.cons_not`
   and `FreeGroup.IsReduced.infix`.

3. **W_b_two_cover**, **W_b_smul_disj**: Symmetric versions for generator `b = FreeGroup.of 1`.

4. **free_group_not_amenable** itself: If μ were an amenable measure on F₂, left-invariance
   gives `μ(W_a) + μ(W_ainv) = 1` and `μ(W_b) + μ(W_binv) = 1`. Pairwise disjointness of
   the four sets gives `μ(W_a) + μ(W_ainv) + μ(W_b) + μ(W_binv) ≤ 1`, contradicting
   adding the two equations to get ≥ 2.

### Key Technical Fixes

- **`rcases hw : w.toWord with _ | ⟨hd, rest⟩`**: After this, Lean substitutes `w.toWord → hd :: rest` in the goal, so the existential goal becomes `∃ tl, hd :: rest = (0, false) :: tl` — NOT `w.toWord = ...`. The proof term must match the *substituted* form.

- **Correct proof**: `exact ⟨rest, by rw [hd_eq]⟩` — where `hd_eq : hd = (0, false)`, `rw [hd_eq]` closes `hd :: rest = (0, false) :: rest` directly.

- **Wrong attempts**: `hw.trans (by simp [hd_eq])` fails because `simp` sees goal `hd :: rest = ?m` with a free RHS metavar and can't close it. `hw.trans` is not needed — the goal is already `hd :: rest = ...` not `w.toWord = ...`.

- **`FreeGroup.isReduced_toWord`**: All arguments implicit — use type annotation `have h1 : FreeGroup.IsReduced w.toWord := FreeGroup.isReduced_toWord`.

- **`instSMulOfMul`**: `a • b = a * b` definitionally — `mul_inv_cancel_left _ g` works where `by group` fails.

- **`Set.union_diff_cancel (Set.subset_univ _)`**: Provides `s ∪ (univ \ s) = univ`.

- **`le_add_of_nonneg_right (zero_le _)`**: Provides `a ≤ a + b` in ℝ≥0∞.

### Files Modified
- `proofs/Proofs/LebesgueMeasureOQ06.lean`: 419 → 527 lines, sorries 5 → 4

### Next Steps
- Submit `hausdorff_free_subgroup` sorry to Aristotle (explicit rotation matrix freeness — HARD)
- Consider building F₂ paradoxical decomposition as standalone algebraic lemma (~150 lines)
- `int_amenable` sorry: tractable via Banach limit / Mathlib's Hahn-Banach (~200 lines)
