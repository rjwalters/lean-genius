/-
  Königsberg OQ-01 OQ-02: Session 9 Recipe Validation File

  This companion file exists to *validate* the Session 7+8 refactor recipe
  for the build-broken `KonigsbergOQ01OQ02.lean` main file.

  Purpose:
  - Provide a reusable bridge lemma `getElem?_eq_some_iff_of_lt`.
  - Provide a worked-out generic `closed_walk_balance'` lemma in the new
    `walk[i]? = some v` form, mirroring the structure of the broken
    `closed_walk_balance` in the main file.

  Why a separate file:
  - The main file does not currently build (Mathlib API drift on
    `walk.get ⟨i, by omega⟩` patterns inside `Finset.filter` lambdas).
  - Sessions 7 and 8 documented the recipe but made no `.lean` edits.
  - This file proves the recipe approach works under the current Mathlib
    (v4.26.0) without depending on the broken main file. Once Session 10
    applies the recipe in-place, this file can be deleted.

  Note on API: the original recipe targeted `walk.get? i = some v`. Under
  current Lean 4.26.0 / Mathlib, `List.get?` is no longer in scope; the
  canonical Option-returning indexing is `walk[i]?` via the `GetElem?`
  type-class. The recipe transcribed here uses the bracket form throughout.

  Mathematical content: zero (this is a recipe-validation file, not a
  research deliverable). The lemmas here are generic combinatorial bridges
  that the broken file's bijection lemmas instantiate.
-/

import Mathlib

namespace KonigsbergOQ01OQ02Recipe

variable {V : Type*}

/-- **Bridge lemma**: connects the `Option`-valued bracket indexing
    `walk[i]?` and the bound-indexed `walk[i]`. Used by Session 10 to
    convert between forms when refactoring the main file's bijection
    lemmas. -/
lemma getElem?_eq_some_iff_of_lt {l : List V} {i : ℕ} {v : V}
    (h : i < l.length) :
    l[i]? = some v ↔ l[i] = v := by
  rw [List.getElem?_eq_getElem h]
  exact Option.some_inj

variable [DecidableEq V]

/-- **Generic closed_walk_balance** in the new `walk[i]? = some v` form.
    For a closed walk `[v₀, ..., vₙ]` with `v₀ = vₙ`, the source-count of
    any vertex `v` (positions `i ∈ [0, n)` with `walk[i] = v`) equals its
    target-count (positions `i ∈ [0, n)` with `walk[i+1] = v`).

    Proof: bijection `i ↦ (i = 0 ? n - 1 : i - 1)` shifts source positions
    to target positions. The closure hypothesis `walk[0]? = walk[n]?`
    handles the `i = 0` case (source 0 maps to target position n-1, whose
    +1 lands at index n, which equals walk[0] = v).

    This is the worked-out template Session 10 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `closed_walk_balance` (currently
    L128–172 of the broken main file).

    Compared to the broken version, the differences are:
    1. Filter predicates use `walk[i]? = some v` (no bound proof needed).
    2. Closure hypothesis is `walk[0]? = walk[n]?` (Option-form).
    3. Proof body uses index-shift `congr 1; omega` patterns on `[_]?`
       calls (no semantic difference from the original `walk.get` form).
-/
lemma closed_walk_balance' (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (hclosed : walk[0]? = walk[n]?) (v : V) :
    ((Finset.range n).filter fun i => walk[i]? = some v).card =
    ((Finset.range n).filter fun i => walk[i + 1]? = some v).card := by
  apply Finset.card_bij (fun i _ => if i = 0 then n - 1 else i - 1)
  · -- maps into target filter
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    refine ⟨by split_ifs <;> omega, ?_⟩
    split_ifs with h
    · -- i = 0: target position n - 1, need walk[n]? = some v
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx, ← hclosed, ← h]
      exact hi_v
    · -- i > 0: target position i - 1, need walk[i]? = some v
      have hidx : i - 1 + 1 = i := by omega
      rw [hidx]
      exact hi_v
  · -- injective
    intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    split_ifs at heq with h1 h2 <;> omega
  · -- surjective: target position j has preimage (j = n - 1 ? 0 : j + 1)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    refine ⟨if j = n - 1 then 0 else j + 1, ⟨by split_ifs <;> omega, ?_⟩, ?_⟩
    · split_ifs with h
      · -- j = n - 1: preimage 0; need walk[0]? = some v
        rw [hclosed]
        have hidx : j + 1 = n := by omega
        rw [← hidx]
        exact hj_v
      · -- j < n - 1: preimage j + 1; need walk[j + 1]? = some v
        exact hj_v
    · -- bijection value at chosen preimage equals j
      by_cases h : j = n - 1
      · simp [h]
      · have hne : j + 1 ≠ 0 := Nat.succ_ne_zero j
        simp [h, hne]

/-- **Generic open_walk_interior_balanced** in the new `walk[i]? = some v` form.
    For an OPEN walk where neither endpoint equals `v` (so `v` is purely
    interior), the source-count of `v` equals its target-count.

    Proof: bijection `i ↦ i - 1` maps source positions to target positions.
    The endpoint hypotheses ensure `i = 0` is not a source position (because
    `walk[0]? ≠ some v`) and `j = n - 1` is not the largest target position
    (because `walk[n]? ≠ some v` would forbid `j + 1 = n`), keeping the
    bijection well-defined on `[1, n-1] → [0, n-2]`.

    This is the worked-out template Session 10/11 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `open_walk_interior_balanced` (currently
    L517–559 of the broken main file).

    Compared to the broken version, the differences are:
    1. Endpoint hypotheses use `walk[0]? ≠ some v` / `walk[n]? ≠ some v`
       (Option-form, no bound proof needed).
    2. Filter predicates use `walk[i]? = some v`.
    3. The `by_contra; push_neg; have : i = 0 := by omega; exact hw0 ...`
       contradiction shape ports verbatim — the only change is that the
       `hi_v` rewrite target is `walk[0]? = some v` instead of
       `walk.get ⟨0, _⟩ = v`. -/
lemma open_walk_interior_balanced' (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (v : V)
    (hw0 : walk[0]? ≠ some v)
    (hwn : walk[n]? ≠ some v) :
    ((Finset.range n).filter fun i => walk[i]? = some v).card =
    ((Finset.range n).filter fun i => walk[i + 1]? = some v).card := by
  apply Finset.card_bij (fun i _ => i - 1)
  · -- maps into target filter
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    -- i ≥ 1: walk[0]? ≠ some v, so i = 0 contradicts walk[i]? = some v
    have hi1 : 1 ≤ i := by
      by_contra h
      push_neg at h
      have hi0 : i = 0 := by omega
      exact hw0 (hi0 ▸ hi_v)
    refine ⟨by omega, ?_⟩
    -- walk[(i - 1) + 1]? = walk[i]? = some v
    have hidx : i - 1 + 1 = i := by omega
    rw [hidx]
    exact hi_v
  · -- injective: i - 1 = j - 1 with i, j ≥ 1 ⟹ i = j
    intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨_, hi_v⟩ := hi
    obtain ⟨_, hj_v⟩ := hj
    have hi1 : 1 ≤ i := by
      by_contra h
      push_neg at h
      have hi0 : i = 0 := by omega
      exact hw0 (hi0 ▸ hi_v)
    have hj1 : 1 ≤ j := by
      by_contra h
      push_neg at h
      have hj0 : j = 0 := by omega
      exact hw0 (hj0 ▸ hj_v)
    omega
  · -- surjective: target position j has preimage j + 1
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    -- j + 1 < n: walk[n]? ≠ some v, so j + 1 = n would contradict walk[j+1]? = some v
    have hjn : j + 1 < n := by
      by_contra h
      push_neg at h
      have hjn_eq : j + 1 = n := by omega
      exact hwn (hjn_eq ▸ hj_v)
    refine ⟨j + 1, ⟨by omega, ?_⟩, by omega⟩
    -- walk[j + 1]? = some v (direct from hypothesis)
    exact hj_v

end KonigsbergOQ01OQ02Recipe
