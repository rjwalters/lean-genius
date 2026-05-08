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

/-- **Generic open_walk_last_target_excess** in the new `walk[i]? = some v` form.
    For an OPEN walk where `walk[0]? ≠ some w` and `walk[n]? = some w`,
    the target-count of `w` (positions where `walk[i+1]? = some w`) exceeds
    its source-count by exactly 1.

    Proof: position `n - 1` is in the target-filter (since `walk[n]? = some w`).
    Removing it leaves a bijection `i ↦ i + 1` with the source-filter, since
    the only source position with `walk[i]? = some w` requires `i ≥ 1` (as
    `walk[0]? ≠ some w`).

    This is the worked-out template Session 13 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `open_walk_last_target_excess`
    (currently L428–467 of the broken main file).

    Compared to the broken version, the differences are:
    1. Endpoint hypotheses use `walk[0]? ≠ some w` and `walk[n]? = some w`
       (Option-form, no bound proof needed).
    2. Filter predicates use `walk[i]? = some w` and `walk[i+1]? = some w`.
    3. The `congr 1; omega` index-shift pattern ports verbatim — no semantic
       difference from the original `walk.get` form. -/
lemma open_walk_last_target_excess' (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk[0]? ≠ some w)
    (hwn : walk[n]? = some w) :
    ((Finset.range n).filter fun i => walk[i + 1]? = some w).card =
    ((Finset.range n).filter fun i => walk[i]? = some w).card + 1 := by
  set T := (Finset.range n).filter (fun i => walk[i + 1]? = some w)
  set S := (Finset.range n).filter (fun i => walk[i]? = some w)
  -- n - 1 ∈ T: walk[(n-1)+1]? = walk[n]? = some w
  have hn1_in_T : n - 1 ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx]
    exact hwn
  rw [show T.card = (T.erase (n - 1)).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase hn1_in_T]]
  congr 1
  -- Bijection: (T \ {n - 1}) → S via i ↦ i + 1
  apply Finset.card_bij (fun i _ => i + 1)
  · -- maps into source filter
    intro i hi
    simp only [T, S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    refine ⟨by omega, ?_⟩
    exact hi_w
  · -- injective: i + 1 = j + 1 ⟹ i = j
    intro i1 _ i2 _ heq
    omega
  · -- surjective: source position j ≥ 1 has preimage j - 1 in T \ {n - 1}
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    -- j ≥ 1: walk[0]? ≠ some w but walk[j]? = some w
    have hj1 : 1 ≤ j := by
      by_contra h
      push_neg at h
      have hj0 : j = 0 := by omega
      exact hw0 (hj0 ▸ hj_w)
    refine ⟨j - 1, ?_, by omega⟩
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    have hidx : j - 1 + 1 = j := by omega
    rw [hidx]
    exact hj_w

/-- **Generic open_walk_first_source_excess** in the new `walk[i]? = some v` form.
    Symmetric to `open_walk_last_target_excess'`. For an OPEN walk where
    `walk[0]? = some w` and `walk[n]? ≠ some w`, the source-count of `w`
    exceeds its target-count by exactly 1.

    Proof: position `0` is in the source-filter. Removing it leaves a
    bijection `i ↦ i - 1` with the target-filter; surjectivity uses that
    `walk[n]? ≠ some w` to exclude the largest target position.

    This is the worked-out template Session 13 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `open_walk_first_source_excess`
    (currently L471–509 of the broken main file).

    Compared to the broken version, the differences are:
    1. Endpoint hypotheses use `walk[0]? = some w` and `walk[n]? ≠ some w`
       (Option-form).
    2. Filter predicates use `walk[i]? = some w` and `walk[i+1]? = some w`.
    3. Surjectivity contradiction `j + 1 = n` ports verbatim. -/
lemma open_walk_first_source_excess' (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk[0]? = some w)
    (hwn : walk[n]? ≠ some w) :
    ((Finset.range n).filter fun i => walk[i]? = some w).card =
    ((Finset.range n).filter fun i => walk[i + 1]? = some w).card + 1 := by
  set S := (Finset.range n).filter (fun i => walk[i]? = some w)
  set T := (Finset.range n).filter (fun i => walk[i + 1]? = some w)
  -- 0 ∈ S: walk[0]? = some w
  have h0_in_S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hw0⟩
  rw [show S.card = (S.erase 0).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase h0_in_S]]
  congr 1
  -- Bijection: (S \ {0}) → T via i ↦ i - 1
  apply Finset.card_bij (fun i _ => i - 1)
  · -- maps into target filter
    intro i hi
    simp only [S, T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    have hi1 : 1 ≤ i := by omega
    refine ⟨by omega, ?_⟩
    have hidx : i - 1 + 1 = i := by omega
    rw [hidx]
    exact hi_w
  · -- injective: i - 1 = j - 1 with i, j ≥ 1 ⟹ i = j
    intro i1 hi1 i2 hi2 heq
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi1 hi2
    omega
  · -- surjective: target position j has preimage j + 1
    intro j hj
    simp only [T, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    -- j + 1 < n: walk[n]? ≠ some w would forbid j + 1 = n
    have hjn : j + 1 < n := by
      by_contra h
      push_neg at h
      have hjn_eq : j + 1 = n := by omega
      exact hwn (hjn_eq ▸ hj_w)
    refine ⟨j + 1, ?_, by omega⟩
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, hj_w⟩

/-- **Generic walk_source_eq_edge_filter** in the new `walk[i]? = some v` form.
    Bijects walk source positions of `v` with edges whose first component is `v`,
    via the `Classical.choose`-based inverse from the unique-coverage hypothesis.

    For a walk of length `n + 1` with `∃!`-coverage of an edge set `edges` and
    every consecutive pair appearing in `edges`, the count of source-positions
    `{i < n : walk[i]? = some v}` equals the count of source-incident edges
    `{e ∈ edges : e.1 = v}`.

    This is the worked-out template Session 13 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `walk_source_eq_outDegree`
    (currently L175–225 of the broken main file).

    Compared to the broken version, the differences are:
    1. Coverage hypothesis uses `walk[i]? = some e.1` (Option-form, no bound proof).
    2. Step hypothesis re-formulated as `∃ e ∈ edges, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2`
       (decouples the witness-edge from the dependent `walk.get` form).
    3. `outDegree` becomes a generic `(edges.filter fun e => e.1 = v).card`
       that the main-file proof unfolds via `unfold outDegree` first.
    4. `Prod.ext` proof of edge-equality uses `Option.some_inj.mp` to strip
       the `some`-wrapper after combining the two `walk[..]? = some _` facts. -/
lemma walk_source_eq_edge_filter' (walk : List V) (n : ℕ) (v : V)
    (edges : Finset (V × V))
    (hcov : ∀ e ∈ edges, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
    (hsteps : ∀ i, i < n → ∃ e ∈ edges,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) :
    ((Finset.range n).filter fun i => walk[i]? = some v).card =
    (edges.filter fun e => e.1 = v).card := by
  symm
  apply Finset.card_bij (fun e he =>
    Classical.choose ((hcov e (Finset.mem_filter.mp he).1).exists))
  · -- maps into the source-position filter
    intro e he
    have hmem := (Finset.mem_filter.mp he).1
    have hv := (Finset.mem_filter.mp he).2
    have hspec := Classical.choose_spec ((hcov e hmem).exists)
    -- hspec : pos < n ∧ walk[pos]? = some e.1 ∧ walk[pos+1]? = some e.2
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hspec.1, ?_⟩
    rw [hspec.2.1, hv]
  · -- injective: pos(e1) = pos(e2) ⟹ e1 = e2
    intro e1 he1 e2 he2 heq
    have hmem1 := (Finset.mem_filter.mp he1).1
    have hmem2 := (Finset.mem_filter.mp he2).1
    have hspec1 := Classical.choose_spec ((hcov e1 hmem1).exists)
    have hspec2 := Classical.choose_spec ((hcov e2 hmem2).exists)
    rw [← heq] at hspec2
    -- hspec1: walk[pos1]? = some e1.1 ∧ walk[pos1+1]? = some e1.2
    -- hspec2 (post-rewrite): walk[pos1]? = some e2.1 ∧ walk[pos1+1]? = some e2.2
    have h1 : some e1.1 = some e2.1 := hspec1.2.1.symm.trans hspec2.2.1
    have h2 : some e1.2 = some e2.2 := hspec1.2.2.symm.trans hspec2.2.2
    exact Prod.ext (Option.some_inj.mp h1) (Option.some_inj.mp h2)
  · -- surjective: each source-position has a corresponding source-edge
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi_lt, hi_v⟩ := hi
    obtain ⟨e, he_mem, he_src, he_tgt⟩ := hsteps i hi_lt
    have he_eq_v : e.1 = v := by
      have heq : some v = some e.1 := hi_v.symm.trans he_src
      exact (Option.some_inj.mp heq).symm
    refine ⟨e, Finset.mem_filter.mpr ⟨he_mem, he_eq_v⟩, ?_⟩
    -- the chosen position for e equals i (uniqueness)
    have hspec := Classical.choose_spec ((hcov e he_mem).exists)
    have hi_spec : i < n ∧ walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2 :=
      ⟨hi_lt, he_src, he_tgt⟩
    exact (hcov e he_mem).unique hspec hi_spec

/-- **Generic walk_target_eq_edge_filter** in the new `walk[i]? = some v` form.
    Symmetric to `walk_source_eq_edge_filter'`. Bijects walk target positions of
    `v` (positions `i < n` with `walk[i+1]? = some v`) with edges whose second
    component is `v`.

    This is the worked-out template Session 13 should transcribe in-place
    into `KonigsbergOQ01OQ02.lean`'s `walk_target_eq_inDegree`
    (currently L228–266 of the broken main file).

    Compared to the broken version, the differences are:
    1. Filter predicate uses `walk[i+1]? = some v` (Option-form).
    2. Step hypothesis identical to source-template (one shared hypothesis form).
    3. `Prod.ext` works the same way; the only structural change is which
       `walk[..]?` projection of `hspec` we use to compare e.2 to v. -/
lemma walk_target_eq_edge_filter' (walk : List V) (n : ℕ) (v : V)
    (edges : Finset (V × V))
    (hcov : ∀ e ∈ edges, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
    (hsteps : ∀ i, i < n → ∃ e ∈ edges,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) :
    ((Finset.range n).filter fun i => walk[i + 1]? = some v).card =
    (edges.filter fun e => e.2 = v).card := by
  symm
  apply Finset.card_bij (fun e he =>
    Classical.choose ((hcov e (Finset.mem_filter.mp he).1).exists))
  · -- maps into the target-position filter
    intro e he
    have hmem := (Finset.mem_filter.mp he).1
    have hv := (Finset.mem_filter.mp he).2
    have hspec := Classical.choose_spec ((hcov e hmem).exists)
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hspec.1, ?_⟩
    rw [hspec.2.2, hv]
  · -- injective: identical to source case
    intro e1 he1 e2 he2 heq
    have hmem1 := (Finset.mem_filter.mp he1).1
    have hmem2 := (Finset.mem_filter.mp he2).1
    have hspec1 := Classical.choose_spec ((hcov e1 hmem1).exists)
    have hspec2 := Classical.choose_spec ((hcov e2 hmem2).exists)
    rw [← heq] at hspec2
    have h1 : some e1.1 = some e2.1 := hspec1.2.1.symm.trans hspec2.2.1
    have h2 : some e1.2 = some e2.2 := hspec1.2.2.symm.trans hspec2.2.2
    exact Prod.ext (Option.some_inj.mp h1) (Option.some_inj.mp h2)
  · -- surjective: each target-position has a corresponding target-edge
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi_lt, hi_v⟩ := hi
    obtain ⟨e, he_mem, he_src, he_tgt⟩ := hsteps i hi_lt
    have he_eq_v : e.2 = v := by
      have heq : some v = some e.2 := hi_v.symm.trans he_tgt
      exact (Option.some_inj.mp heq).symm
    refine ⟨e, Finset.mem_filter.mpr ⟨he_mem, he_eq_v⟩, ?_⟩
    have hspec := Classical.choose_spec ((hcov e he_mem).exists)
    have hi_spec : i < n ∧ walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2 :=
      ⟨hi_lt, he_src, he_tgt⟩
    exact (hcov e he_mem).unique hspec hi_spec

end KonigsbergOQ01OQ02Recipe
