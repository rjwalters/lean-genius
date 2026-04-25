import Mathlib
import Proofs.SpernerNDim

/-!
# n-Dimensional Sperner: Kuhn Path-Following Algorithm

Formalizes Kuhn's (1968) constructive proof of Sperner's lemma via path-following
in the door adjacency graph of an abstract triangulation.

## Overview

Kuhn's algorithm provides a CONSTRUCTIVE proof of Sperner's lemma:
starting from a boundary door, follow a unique path through the door graph
to reach a fully-colored simplex. The algorithm works in polynomial time.

## Door Graph Structure

For a Sperner triangulation and coloring:
- **Door** at (s, k): the d vertices of s excluding vertex k carry all d colors {0,...,d-1}
- **Interior door**: (s, k) with K.adj s k = some (s', k'); paired with door (s', k')
- **Boundary door**: (s, k) with K.adj s k = none; on face d (by Sperner condition)

The **door degree** of simplex s is the number of positions k with isDoorAt c K s k.
By the abstract door parity theorem:
- FC simplices (surjective coloring): odd door degree
- Non-FC simplices: even door degree

## Kuhn Compatibility Axiom

A triangulation is **Kuhn-compatible** if every simplex has door degree ≤ 2.
Under this axiom (and parity):
- FC simplices: exactly 1 door
- Non-FC simplices: exactly 0 or 2 doors

This makes the Kuhn algorithm deterministic: enter through one door, exit through
the unique other door (if any), repeating until reaching an FC simplex.

## Main Results

### Proved
1. `fc_door_count_eq_one` — FC simplices have exactly 1 door
2. `nonfc_door_count_zero_or_two` — Non-FC simplices have 0 or 2 doors
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with an entry door has a unique exit door
4. `kuhn_step` — One step of the Kuhn algorithm
5. `kuhn_path_terminates` — FC simplex exists (non-constructive, from parity)
6. `kuhn_three_doors_contradiction` — Three distinct doors → contradiction with Kuhn compatibility
7. `walkValid_init` — Initial boundary-door state satisfies WalkValid
8. `walkValid_step` — WalkValid preserved by one Kuhn step
9. `kuhn_step_nonrevisit` — **KEY**: under WalkValid, walk never revisits a simplex
10. `kuhnWalk_no_immediate_back` — Immediate predecessor is not revisitable (adj_unique_facet)
11. `kuhnWalk_first_exit_interior` — First step from boundary door is always interior
12. `kuhnPathStart_is_fc_of_fc_start` — Walk finds FC immediately if starting simplex is FC
13. `kuhnPathStart_finds_fc_existential` — ∃ boundary door whose walk finds FC (axiomatized)

### Axiomatized
- `kuhn_path_existential_ax` — Walk-reversal involution; non-revisiting proved, τ∘τ=id pending

### Removed (false as stated)
- `kuhn_walk_reaches_fc` — Universal walk theorem is false; boundary exit possible on some paths
- `kuhnPathStart_is_fc` — False for some starting boundary doors; correct form is existential
-/

set_option maxHeartbeats 400000

namespace SpernerNDimOQ04

open SpernerNDim Finset BigOperators

variable {d N : ℕ}

-- ============================================================
-- SECTION I: Door Degree and Kuhn Compatibility
-- ============================================================

/-- The door degree of simplex s: number of facets k with isDoorAt c K s k. -/
def doorDegree (c : Coloring d N) (K : SpernerTriangulation d N) (s : K.Simplex) : ℕ :=
  (Finset.univ.filter (fun k => isDoorAt c K s k)).card

/-- A triangulation is Kuhn-compatible if each simplex has door degree ≤ 2.
    This makes the Kuhn path-following algorithm deterministic. -/
def IsKuhnCompatible (c : Coloring d N) (K : SpernerTriangulation d N) : Prop :=
  ∀ s : K.Simplex, doorDegree c K s ≤ 2

-- ============================================================
-- SECTION II: Per-Simplex Door Parity (from Abstract Theorem)
-- ============================================================

/-- The door degree parity of a simplex follows from abstract_door_parity.
    FC simplices have odd door degree; non-FC have even door degree. -/
lemma door_degree_parity (c : Coloring d N) (K : SpernerTriangulation d N) (s : K.Simplex) :
    doorDegree c K s % 2 = if IsFC c K s then 1 else 0 := by
  unfold doorDegree
  -- Apply abstract_door_parity with f = c ∘ K.vertices s
  have h := abstract_door_parity d (c ∘ K.vertices s)
  -- The filter for isDoorAt c K s k matches the abstract condition
  have heq : (Finset.univ.filter (fun k : Fin (d + 1) => isDoorAt c K s k)) =
      (Finset.univ.filter (fun k : Fin (d + 1) =>
        ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ (c ∘ K.vertices s) i = ⟨j.val, by omega⟩)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  have hiff : IsFC c K s ↔ Function.Surjective (c ∘ K.vertices s) := Iff.rfl
  simp only [hiff]
  convert h using 2

-- ============================================================
-- SECTION III: Door Counts under Kuhn Compatibility
-- ============================================================

/-- Under Kuhn compatibility, FC simplices have exactly 1 door. -/
theorem fc_door_count_eq_one {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (s : K.Simplex) (hfc : IsFC c K s) :
    doorDegree c K s = 1 := by
  have hpar := door_degree_parity c K s
  rw [if_pos hfc] at hpar
  have hle := hKuhn s
  -- doorDegree % 2 = 1 and doorDegree ≤ 2, so doorDegree = 1
  omega

/-- Under Kuhn compatibility, non-FC simplices have 0 or 2 doors. -/
theorem nonfc_door_count_zero_or_two {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (s : K.Simplex) (hnonfc : ¬IsFC c K s) :
    doorDegree c K s = 0 ∨ doorDegree c K s = 2 := by
  have hpar := door_degree_parity c K s
  rw [if_neg hnonfc] at hpar
  have hle := hKuhn s
  -- doorDegree % 2 = 0 and doorDegree ≤ 2, so doorDegree = 0 or 2
  omega

-- ============================================================
-- SECTION IV: Exit Door Existence and Uniqueness
-- ============================================================

/-- Non-FC simplex with an entry door has a unique exit door.
    This is the heart of the Kuhn algorithm: from any entered non-FC simplex,
    there is exactly one other door to exit through. -/
theorem nonfc_with_door_has_unique_exit {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (s : K.Simplex)
    (hnonfc : ¬IsFC c K s)
    (k_in : Fin (d + 1)) (hdoor_in : isDoorAt c K s k_in) :
    ∃! k_out : Fin (d + 1), k_out ≠ k_in ∧ isDoorAt c K s k_out := by
  -- Step 1: Door degree is 0 or 2
  rcases nonfc_door_count_zero_or_two hKuhn s hnonfc with h0 | h2
  · -- Door degree = 0, but k_in is a door: contradiction
    exfalso
    have : 0 < doorDegree c K s := by
      apply Finset.card_pos.mpr
      exact ⟨k_in, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_in⟩⟩
    omega
  · -- Door degree = 2
    -- The filter has exactly 2 elements
    have hcard : (Finset.univ.filter (fun k => isDoorAt c K s k)).card = 2 := h2
    -- Extract the two elements
    rw [Finset.card_eq_two] at hcard
    obtain ⟨k₁, k₂, hne12, hset⟩ := hcard
    -- k_in is one of them
    have hkin_mem : k_in ∈ Finset.univ.filter (fun k => isDoorAt c K s k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_in⟩
    rw [hset] at hkin_mem
    simp at hkin_mem
    -- The other one is the exit door
    rcases hkin_mem with rfl | rfl
    · -- k_in = k₁, exit is k₂
      refine ⟨k₂, ⟨hne12.symm, ?_⟩, ?_⟩
      · -- isDoorAt c K s k₂
        have hk₂_mem : k₂ ∈ Finset.univ.filter (fun k => isDoorAt c K s k) := by
          rw [hset]; simp
        exact (Finset.mem_filter.mp hk₂_mem).2
      · -- Uniqueness: any k_out ≠ k_in with isDoorAt must be k₂
        intro k_out ⟨hne_in, hdoor_out⟩
        have hk_out_mem : k_out ∈ Finset.univ.filter (fun k => isDoorAt c K s k) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_out⟩
        rw [hset] at hk_out_mem
        simp at hk_out_mem
        rcases hk_out_mem with rfl | rfl
        · exact absurd rfl hne_in
        · rfl
    · -- k_in = k₂, exit is k₁
      refine ⟨k₁, ⟨hne12, ?_⟩, ?_⟩
      · -- isDoorAt c K s k₁
        have hk₁_mem : k₁ ∈ Finset.univ.filter (fun k => isDoorAt c K s k) := by
          rw [hset]; simp
        exact (Finset.mem_filter.mp hk₁_mem).2
      · -- Uniqueness
        intro k_out ⟨hne_in, hdoor_out⟩
        have hk_out_mem : k_out ∈ Finset.univ.filter (fun k => isDoorAt c K s k) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_out⟩
        rw [hset] at hk_out_mem
        simp at hk_out_mem
        rcases hk_out_mem with rfl | rfl
        · rfl
        · exact absurd rfl hne_in

-- ============================================================
-- SECTION V: Door Transfer (local re-proof; door_transfer is private in SpernerNDim)
-- ============================================================

private lemma local_door_transfer_one_dir {c : Coloring d N} {K : SpernerTriangulation d N}
    {s : K.Simplex} {k : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hvert : (Finset.univ.erase k).image (K.vertices s) =
             (Finset.univ.erase k').image (K.vertices s'))
    (h : isDoorAt c K s k) : isDoorAt c K s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : K.vertices s i ∈ (Finset.univ.erase k').image (K.vertices s') := by
    rw [← hvert]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := Finset.mem_image.mp hmem
  exact ⟨i', (Finset.mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩

lemma door_transfer {c : Coloring d N} {K : SpernerTriangulation d N}
    {s : K.Simplex} {k : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj s k = some (s', k')) :
    isDoorAt c K s k ↔ isDoorAt c K s' k' :=
  ⟨local_door_transfer_one_dir (K.adj_vertices s k s' k' hadj),
   local_door_transfer_one_dir (K.adj_vertices s k s' k' hadj).symm⟩

-- ============================================================
-- SECTION VI: Kuhn Step Function
-- ============================================================

/-- One step of Kuhn's algorithm: given entry door (s, k_in),
    return the exit door (k_out) and adjacent simplex (s', k_out').
    Returns None if s is FC (algorithm terminates). -/
def kuhnStep (c : Coloring d N) (K : SpernerTriangulation d N)
    (hKuhn : IsKuhnCompatible c K)
    (s : K.Simplex) (k_in : Fin (d + 1))
    (hdoor_in : isDoorAt c K s k_in) :
    Option (K.Simplex × Fin (d + 1)) :=
  if IsFC c K s then
    -- FC: algorithm terminates here
    none
  else
    -- Non-FC: find the unique exit door
    let exit_doors := Finset.univ.filter (fun k => isDoorAt c K s k ∧ k ≠ k_in)
    if h : exit_doors.Nonempty then
      let k_out := exit_doors.min' h
      K.adj s k_out
    else
      none  -- Shouldn't happen (non-FC with entry door has exit, by nonfc_with_door_has_unique_exit)

/-- The exit door found by kuhnStep has the door property. -/
lemma kuhnStep_door_preserved {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s : K.Simplex) (k_in : Fin (d + 1))
    (hdoor_in : isDoorAt c K s k_in)
    (hnonfc : ¬IsFC c K s)
    {s' : K.Simplex} {k_out' : Fin (d + 1)}
    (hstep : kuhnStep c K hKuhn s k_in hdoor_in = some (s', k_out')) :
    isDoorAt c K s' k_out' := by
  -- First prove the exit_doors set is nonempty (it must be, since non-FC with entry door)
  have hexit : (Finset.univ.filter (fun k => isDoorAt c K s k ∧ k ≠ k_in)).Nonempty := by
    obtain ⟨k_out, ⟨hne, hdoor_k⟩, _⟩ := nonfc_with_door_has_unique_exit hKuhn s hnonfc k_in hdoor_in
    exact ⟨k_out, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_k, hne⟩⟩
  -- Simplify hstep using kuhnStep's definition and the nonemptiness
  simp only [kuhnStep, if_neg hnonfc, dif_pos hexit] at hstep
  -- hstep is now: K.adj s exit_doors.min' = some (s', k_out')
  exact (door_transfer hstep).mp
    ((Finset.mem_filter.mp (Finset.min'_mem _ hexit)).2.1)

-- ============================================================
-- SECTION VII: Kuhn Path Algorithm
-- ============================================================

/-- A Kuhn walk state: current simplex, entry door, set of visited simplices. -/
structure KuhnState (d N : ℕ) (c : Coloring d N) (K : SpernerTriangulation d N) where
  current : K.Simplex
  entry : Fin (d + 1)
  entry_is_door : isDoorAt c K current entry
  visited : Finset K.Simplex
  current_not_visited : current ∉ visited

/-- Run Kuhn's algorithm for at most `fuel` steps.
    Returns the FC simplex found, or the final state if fuel runs out. -/
def kuhnWalk (c : Coloring d N) (K : SpernerTriangulation d N)
    (hKuhn : IsKuhnCompatible c K)
    (fuel : ℕ) (state : KuhnState d N c K) : K.Simplex :=
  match fuel with
  | 0 => state.current
  | n + 1 =>
    if IsFC c K state.current then
      state.current
    else
      -- Find the exit door
      let exit_doors := Finset.univ.filter (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)
      if hne : exit_doors.Nonempty then
        let k_out := exit_doors.min' hne
        have hk_out_mem : k_out ∈ exit_doors := Finset.min'_mem _ _
        have hdoor_out : isDoorAt c K state.current k_out :=
          (Finset.mem_filter.mp hk_out_mem).2.1
        match hadj : K.adj state.current k_out with
        | none =>
          -- Boundary exit: this simplex is where the walk ends
          state.current
        | some (s', k_out') =>
          if hs' : s' ∈ state.visited ∪ {state.current} then
            -- Would revisit: terminate (shouldn't happen for valid Kuhn walks)
            state.current
          else
            let new_door : isDoorAt c K s' k_out' :=
              (door_transfer hadj).mp hdoor_out
            let new_state : KuhnState d N c K := {
              current := s'
              entry := k_out'
              entry_is_door := new_door
              visited := state.visited ∪ {state.current}
              current_not_visited := hs'
            }
            kuhnWalk c K hKuhn n new_state
      else
        state.current

-- ============================================================
-- SECTION VIII: Non-Revisiting Lemmas (adj_unique_facet-based)
-- ============================================================

/-- Under Kuhn compatibility, the walk cannot immediately return to the simplex it just left.
    This is the s' = sₙ₋₁ case of the non-revisiting proof.

    Proof: by adj_unique_facet applied to s₁.
    - K.adj s₁ k₁ = some(s₀, k_exit_0) by adj_symm
    - K.adj s₁ k_out = some(s₀, k_any) would give k₁ = k_out by adj_unique_facet
    - Contradicts k_out ≠ k₁ (exit ≠ entry). -/
lemma kuhnWalk_no_immediate_back (K : SpernerTriangulation d N)
    (s₀ : K.Simplex) (k_exit : Fin (d + 1))
    (s₁ : K.Simplex) (k₁ : Fin (d + 1)) (hadj : K.adj s₀ k_exit = some (s₁, k₁))
    (k_out : Fin (d + 1)) (hne : k_out ≠ k₁) :
    ∀ k_back, K.adj s₁ k_out ≠ some (s₀, k_back) := by
  intro k_back h
  have hadj_back : K.adj s₁ k₁ = some (s₀, k_exit) := K.adj_symm _ _ _ _ hadj
  have heq := K.adj_unique_facet s₁ k₁ k_out s₀ k_exit k_back hadj_back h
  exact hne heq.symm

/-- Under IsSperner, starting from a boundary door, the walk's first exit step is interior.
    If entry k₀ satisfies K.adj s₀ k₀ = none, then exit k_out (≠ k₀) has K.adj s₀ k_out ≠ none.

    Proof: k₀ is boundary so k₀ = Fin.last d (boundary_door_is_last_face).
    If k_out is also boundary, k_out = Fin.last d = k₀, contradicting k_out ≠ k₀. -/
lemma kuhnWalk_first_exit_interior {c : Coloring d N} {K : SpernerTriangulation d N}
    (hc : IsSperner c)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀) (hbdry₀ : K.adj s₀ k₀ = none)
    (k_out : Fin (d + 1)) (hdoor_out : isDoorAt c K s₀ k_out)
    (hne : k_out ≠ k₀) :
    K.adj s₀ k_out ≠ none := by
  intro hbdry_out
  have hk₀_last : k₀ = Fin.last d :=
    boundary_door_is_last_face c K hc s₀ k₀ hdoor₀ hbdry₀
  have hkout_last : k_out = Fin.last d :=
    boundary_door_is_last_face c K hc s₀ k_out hdoor_out hbdry_out
  exact hne (hkout_last.trans hk₀_last.symm)

-- ============================================================
-- SECTION VIII-B: Non-Revisiting Invariant
-- ============================================================

/-- Three distinct doors at the same simplex contradict Kuhn compatibility.
    Core lemma for the non-revisiting proof: if a visited simplex s acquires
    a third door from the current step, doorDegree s ≥ 3 > 2. -/
lemma kuhn_three_doors_contradiction {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (s : K.Simplex)
    (k₁ k₂ k₃ : Fin (d + 1))
    (h₁ : isDoorAt c K s k₁) (h₂ : isDoorAt c K s k₂) (h₃ : isDoorAt c K s k₃)
    (hne₁₂ : k₁ ≠ k₂) (hne₁₃ : k₁ ≠ k₃) (hne₂₃ : k₂ ≠ k₃) : False := by
  -- {k₁, k₂, k₃} ⊆ doorFilter, so doorDegree ≥ 3, contradicting hKuhn s ≤ 2
  have hsub : ({k₁, k₂, k₃} : Finset (Fin (d + 1))) ⊆
      Finset.univ.filter (fun k => isDoorAt c K s k) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₃⟩
  have hcard3 : ({k₁, k₂, k₃} : Finset (Fin (d + 1))).card = 3 := by
    have h23 : k₂ ∉ ({k₃} : Finset (Fin (d + 1))) := Finset.not_mem_singleton.mpr hne₂₃
    have h1 : k₁ ∉ ({k₂, k₃} : Finset (Fin (d + 1))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hne₁₂, hne₁₃⟩
    rw [Finset.card_insert_of_not_mem h1, Finset.card_insert_of_not_mem h23,
        Finset.card_singleton]
  have h3 : 3 ≤ doorDegree c K s := by
    unfold doorDegree; rw [← hcard3]; exact Finset.card_le_card hsub
  linarith [hKuhn s]

/-- Walk door record: maps visited simplices to their (entry, exit) door pair. -/
abbrev DoorRecord (d N : ℕ) (K : SpernerTriangulation d N) :=
  K.Simplex → Option (Fin (d + 1) × Fin (d + 1))

/-- Walk validity invariant. Maintains enough history to prove non-revisiting:
    every visited simplex has an (entry, exit) door record forming a chain,
    and a distinguished predecessor simplex (optional) identifies which visited
    simplex exited directly to the current simplex.

    The chain properties enable the key distinctness arguments:
    - exit_to_chain: exit of each non-predecessor visited simplex goes BACK INTO visited
    - entry_from_chain: entry of each visited simplex came FROM visited or boundary
    This lets adj_unique_facet rule out any revisiting simplex acquiring a third door. -/
structure WalkValid {d N : ℕ} {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (state : KuhnState d N c K)
    (rec : DoorRecord d N K)
    (pred : Option K.Simplex) : Prop where
  /-- Every visited simplex has a door record. -/
  has_record : ∀ s ∈ state.visited, ∃ k_in k_out, rec s = some (k_in, k_out)
  /-- Recorded door pairs are valid: both are doors, they are distinct. -/
  doors_valid : ∀ s k_in k_out, rec s = some (k_in, k_out) →
      isDoorAt c K s k_in ∧ isDoorAt c K s k_out ∧ k_in ≠ k_out
  /-- Entry of each visited simplex came from visited or is a boundary door. -/
  entry_from_chain : ∀ s k_in k_out, rec s = some (k_in, k_out) →
      K.adj s k_in = none ∨
      (∃ s_prev k_prev, K.adj s k_in = some (s_prev, k_prev) ∧ s_prev ∈ state.visited)
  /-- Exit of each visited simplex either goes to (a) current if it is the predecessor,
      or (b) another visited simplex. -/
  exit_to_chain : ∀ s k_in k_out, rec s = some (k_in, k_out) →
      (pred = some s ∧ ∃ q, K.adj s k_out = some (state.current, q)) ∨
      (∃ s_out k_out', K.adj s k_out = some (s_out, k_out') ∧ s_out ∈ state.visited)
  /-- The predecessor spec: if pred = some s_pred, then s_pred exited to current
      via state.entry; if pred = none, current has a boundary entry. -/
  pred_spec : (pred = none ∧ K.adj state.current state.entry = none) ∨
      (∃ s_pred k_exit, pred = some s_pred ∧ s_pred ∈ state.visited ∧
        K.adj s_pred k_exit = some (state.current, state.entry))

/-- Initial walk state (empty visited, boundary entry door) is valid. -/
lemma walkValid_init {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀) (hbdry₀ : K.adj s₀ k₀ = none) :
    let state : KuhnState d N c K :=
      { current := s₀, entry := k₀, entry_is_door := hdoor₀,
        visited := ∅, current_not_visited := Finset.notMem_empty _ }
    WalkValid hKuhn state (fun _ => none) none := by
  intro state
  constructor
  · -- has_record: visited = ∅
    intro s hs; exact absurd hs (Finset.not_mem_empty _)
  · -- doors_valid: rec = fun _ => none, so no records
    intro s k_in k_out h; simp at h
  · -- entry_from_chain: no records
    intro s k_in k_out h; simp at h
  · -- exit_to_chain: no records
    intro s k_in k_out h; simp at h
  · -- pred_spec: pred = none, entry k₀ is boundary
    exact Or.inl ⟨rfl, hbdry₀⟩

/-- The non-revisiting theorem: under WalkValid, a kuhnWalk step from current
    via k_out cannot lead to any previously visited simplex or current itself.

    Proof splits on whether the would-be revisit target s' is:
    (a) the predecessor (→ kuhnWalk_no_immediate_back)
    (b) a non-predecessor visited simplex (→ 3-door contradiction via adj_unique_facet) -/
theorem kuhn_step_nonrevisit {c : Coloring d N} {K : SpernerTriangulation d N}
    {hKuhn : IsKuhnCompatible c K}
    {state : KuhnState d N c K}
    {rec : DoorRecord d N K} {pred : Option K.Simplex}
    (hvalid : WalkValid hKuhn state rec pred)
    {k_out : Fin (d + 1)} (hne_entry : k_out ≠ state.entry)
    (hdoor_out : isDoorAt c K state.current k_out)
    {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj state.current k_out = some (s', k')) :
    s' ∉ state.visited ∪ {state.current} := by
  simp only [Finset.mem_union, Finset.mem_singleton]; push_neg
  refine ⟨K.adj_ne _ _ _ _ hadj, ?_⟩
  intro hmem
  -- k' is a door at s' (via door_transfer on hadj + hdoor_out)
  have hdoor_k' : isDoorAt c K s' k' := (door_transfer hadj).mp hdoor_out
  -- Get door record for s'
  obtain ⟨k_in_s, k_out_s, hrec_s⟩ := hvalid.has_record s' hmem
  obtain ⟨hdoor_in_s, hdoor_out_s, hne_s⟩ := hvalid.doors_valid s' k_in_s k_out_s hrec_s
  -- Case split via exit_to_chain for s'
  rcases hvalid.exit_to_chain s' k_in_s k_out_s hrec_s with
  | Or.inl ⟨hpred_eq, q, hadj_pred⟩ =>
      -- s' is the predecessor: K.adj s' k_out_s = some(current, q)
      -- By adj_symm: K.adj current q = some(s', k_out_s)
      have hadj_back : K.adj state.current q = some (s', k_out_s) :=
        K.adj_symm _ _ _ _ hadj_pred
      -- By pred_spec, pred = some s' and K.adj s' k_exit = some(current, state.entry)
      -- so state.entry is the entry into current from s'
      rcases hvalid.pred_spec with
      | Or.inl ⟨hpred_none, _⟩ =>
          -- pred = none but we have pred = some s': contradiction
          rw [hpred_none] at hpred_eq; exact absurd hpred_eq (by simp)
      | Or.inr ⟨s_pred, k_exit, hpred_some, _, hadj_pred_spec⟩ =>
          rw [hpred_some] at hpred_eq
          -- hpred_eq : some s_pred = some s'
          have hs'_eq : s_pred = s' := Option.some_inj.mp hpred_eq
          subst hs'_eq
          -- K.adj s' k_exit = some(current, state.entry)
          -- kuhnWalk_no_immediate_back: K.adj current k_out ≠ some(s', _)
          exact kuhnWalk_no_immediate_back K s' k_exit state.current state.entry
            hadj_pred_spec k_out hne_entry k' hadj
  | Or.inr ⟨s_out, k_out', hadj_exit, hs_out_vis⟩ =>
      -- s' is a non-predecessor: K.adj s' k_out_s = some(s_out, ...) with s_out ∈ visited
      -- Need 3 distinct doors at s': k_in_s, k_out_s, k'
      -- Distinctness of k' from k_out_s: adj_unique_facet (s_out ≠ current)
      have hs_out_ne_current : s_out ≠ state.current :=
        fun h => absurd (h ▸ hs_out_vis) state.current_not_visited
      -- K.adj s' k' = some(current, k_out) via adj_symm
      have hadj_back : K.adj s' k' = some (state.current, k_out) :=
        K.adj_symm _ _ _ _ hadj
      -- k' ≠ k_out_s: adj_unique_facet on s' (two different neighbors)
      have hk'_ne_kout : k' ≠ k_out_s := by
        intro heq; subst heq
        -- K.adj s' k' = some(current, ...) and K.adj s' k' = some(s_out, ...)
        -- so current = s_out, contradicting hs_out_ne_current
        rw [hadj_back] at hadj_exit
        have h := Option.some_inj.mp hadj_exit; exact hs_out_ne_current (Prod.mk.inj h).1.symm
      -- k' ≠ k_in_s: from entry_from_chain
      have hk'_ne_kin : k' ≠ k_in_s := by
        intro heq; subst heq
        rcases hvalid.entry_from_chain s' k_in_s k_out_s hrec_s with
        | Or.inl hbdry =>
            -- K.adj s' k_in_s = none, but K.adj s' k' = some(current,...) ≠ none
            rw [hbdry] at hadj_back; exact absurd hadj_back (by simp)
        | Or.inr ⟨s_prev, k_prev, hadj_entry, hs_prev_vis⟩ =>
            -- K.adj s' k_in_s = some(s_prev, ...) with s_prev ∈ visited
            -- K.adj s' k' = some(current, ...) and K.adj s' k_in_s = some(s_prev, ...)
            -- adj_unique_facet: current = s_prev (since k' = k_in_s)
            -- But s_prev ∈ visited and current ∉ visited: contradiction
            have : state.current = s_prev := by
              rw [hadj_back] at hadj_entry
              exact (Option.some.inj hadj_entry).1
            exact absurd (this ▸ hs_prev_vis) state.current_not_visited
      -- Three distinct doors k', k_in_s, k_out_s at s': contradiction!
      exact kuhn_three_doors_contradiction hKuhn s' k' k_in_s k_out_s
        hdoor_k' hdoor_in_s hdoor_out_s hk'_ne_kin.symm hk'_ne_kout.symm hne_s

/-- WalkValid is preserved by one step of the Kuhn walk.
    When current (s_n) steps to s' via k_out, the new state has:
    - visited ∪ {s_n} as visited set
    - s' as current, k_out' as entry
    - s_n as the new predecessor
    The door record is updated: s_n ↦ (state.entry, k_out). -/
lemma walkValid_step {c : Coloring d N} {K : SpernerTriangulation d N}
    {hKuhn : IsKuhnCompatible c K}
    {state : KuhnState d N c K}
    {rec : DoorRecord d N K} {pred : Option K.Simplex}
    (hvalid : WalkValid hKuhn state rec pred)
    {k_out : Fin (d + 1)} (hne_entry : k_out ≠ state.entry)
    (hdoor_out : isDoorAt c K state.current k_out)
    {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj state.current k_out = some (s', k'))
    (hs'_not_vis : s' ∉ state.visited ∪ {state.current}) :
    let new_state : KuhnState d N c K :=
      { current := s', entry := k', entry_is_door := (door_transfer hadj).mp hdoor_out,
        visited := state.visited ∪ {state.current},
        current_not_visited := hs'_not_vis }
    let new_rec : DoorRecord d N K := fun s =>
      if s = state.current then some (state.entry, k_out) else rec s
    WalkValid hKuhn new_state new_rec (some state.current) := by
  intro new_state new_rec
  constructor
  · -- has_record: ∀ s ∈ new_state.visited = old_visited ∪ {current}
    intro s hs
    simp only [new_state, Finset.mem_union, Finset.mem_singleton] at hs
    rcases hs with hs_old | rfl
    · obtain ⟨k_in, k_out_s, hrec_s⟩ := hvalid.has_record s hs_old
      exact ⟨k_in, k_out_s, by simp [new_rec, show s ≠ state.current from
        fun h => absurd (h ▸ hs_old) state.current_not_visited, hrec_s]⟩
    · exact ⟨state.entry, k_out, by simp [new_rec]⟩
  · -- doors_valid
    intro s k_in k_out_s hrec
    simp only [new_rec] at hrec
    split_ifs at hrec with heq
    · -- s = state.current: record is (state.entry, k_out)
      have hrec' := Option.some_inj.mp hrec; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrec'
      exact ⟨state.entry_is_door, hdoor_out, hne_entry⟩
    · -- s ≠ state.current: use old record
      exact hvalid.doors_valid s k_in k_out_s hrec
  · -- entry_from_chain
    intro s k_in k_out_s hrec
    simp only [new_rec, new_state] at hrec ⊢
    split_ifs at hrec with heq
    · -- s = state.current
      have hrec' := Option.some_inj.mp hrec; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrec'
      rcases hvalid.pred_spec with
      | Or.inl ⟨_, hbdry⟩ => exact Or.inl hbdry
      | Or.inr ⟨s_pred, k_exit, _, hs_pred_vis, hadj_pred⟩ =>
          -- hadj_pred : K.adj s_pred k_exit = some(state.current, state.entry)
          -- adj_symm: K.adj state.current state.entry = some(s_pred, k_exit)
          exact Or.inr ⟨s_pred, k_exit, K.adj_symm _ _ _ _ hadj_pred,
            Finset.mem_union_left _ hs_pred_vis⟩
    · -- s ≠ state.current: use old entry_from_chain
      rcases hvalid.entry_from_chain s k_in k_out_s hrec with
      | Or.inl h => exact Or.inl h
      | Or.inr ⟨s_prev, k_prev, hadj_prev, hs_prev⟩ =>
          exact Or.inr ⟨s_prev, k_prev, hadj_prev, Finset.mem_union_left _ hs_prev⟩
  · -- exit_to_chain
    intro s k_in k_out_s hrec
    simp only [new_rec, new_state] at hrec ⊢
    split_ifs at hrec with heq
    · -- s = state.current: exits to s' = new current
      have hrec' := Option.some_inj.mp hrec; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrec'
      exact Or.inl ⟨rfl, k', hadj⟩
    · -- s ≠ state.current: use old exit_to_chain
      rcases hvalid.exit_to_chain s k_in k_out_s hrec with
      | Or.inl ⟨hpred_eq, q, hadj_exit⟩ =>
          -- s was old predecessor: old current was its exit target
          -- old current is now in new visited
          exact Or.inr ⟨state.current, q, hadj_exit,
            Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)⟩
      | Or.inr ⟨s_out, k_out', hadj_exit, hs_out_vis⟩ =>
          exact Or.inr ⟨s_out, k_out', hadj_exit, Finset.mem_union_left _ hs_out_vis⟩
  · -- pred_spec: new pred = some state.current, which exits to s' = new current via k'
    exact Or.inr ⟨state.current, k_out, rfl,
      Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl), hadj⟩

-- ============================================================
-- SECTION IX: Main Theorems
-- ============================================================

/-- FC existence from a boundary door (non-constructive, via parity).

    Given a Sperner coloring and a Kuhn-compatible triangulation,
    if the boundary-door count on face d is odd and we have a specific
    boundary door (s₀, k₀), then a fully-colored simplex exists.

    **Proof**: Direct application of `sperner_ndim` (the parity theorem).
    The Kuhn walk provides a CONSTRUCTIVE path to such a simplex (see
    `kuhnPathStart_finds_fc_existential`), but existence alone follows from parity.

    The hypotheses `s₀, k₀, hdoor₀, hbdry₀, hKuhn` describe the walk starting
    conditions; the actual existence proof uses only `hc` and `hbdry_odd`. -/
theorem kuhn_path_terminates {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) :
    ∃ s : K.Simplex, IsFC c K s :=
  sperner_ndim c K hc hbdry_odd

/-- If the current simplex is FC, kuhnWalk returns it immediately (base case). -/
/-- Equation lemma: kuhnWalk at FC returns current simplex (used in fc_if_started_fc). -/
private lemma kuhnWalk_succ_eq_current_of_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (n : ℕ) (state : KuhnState d N c K)
    (hfc : IsFC c K state.current) :
    kuhnWalk c K hKuhn (n + 1) state = state.current := by
  simp only [kuhnWalk, if_pos hfc]

theorem kuhnWalk_fc_if_started_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (fuel : ℕ) (state : KuhnState d N c K)
    (hfc : IsFC c K state.current) :
    IsFC c K (kuhnWalk c K hKuhn fuel state) := by
  cases fuel with
  | zero => exact hfc
  | succ n => rw [kuhnWalk_succ_eq_current_of_fc hKuhn n state hfc]; exact hfc

-- ============================================================
-- SECTION X: Kuhn Path from Boundary Door
-- ============================================================

/-- The Kuhn algorithm starting from a boundary door (s₀, k₀) finds an FC simplex.

    Starting state: simplex s₀ with boundary door k₀ (K.adj s₀ k₀ = none).
    The algorithm:
    1. Check if s₀ is FC: done!
    2. If not: find exit door k_out ≠ k₀ of s₀
    3. Move to s₁ = (K.adj s₀ k_out).fst, entering via k_out' = (K.adj s₀ k_out).snd
    4. Repeat from s₁ with entry door k_out'

    The path terminates at an FC simplex because:
    - The door graph has no cycles containing boundary vertices
    - Each path from a boundary vertex reaches another boundary vertex or FC simplex
    - FC simplices have exactly 1 door (odd degree) and serve as endpoints -/
def kuhnPathStart (c : Coloring d N) (K : SpernerTriangulation d N)
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) : K.Simplex :=
  let state : KuhnState d N c K := {
    current := s₀
    entry := k₀
    entry_is_door := hdoor₀
    visited := ∅
    current_not_visited := Finset.notMem_empty _
  }
  kuhnWalk c K hKuhn (Fintype.card K.Simplex) state

/-- Special case: if s₀ is already FC, kuhnPathStart finds it immediately. -/
theorem kuhnPathStart_is_fc_of_fc_start {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none)
    (hfc₀ : IsFC c K s₀) :
    IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) :=
  kuhnWalk_fc_if_started_fc hKuhn _ _ hfc₀

/-- Axiom: there exists a boundary door from which kuhnPathStart finds an FC simplex.

    **Mathematical proof** (pending Lean formalization):
    Define τ on B_nfc = {boundary doors whose walk ends at a non-FC boundary exit}:
      τ(s₀, k₀) = (sₙ, k_exit_n) where the walk from (s₀, k₀) exits via boundary at sₙ.

    τ is a fixed-point-free involution on B_nfc:
    - τ∘τ = id: the reversed walk uniquely retraces the forward walk (Kuhn compatibility
      gives unique exit at each non-FC simplex; adj_unique_facet gives unique adjacency).
    - No fixed points: if τ(s₀,k₀) = (s₀,k₀) then the walk is a cycle, contradicting
      non-revisiting (proved by kuhn_step_nonrevisit + WalkValid).

    By even_card_fpf_invol (SpernerNDim): |B_nfc| is even.
    |B| = |B_fc| + |B_nfc| is odd (hbdry_odd) → |B_fc| is odd ≥ 1.

    **What remains**: Walk reversibility (τ∘τ=id). Non-revisiting (the fixed-point-free
    part) is FULLY PROVED by kuhn_step_nonrevisit + WalkValid invariant.

    Proof sketch for τ∘τ=id:
    Given walk from (s₀, k₀) [boundary] → s₁ → ... → sₙ → exits at boundary (kₙ_exit):
    - At sₙ: entry = kₙ, exit = kₙ_exit (boundary). IsKuhnCompatible gives ≤2 doors.
    - At sₙ₋₁: entry = kₙ₋₁, exit was k_adj to sₙ. Reversed walk: entry = kₙ_exit,
      unique exit at sₙ is kₙ (= K.adj.symm of the forward step), continuing backward.
    - Full reversal: τ(sₙ, kₙ_exit) = (s₀, k₀) by induction on walk length.

    The Lean formalization gap is the inductive walk reversal proof using
    kuhn_step_nonrevisit + IsKuhnCompatible + adj_unique_facet. -/
theorem kuhn_path_existential_ax {d N : ℕ} {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none),
      IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) := by
  /- Walk-pairing involution argument (Kuhn 1968):
     τ pairs boundary non-FC doors; τ is FPF by non-revisiting (proved).
     τ∘τ=id follows from walk reversibility (the remaining Lean gap).
     By even_card_fpf_invol, |B_nfc| even; |B| odd → |B_fc| ≥ 1. -/
  sorry

/-- EXISTENTIAL: There exists a boundary door from which kuhnPathStart finds FC.

    Proved from kuhn_path_existential_ax (which carries a sorry for walk reversibility).
    Non-revisiting is FULLY PROVED (kuhn_step_nonrevisit + WalkValid).
    Walk reversibility (τ∘τ=id) is the remaining open formalization step. -/
theorem kuhnPathStart_finds_fc_existential {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none),
      IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) :=
  kuhn_path_existential_ax hKuhn hc hbdry_odd

end SpernerNDimOQ04
