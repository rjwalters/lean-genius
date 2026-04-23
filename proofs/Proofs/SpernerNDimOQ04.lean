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

1. `fc_door_count_eq_one` — FC simplices have exactly 1 door
2. `nonfc_door_count_zero_or_two` — Non-FC simplices have 0 or 2 doors
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with an entry door has a unique exit door
4. `kuhnPathStart` — The Kuhn walk from a boundary door
5. `kuhnPathStart_is_fc` — The walk terminates at an FC simplex (BLOCKED: depends on kuhn_walk_reaches_fc sorry)
6. `kuhn_path_terminates` — FC simplex exists (PROVED non-constructively via sperner_ndim)
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
-- SECTION VIII: Non-Revisiting Infrastructure
-- ============================================================

/-- Path invariant for the Kuhn walk: every visited simplex was reached from a
    predecessor in the visited set. The three parts capture:
    (1) current was either the initial boundary vertex, or was reached from a visited predecessor;
    (2) visited is empty iff we are at the boundary (initial state);
    (3) every visited simplex has a door and a predecessor in visited. -/
def KuhnStateValid (c : Coloring d N) (K : SpernerTriangulation d N)
    (state : KuhnState d N c K) : Prop :=
  (K.adj state.current state.entry = none ∨
   ∃ s_pred k_pred, K.adj s_pred k_pred = some (state.current, state.entry) ∧
     s_pred ∈ state.visited) ∧
  (K.adj state.current state.entry = none → state.visited = ∅) ∧
  (∀ s ∈ state.visited, ∃ (e_s k_pred : Fin (d + 1)) (s_pred : K.Simplex),
    isDoorAt c K s e_s ∧
    K.adj s_pred k_pred = some (s, e_s) ∧
    s_pred ∈ state.visited)

/-- The initial state (boundary door, empty visited) satisfies KuhnStateValid. -/
lemma kuhnState_initial_valid (c : Coloring d N) (K : SpernerTriangulation d N)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀) (hbdry₀ : K.adj s₀ k₀ = none) :
    KuhnStateValid c K {
      current := s₀, entry := k₀, entry_is_door := hdoor₀,
      visited := ∅, current_not_visited := Finset.notMem_empty _ } := by
  refine ⟨Or.inl hbdry₀, fun _ => rfl, fun s hs => ?_⟩
  exact absurd hs (Finset.notMem_empty _)

/-- If s' ∈ visited and k' = s''s entry door (Case A of non-revisiting), adj_symm
    forces the predecessor of s' to be current, contradicting current_not_visited. -/
lemma guard_entry_case_impossible {c : Coloring d N} {K : SpernerTriangulation d N}
    {state : KuhnState d N c K}
    {k_out : Fin (d + 1)}
    {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj state.current k_out = some (s', k'))
    {e_s : Fin (d + 1)} {k_pred : Fin (d + 1)} {s_pred : K.Simplex}
    (he_s_adj : K.adj s_pred k_pred = some (s', e_s))
    (hs_pred_vis : s_pred ∈ state.visited)
    (hk'_is_entry : k' = e_s) : False := by
  have hadj_back : K.adj s' k' = some (state.current, k_out) := K.adj_symm _ _ _ _ hadj
  have he_s_back : K.adj s' e_s = some (s_pred, k_pred) := K.adj_symm _ _ _ _ he_s_adj
  rw [hk'_is_entry] at hadj_back
  rw [hadj_back] at he_s_back
  have ⟨heq_cur, _⟩ := Prod.mk.inj (Option.some.inj he_s_back)
  exact state.current_not_visited (heq_cur ▸ hs_pred_vis)

/-- The walk never steps to current itself: adj_ne rules it out immediately. -/
lemma guard_current_impossible {c : Coloring d N} {K : SpernerTriangulation d N}
    (state : KuhnState d N c K) {k_out : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj state.current k_out = some (s', k')) :
    s' ≠ state.current :=
  fun h => K.adj_ne _ _ _ _ hadj h.symm

-- ============================================================
-- SECTION IX: Core Walk Correctness (Main Blocker)
-- ============================================================

/-- The Kuhn walk with sufficient fuel finds an FC simplex from any valid state.

    **STATUS**: BLOCKED — the theorem as stated is MATHEMATICALLY INCORRECT.

    **The flaw** (identified in Session 4, 2026-04-23):
    The `kuhnWalk` function terminates in these cases:
    1. `IsFC c K state.current` — correct, current is FC ✓
    2. `fuel = 0` — incorrect if current is non-FC (handled by sufficient fuel)
    3. `exit_doors.isEmpty` — ruled out by nonfc_with_door_has_unique_exit ✓
    4. `K.adj state.current k_out = none` — **CASE 4 IS THE BLOCKER**

    **Case 4 is genuinely possible** (not just hard to formalize):
    After the first step, the walk enters non-initial simplices via interior doors.
    A simplex on the outer boundary can have:
    - Entry door k_entry (interior door, so k_entry ≠ Fin.last d)
    - Exit door k_out = Fin.last d (boundary door, K.adj s k_out = none)
    Then the walk terminates at a non-FC simplex! The theorem is false.

    **What IS true**: The walk terminates at either an FC simplex OR another boundary
    door (on face Fin.last d, by boundary_door_is_last_face with IsSperner c).
    The correct theorem is a disjunction:
      `IsFC c K result ∨ (∃ k, isDoorAt c K result k ∧ K.adj result k = none)`
    Deriving FC existence from this disjunction requires the boundary parity argument
    (odd count of boundary doors → at least one walk reaches FC, not another boundary).

    **Reformulation required**: This theorem needs to be stated as "FC or boundary exit"
    and then FC existence derived separately via the sperner_ndim parity theorem.
    Until reformulated, this sorry cannot be resolved. -/
theorem kuhn_walk_reaches_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (state : KuhnState d N c K)
    (hvalid : KuhnStateValid c K state)
    (hfuel_sufficient : state.visited.card + (Fintype.card K.Simplex - state.visited.card) =
                        Fintype.card K.Simplex) :
    IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex - state.visited.card) state) := by
  -- BLOCKED: The theorem is false as stated. Case 4 (boundary exit) can occur
  -- at non-initial walk steps even with IsSperner c. The theorem would need to be
  -- reformulated as "FC or boundary exit" before this sorry can be resolved.
  -- The non-constructive existence theorem (kuhn_path_terminates) uses sperner_ndim directly.
  sorry

-- ============================================================
-- SECTION IX: Kuhn Path from Boundary Door
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

/-- The simplex found by kuhnPathStart is fully colored.

    This follows from kuhn_walk_reaches_fc applied to the initial state:
    - Initial visited = ∅, so visited.card = 0
    - Fuel = Fintype.card K.Simplex - 0 = Fintype.card K.Simplex
    - kuhnPathStart is exactly kuhnWalk with this initial state and fuel

    Note: the sorry in kuhn_walk_reaches_fc is the only remaining obligation. -/
theorem kuhnPathStart_is_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) :
    IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) := by
  -- The initial KuhnState matching kuhnPathStart's internal state
  let state₀ : KuhnState d N c K := {
    current := s₀
    entry := k₀
    entry_is_door := hdoor₀
    visited := ∅
    current_not_visited := Finset.notMem_empty _
  }
  -- visited.card = 0, so fuel = Fintype.card K.Simplex - 0 = Fintype.card K.Simplex
  have hcard : state₀.visited.card = 0 := by simp [state₀]
  have hfuel : state₀.visited.card + (Fintype.card K.Simplex - state₀.visited.card) =
               Fintype.card K.Simplex := by simp [state₀]
  -- The initial state satisfies KuhnStateValid (boundary door, empty visited set)
  have hvalid : KuhnStateValid c K state₀ := kuhnState_initial_valid c K s₀ k₀ hdoor₀ hbdry₀
  -- Apply kuhn_walk_reaches_fc
  have hreach : IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex - state₀.visited.card) state₀) :=
    kuhn_walk_reaches_fc hKuhn state₀ hvalid hfuel
  -- Simplify fuel: Fintype.card K.Simplex - 0 = Fintype.card K.Simplex
  rw [hcard, Nat.sub_zero] at hreach
  -- hreach : IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex) state₀)
  -- kuhnPathStart is definitionally kuhnWalk (Fintype.card K.Simplex) state₀
  exact hreach

/-- Existence of FC simplex: given a Kuhn-compatible Sperner triangulation with an odd
    number of boundary doors on face d, there exists a fully-colored simplex.

    **Proof**: Directly applies `sperner_ndim` (the non-constructive Sperner parity theorem).
    This proof does NOT use the Kuhn walk and has no sorries.

    **Note on the constructive version**: `kuhnPathStart_is_fc` provides the algorithmic
    witness (the specific FC simplex found by running the walk from a given boundary door),
    but its proof depends on `kuhn_walk_reaches_fc` (which has 1 sorry and is BLOCKED:
    the theorem statement needs reformulation to handle mid-walk boundary exits). -/
theorem kuhn_path_terminates {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ s : K.Simplex, IsFC c K s :=
  sperner_ndim c K hc hbdry

end SpernerNDimOQ04
