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

1. `fc_door_count_eq_one` — FC simplices have exactly 1 door [PROVED]
2. `nonfc_door_count_zero_or_two` — Non-FC simplices have 0 or 2 doors [PROVED]
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with an entry door has a unique exit door [PROVED]
4. `kuhn_step` — One step of the Kuhn algorithm [PROVED]
5. `kuhn_path_terminates` — FC simplex exists (non-constructive, from parity) [PROVED]
6. `kuhn_walk_reaches_fc` — Walk correctness (pending non-revisiting invariant) [SORRY]
7. `kuhnPathStart_is_fc` — Constructive FC witness (pending walk correctness) [SORRY]
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
-- SECTION IX: Main Theorems
-- ============================================================

/-- FC existence from a boundary door (non-constructive, via parity).

    Given a Sperner coloring and a Kuhn-compatible triangulation,
    if the boundary-door count on face d is odd and we have a specific
    boundary door (s₀, k₀), then a fully-colored simplex exists.

    **Proof**: Direct application of `sperner_ndim` (the parity theorem).
    The Kuhn walk provides a CONSTRUCTIVE path to such a simplex (see
    `kuhnPathStart_is_fc`), but existence alone follows from parity.

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

/-- The Kuhn walk with appropriate fuel finds an FC simplex.

    **Proof sketch** (pending non-revisiting invariant):

    Non-revisiting cases:
    - s' = sₙ (self-loop): impossible by K.adj_ne.
    - s' = sₙ₋₁ (immediate back): proved by kuhnWalk_no_immediate_back (adj_unique_facet).
    - s' = sⱼ (j < n-1): sⱼ would have a THIRD door (entry kⱼ, exit k_exit_j, plus back-entry
      from sₙ). By door_transfer: the back-entry is a door. doorDegree sⱼ ≥ 3 > 2. Contradiction.
      This case requires per-simplex door history, not currently in KuhnState.

    Boundary exit analysis:
    - First step: ruled out by kuhnWalk_first_exit_interior (both boundary doors would
      equal Fin.last d, contradicting k_out ≠ entry).
    - Later steps: a simplex with INTERIOR entry k_in and BOUNDARY exit k_out.
      This terminates the walk at a non-FC simplex. Occurs when the walk "reaches the
      boundary on the other side." Ruled out by the global parity argument (hbdry_odd).

    **Status** (2026-04-25): kuhnWalk_no_immediate_back and kuhnWalk_first_exit_interior
    are now proved. Remaining: (1) general non-revisiting (j < n-1 case) needs per-simplex
    door history; (2) boundary-exit ruling-out needs global parity argument. -/
theorem kuhn_walk_reaches_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card)
    (state : KuhnState d N c K)
    (hfuel_sufficient : state.visited.card + (Fintype.card K.Simplex - state.visited.card) =
                        Fintype.card K.Simplex) :
    IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex - state.visited.card) state) := by
  -- Remaining sorry: general non-revisiting (needs per-simplex door history in KuhnState)
  -- + boundary-exit ruling-out (needs global parity argument via hbdry_odd).
  -- Key ingredient kuhnWalk_no_immediate_back (adj_unique_facet) is now proved.
  sorry

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

/-- EXISTENTIAL: There exists a boundary door from which kuhnPathStart finds FC.

    Proof strategy (pending):
    - Walk paths pair up boundary doors (start → end, both on face Fin.last d).
    - Pairing: if the walk from (s₀, k₀) terminates at (sₙ, k_out_n) via boundary exit,
      then (s₀, k₀) and (sₙ, k_out_n) are paired.
    - FC simplices' boundary doors are unpaired (degree 1, walk terminates immediately).
    - |unpaired boundary doors| = |FC simplices with boundary doors|.
    - Since total boundary door count is odd (hbdry_odd) and paired count is even:
      |unpaired| is odd ≥ 1 → ∃ FC simplex with a boundary door.
    - kuhnPathStart_is_fc_of_fc_start gives the result. -/
theorem kuhnPathStart_finds_fc_existential {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none),
      IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) := by
  -- Needs: walk-pairing argument + non-revisiting to show some boundary door is unpaired (FC).
  sorry

/-- UNIVERSAL: The simplex found by kuhnPathStart is fully colored, for all starting boundary doors.

    **Analysis** (2026-04-25): This theorem as stated may be FALSE for some starting
    boundary doors. The walk can terminate via "boundary exit" (K.adj sₙ k_out = none)
    returning a non-FC simplex. The correct statement is existential
    (kuhnPathStart_finds_fc_existential), or requires an additional hypothesis ruling out
    the boundary-exit termination for this specific starting door.

    **Proved ingredients** (2026-04-25):
    - kuhnWalk_no_immediate_back: s' = sₙ₋₁ revisit impossible (adj_unique_facet)
    - kuhnWalk_first_exit_interior: first step is never a boundary exit (boundary_door_is_last_face)
    - kuhnWalk_fc_if_started_fc: walk returns FC if already at FC
    - kuhnPathStart_is_fc_of_fc_start: works when s₀ is FC -/
theorem kuhnPathStart_is_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) :
    IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) := by
  -- Remaining sorry: global parity argument that boundary-exit termination cannot happen
  -- (needs walk-pairing + non-revisiting; key ingredients now proved above).
  sorry

end SpernerNDimOQ04
