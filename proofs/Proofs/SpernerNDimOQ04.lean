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
5. `kuhnPathStart_is_fc` — The walk terminates at an FC simplex (depends on kuhn_walk_reaches_fc)
6. `kuhn_path_terminates` — FC simplex exists given a boundary door
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
-- SECTION VIII: Core Walk Correctness (Main Blocker)
-- ============================================================

/-- The Kuhn walk with sufficient fuel finds an FC simplex from any valid state.

    **STATUS**: One sorry remains. This is the core mathematical obligation.

    **What needs to be proved**:
    The walk's termination conditions must all guarantee FC. The `kuhnWalk` function
    terminates (returns state.current) in these cases:
    1. `IsFC c K state.current` — correct, current is FC ✓
    2. `fuel = 0` — incorrect if current is non-FC
    3. `exit_doors.isEmpty` — non-FC with 0 doors; shouldn't occur if entered
    4. `K.adj state.current k_out = none` — boundary exit, current may be non-FC
    5. `s' ∈ state.visited ∪ {state.current}` — revisit guard, current may be non-FC

    Cases (2)-(5) must be eliminated:
    - (2) is handled by choosing fuel = Fintype.card K.Simplex - visited.card
    - (3) follows from nonfc_with_door_has_unique_exit (entry door ⟹ exit door exists)
    - (4) requires: the walk never hits a second boundary door (needs IsSperner c +
          unique-boundary-door-on-face-d assumption)
    - (5) requires: the NON-REVISITING INVARIANT

    **Non-Revisiting Invariant** (why the walk never revisits):
    Suppose s' = K.adj state.current k_out arrives in state.visited.
    By adj_symm: K.adj s' k_out' = some (state.current, k_out).
    When s' was previously the current at time j:
    - s' had door k_out' (which leads to state.current)
    - s' exited via the unique other door k_exit ≠ k_out' (by nonfc_with_door_has_unique_exit)
    - OR s' exited via k_out', moving to state.current at time j+1
    In the second case, state.current was visited at time j+1 < now,
    so state.current ∈ state.visited — contradicting current_not_visited.
    In the first case, s' has 2 doors {k_out', k_exit}, and exited via k_exit.
    But then s' can only be re-entered via the OTHER door (k_out'), which is
    the entry from state.current. This forces state.current to be visited, contradiction.

    **Blocker**: Formalizing this requires tracking NOT just the visited set but
    the sequence of (simplex, exit-door) pairs used. The current KuhnState structure
    stores only the visited set, losing the edge information needed to complete
    the contradiction. A stronger invariant would be required.

    **Possible fix**: Add a `prev_simplex : Option K.Simplex` field and a
    `prev_exit_door_leads_to_current` invariant to KuhnState. Then the
    non-revisiting argument becomes: if s' ∈ visited, it was previously current,
    its exit led toward state.current via a chain, and the chain closes a cycle —
    contradicting current_not_visited via adj_symm and the predecessor invariant. -/
theorem kuhn_walk_reaches_fc {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (state : KuhnState d N c K)
    (hfuel_sufficient : state.visited.card + (Fintype.card K.Simplex - state.visited.card) =
                        Fintype.card K.Simplex) :
    IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex - state.visited.card) state) := by
  -- SORRY: Requires non-revisiting invariant (see docstring above for full analysis).
  -- Additional hypotheses needed: IsSperner c and unique-boundary-door condition.
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
  -- Apply kuhn_walk_reaches_fc
  have hreach : IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex - state₀.visited.card) state₀) :=
    kuhn_walk_reaches_fc hKuhn state₀ hfuel
  -- Simplify fuel: Fintype.card K.Simplex - 0 = Fintype.card K.Simplex
  rw [hcard, Nat.sub_zero] at hreach
  -- hreach : IsFC c K (kuhnWalk c K hKuhn (Fintype.card K.Simplex) state₀)
  -- kuhnPathStart is definitionally kuhnWalk (Fintype.card K.Simplex) state₀
  exact hreach

/-- Existence of FC simplex: given a Kuhn-compatible triangulation with a boundary door,
    there exists a fully-colored simplex.

    The constructive witness is kuhnPathStart: the Kuhn walk from (s₀, k₀) returns an
    FC simplex by kuhnPathStart_is_fc. This reduces the existence claim to the
    walk correctness theorem (kuhn_walk_reaches_fc, which has one remaining sorry). -/
theorem kuhn_path_terminates {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) :
    ∃ s : K.Simplex, IsFC c K s :=
  ⟨kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀,
   kuhnPathStart_is_fc hKuhn s₀ k₀ hdoor₀ hbdry₀⟩

end SpernerNDimOQ04
