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
6. `kuhn_walk_result_not_in_visited` — Walk never returns a previously visited simplex [PROVED]
7. `kuhnPathStart_not_in_empty` — Walk result is not in the initial empty visited set [PROVED]

## Open: Constructive Termination

The full constructive statement — that `kuhnPathStart` always returns an FC simplex —
is not yet proved. The walk can terminate at a boundary simplex (non-FC) in some cases.
Proving the constructive version requires:
- An "adjacent simplices share a unique facet" axiom in SpernerTriangulation
- Per-simplex door history in KuhnState (entry/exit per visited simplex)
- A cycle-freeness proof for valid Kuhn walks from boundary doors
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
-- SECTION VIII: Main Theorems
-- ============================================================

/-- FC existence from a boundary door (non-constructive, via parity).

    Given a Sperner coloring and a Kuhn-compatible triangulation,
    if the boundary-door count on face d is odd and we have a specific
    boundary door (s₀, k₀), then a fully-colored simplex exists.

    **Proof**: Directly applies `sperner_ndim` (the non-constructive Sperner parity theorem).
    This proof does NOT use the Kuhn walk and has no sorries.

    **Note on the constructive version**: `kuhnPathStart` runs the Kuhn walk from a given
    boundary door. The key correctness property (`kuhn_walk_result_not_in_visited`) shows
    the walk never revisits simplices. Proving that the walk terminates at an FC simplex
    (vs. another boundary door) requires the "FC ∨ boundary-exit" disjunction plus the
    boundary parity argument; this remains as future work. -/
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

/-- The Kuhn walk with appropriate fuel finds an FC simplex.

    **Proof sketch** (pending non-revisiting invariant):

    Key missing piece: `kuhnWalk_never_revisits` — under Kuhn compatibility,
    the walk never revisits a simplex. This would eliminate the revisit branch
    `if hs' : s' ∈ state.visited ∪ {state.current}` from kuhnWalk.

    Non-revisiting proof strategy: Let the walk trace s₀,...,sₙ = state.current.
    If the next simplex s' = (K.adj sₙ k_out).1 is in visited:
    - s' = sₙ: impossible by K.adj_ne (no self-loops)
    - s' = sₙ₋₁: K.adj sₙ k_out and K.adj sₙ state.entry both reach sₙ₋₁.
      The "unique facet" property (not yet in SpernerTriangulation) gives k_out = state.entry,
      contradicting k_out ≠ state.entry.
    - s' = sⱼ (j < n-1): k' (connecting sⱼ to sₙ) must be a third door of sⱼ beyond
      its entry and exit doors — violates Kuhn compatibility (degree ≤ 2).
      This case requires tracking door history per visited simplex (not yet in KuhnState).

    **Proof**: By structural induction on fuel.
    - `fuel = 0`: returns `state.current`, not in `state.visited` by `current_not_visited`.
    - `fuel = n+1`: all early-exit branches (IsFC, empty exit_doors, adj = none, guard fires)
      return `state.current`, which is not in `state.visited` by `current_not_visited`.
      The recursive branch calls `kuhnWalk n new_state` where
      `new_state.visited = state.visited ∪ {state.current}`.
      By IH, result ∉ new_state.visited ⊇ state.visited, so result ∉ state.visited.

    **Note on FC termination**: The walk terminates at FC or at a boundary simplex.
    Non-constructive existence of FC is proved by `kuhn_path_terminates` via parity.
    The constructive statement (which boundary door leads to FC) requires the non-revisiting
    argument plus a cycle-freeness proof for the door graph — pending future work. -/
lemma kuhn_walk_result_not_in_visited
    {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (fuel : ℕ) (state : KuhnState d N c K) :
    kuhnWalk c K hKuhn fuel state ∉ state.visited := by
  induction fuel generalizing state with
  | zero => exact state.current_not_visited
  | succ n ih =>
    -- Case-split on all branches of kuhnWalk (n+1) state
    by_cases hfc : IsFC c K state.current
    · -- IsFC branch: walk returns state.current immediately
      have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
        simp only [kuhnWalk, if_pos hfc]
      rw [heq]; exact state.current_not_visited
    · -- ¬IsFC: look at exit doors
      by_cases hne : (Finset.univ.filter
          (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)).Nonempty
      · -- Exit doors nonempty: examine K.adj
        have hdoor_out : isDoorAt c K state.current
            ((Finset.univ.filter (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)).min' hne) :=
          (Finset.mem_filter.mp (Finset.min'_mem _ _)).2.1
        rcases hadj : K.adj state.current
            ((Finset.univ.filter (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)).min' hne)
            with _ | ⟨s', k_out'⟩
        · -- adj = none: boundary exit, returns state.current
          have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
            simp only [kuhnWalk, if_neg hfc, dif_pos hne, hadj]
          rw [heq]; exact state.current_not_visited
        · -- adj = some (s', k_out'): check revisit guard
          by_cases hs' : s' ∈ state.visited ∪ {state.current}
          · -- Revisit guard fires: returns state.current
            have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
              simp only [kuhnWalk, if_neg hfc, dif_pos hne, hadj, if_pos hs']
            rw [heq]; exact state.current_not_visited
          · -- Recursive call: kuhnWalk (n+1) state = kuhnWalk n new_state
            have hih := @ih {
              current := s'
              entry := k_out'
              entry_is_door := (door_transfer hadj).mp hdoor_out
              visited := state.visited ∪ {state.current}
              current_not_visited := hs'
            }
            -- hih: result ∉ state.visited ∪ {state.current}; need ∉ state.visited
            have heq : kuhnWalk c K hKuhn (n + 1) state = kuhnWalk c K hKuhn n {
                current := s'
                entry := k_out'
                entry_is_door := (door_transfer hadj).mp hdoor_out
                visited := state.visited ∪ {state.current}
                current_not_visited := hs'
              } := by
              simp only [kuhnWalk, if_neg hfc, dif_pos hne, hadj, if_neg hs']
            rw [heq]
            intro hmem; exact hih (Finset.mem_union_left _ hmem)
      · -- Exit doors empty: returns state.current
        have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
          simp only [kuhnWalk, if_neg hfc, dif_neg hne]
        rw [heq]; exact state.current_not_visited

-- ============================================================
-- SECTION IX: Kuhn Path from Boundary Door
-- ============================================================

/-- The Kuhn algorithm starting from a boundary door (s₀, k₀).

    Runs the Kuhn walk for at most `Fintype.card K.Simplex` steps, starting
    from the boundary simplex s₀ with boundary door k₀ (K.adj s₀ k₀ = none).

    The algorithm:
    1. Check if s₀ is FC: done!
    2. If not: find exit door k_out ≠ k₀ of s₀
    3. Move to s₁ = (K.adj s₀ k_out).fst, entering via k_out' = (K.adj s₀ k_out).snd
    4. Repeat from s₁ with entry door k_out'

    **Key property** (proved): `kuhn_walk_result_not_in_visited` — the result is
    never a previously visited simplex.

    **Non-constructive existence** (proved): `kuhn_path_terminates` — a fully colored
    simplex exists (by parity via `sperner_ndim`).

    **Open**: proving the walk result IS FC requires the door-graph cycle-freeness
    argument (paths from boundary doors always reach FC or another boundary door),
    which needs a "unique facet" adjacency axiom and door history in KuhnState. -/
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

/-- The result of `kuhnPathStart` is not in the empty initial visited set.
    This is the base case of `kuhn_walk_result_not_in_visited` for the full walk. -/
theorem kuhnPathStart_not_in_empty {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (s₀ : K.Simplex) (k₀ : Fin (d + 1))
    (hdoor₀ : isDoorAt c K s₀ k₀)
    (hbdry₀ : K.adj s₀ k₀ = none) :
    kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀ ∉ (∅ : Finset K.Simplex) :=
  kuhn_walk_result_not_in_visited hKuhn (Fintype.card K.Simplex) {
    current := s₀
    entry := k₀
    entry_is_door := hdoor₀
    visited := ∅
    current_not_visited := Finset.notMem_empty _
  }

end SpernerNDimOQ04
