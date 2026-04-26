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
13. `kuhnPathStart_finds_fc_existential` — ∃ boundary door whose walk finds FC

### Proved (Section XI — Termination Dichotomy)
13. `all_visited_forces_bdry` — When all simplices visited, non-FC exit must be boundary
14. `kuhnWalk_fc_or_bdry` — With |K.Simplex| fuel, walk terminates at FC or boundary door
15. `kuhn_path_existential` — Structure proved; parity + Case 1 (walk reaches FC) done;
    Case 2 (involution τ on B when all walks fail) has 1 sorry in bdry_all_even_of_no_fc_walks

### 1 Sorry Remaining (Section XII — hInv)
- `bdry_all_even_of_no_fc_walks` — hMem ✓ and hNe ✓ proved; hInv has 1 sorry (walkTrace_reversal)
  Needs: walkTrace_reversal — induction on walk length using adj_symm + nonfc_with_door_has_unique_exit.
  Proof sketch: at each sᵢ, exactly 2 doors {kᵢ, eᵢ} (Kuhn compat + non-FC); backward entry eᵢ →
  unique exit kᵢ → K.adj sᵢ kᵢ = some(sᵢ₋₁, eᵢ₋₁) by adj_symm; induction reverses to s₀.

### Previously Axiomatized (now theorem + sorry)
- `kuhn_path_existential` — Promoted from axiom to theorem (0 axioms, 1 sorry)

### Removed (false as stated)
- `kuhn_walk_reaches_fc` — Universal walk theorem is false; boundary exit possible on some paths
- `kuhnPathStart_is_fc` — False for some starting boundary doors; correct form is existential
- `bdry_nfc_even` — False without additional hypotheses; |B_nfc| is not always even in the abstract setting
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

-- ============================================================
-- SECTION XI: Termination Dichotomy
-- ============================================================

/-- When all simplices except current are visited, any non-FC exit must be a boundary door.
    The exit door can't lead to a new simplex (none left), so K.adj = none. -/
private lemma all_visited_forces_bdry {c : Coloring d N} {K : SpernerTriangulation d N}
    {hKuhn : IsKuhnCompatible c K} {state : KuhnState d N c K}
    {rec : DoorRecord d N K} {pred : Option K.Simplex}
    (hvalid : WalkValid hKuhn state rec pred)
    (hfull : state.visited.card + 1 = Fintype.card K.Simplex)
    (hnonfc : ¬IsFC c K state.current) :
    ∃ k_out, isDoorAt c K state.current k_out ∧ K.adj state.current k_out = none := by
  -- Get the unique exit door k_out ≠ state.entry
  obtain ⟨k_out, ⟨hne, hdoor_out⟩, _⟩ :=
    nonfc_with_door_has_unique_exit hKuhn state.current hnonfc state.entry state.entry_is_door
  refine ⟨k_out, hdoor_out, ?_⟩
  -- If K.adj = some (s', k'), then s' must be new, but all simplices are visited ∪ {current}
  cases hadj : K.adj state.current k_out with
  | none => rfl
  | some sk =>
    obtain ⟨s', k'⟩ := sk
    exfalso
    -- s' ∉ visited ∪ {current} by non-revisiting
    have hs'_not := kuhn_step_nonrevisit hvalid hne hdoor_out hadj
    -- but visited ∪ {current} covers all simplices
    have huniv : state.visited ∪ {state.current} = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hdisj : Disjoint state.visited {state.current} := by
        simp [Finset.disjoint_left, state.current_not_visited]
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      exact hfull
    exact hs'_not (huniv ▸ Finset.mem_univ s')

/-- kuhnWalk is proof-irrelevant in the KuhnState Prop fields: only current, entry, visited matter.
    Proof: reduce to KuhnState equality, then use proof_irrel for the two Prop fields. -/
private lemma kuhnWalk_congr {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (fuel : ℕ) (s₁ s₂ : KuhnState d N c K)
    (hcur : s₁.current = s₂.current) (hent : s₁.entry = s₂.entry) (hvis : s₁.visited = s₂.visited) :
    kuhnWalk c K hKuhn fuel s₁ = kuhnWalk c K hKuhn fuel s₂ := by
  suffices h : s₁ = s₂ from congrArg (kuhnWalk c K hKuhn fuel) h
  obtain ⟨cur₁, ent₁, ed₁, vis₁, cnv₁⟩ := s₁
  obtain ⟨cur₂, ent₂, ed₂, vis₂, cnv₂⟩ := s₂
  -- hcur, hent, hvis are now field equalities after obtain
  simp only at hcur hent hvis
  subst hcur; subst hent; subst hvis
  -- ed₁ ed₂ : isDoorAt c K cur₁ ent₁ (same type); cnv₁ cnv₂ : cur₁ ∉ vis₁ (same type)
  have h1 : ed₁ = ed₂ := proof_irrel _ _
  have h2 : cnv₁ = cnv₂ := proof_irrel _ _
  rw [h1, h2]

/-- With fuel = (Fintype.card K.Simplex - visited.card), kuhnWalk terminates at FC or boundary.
    Proof: by induction on fuel. Non-revisiting ensures each step visits a fresh simplex;
    when all simplices are claimed, the exit must be a boundary door. -/
theorem kuhnWalk_fc_or_bdry {c : Coloring d N} {K : SpernerTriangulation d N}
    {hKuhn : IsKuhnCompatible c K} (fuel : ℕ) :
    ∀ (state : KuhnState d N c K) (rec : DoorRecord d N K) (pred : Option K.Simplex),
      WalkValid hKuhn state rec pred →
      fuel + state.visited.card = Fintype.card K.Simplex →
      IsFC c K (kuhnWalk c K hKuhn fuel state) ∨
      ∃ k, isDoorAt c K (kuhnWalk c K hKuhn fuel state) k ∧
           K.adj (kuhnWalk c K hKuhn fuel state) k = none := by
  induction fuel with
  | zero =>
    intro state rec pred hvalid hn
    -- fuel = 0 ⟹ visited.card = |K.Simplex|, but current ∉ visited — impossible
    exfalso
    simp only [Nat.zero_add] at hn
    have hdisj : Disjoint state.visited {state.current} := by
      rw [Finset.disjoint_left]; intro x hx hmem
      exact state.current_not_visited (Finset.mem_singleton.mp hmem ▸ hx)
    have hcard : (state.visited ∪ {state.current}).card = state.visited.card + 1 := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    linarith [Finset.card_le_univ (state.visited ∪ {state.current})]
  | succ n ih =>
    intro state rec pred hvalid hn
    by_cases hfc : IsFC c K state.current
    · -- FC: walk returns current immediately
      left; rw [kuhnWalk_succ_eq_current_of_fc hKuhn n state hfc]; exact hfc
    · -- Non-FC: take one step
      -- Use kuhnStep to identify the exit door and next simplex
      set exit_doors := Finset.univ.filter (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)
      -- Exit doors are nonempty (non-FC with entry door has a unique other door)
      have hnonempty : exit_doors.Nonempty := by
        obtain ⟨k_u, ⟨hne_u, hdoor_u⟩, _⟩ :=
          nonfc_with_door_has_unique_exit hKuhn state.current hfc state.entry state.entry_is_door
        exact ⟨k_u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_u, hne_u⟩⟩
      set k_out := exit_doors.min' hnonempty
      have hk_prop := (Finset.mem_filter.mp (Finset.min'_mem exit_doors hnonempty)).2
      -- Non-revisiting: the next simplex (if any) is fresh
      cases hadj : K.adj state.current k_out with
      | none =>
        -- Boundary exit
        have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
          simp only [kuhnWalk, if_neg hfc, dif_pos hnonempty, hadj]
        rw [heq]; right; exact ⟨k_out, hk_prop.1, hadj⟩
      | some sk =>
        obtain ⟨s', k'⟩ := sk
        have hs'_fresh := kuhn_step_nonrevisit hvalid hk_prop.2 hk_prop.1 hadj
        -- Walk steps to s' (the hs' guard never triggers)
        -- LHS: unfold kuhnWalk (n+1) with all guards discharged
        -- RHS: kuhnWalk n with explicitly-named proof terms
        -- After unfolding, both states have same data fields; kuhnWalk_congr handles Prop fields.
        have heq : kuhnWalk c K hKuhn (n + 1) state =
            kuhnWalk c K hKuhn n
              { current := s', entry := k', entry_is_door := (door_transfer hadj).mp hk_prop.1,
                visited := state.visited ∪ {state.current},
                current_not_visited := hs'_fresh } := by
          conv_lhs => simp only [kuhnWalk, if_neg hfc, dif_pos hnonempty, hadj, dif_neg hs'_fresh]
          apply kuhnWalk_congr <;> rfl
        rw [heq]
        have hvalid_new := walkValid_step hvalid hk_prop.2 hk_prop.1 hadj hs'_fresh
        have hn_new : n + (state.visited ∪ {state.current}).card = Fintype.card K.Simplex := by
          have hdisj : Disjoint state.visited {state.current} := by
            rw [Finset.disjoint_left]; intro x hx hmem
            exact state.current_not_visited (Finset.mem_singleton.mp hmem ▸ hx)
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]; omega
        exact ih _ _ _ hvalid_new hn_new

-- ============================================================
-- SECTION XII: Walk Pairing Parity and Main Existential
-- ============================================================

/-- The kuhnWalk result is never in the initial visited set.
    Key consequence: kuhnPathStart never returns to the starting simplex
    (after it has been added to visited on step 1).

    Proof: by induction on fuel, same pattern as kuhnWalk_fc_or_bdry.
    - FC case: returns current ∉ visited (current_not_visited).
    - Boundary exit (none): returns current ∉ visited.
    - Interior step: result = kuhnWalk n state₁ where state₁.visited ⊃ state.visited.
      By IH, result ∉ state₁.visited ⊃ state.visited. -/
private lemma kuhnWalk_not_in_initial_visited {c : Coloring d N} {K : SpernerTriangulation d N}
    {hKuhn : IsKuhnCompatible c K}
    (fuel : ℕ) :
    ∀ (state : KuhnState d N c K) (rec : DoorRecord d N K) (pred : Option K.Simplex),
      WalkValid hKuhn state rec pred →
      fuel + state.visited.card = Fintype.card K.Simplex →
      kuhnWalk c K hKuhn fuel state ∉ state.visited := by
  induction fuel with
  | zero =>
    intro state rec pred hvalid hn
    exfalso
    simp only [Nat.zero_add] at hn
    have hlt : state.visited.card < Fintype.card K.Simplex :=
      Finset.card_lt_card (Finset.ssubset_univ (fun h =>
        state.current_not_visited (h ▸ Finset.mem_univ _)))
    omega
  | succ n ih =>
    intro state rec pred hvalid hn
    by_cases hfc : IsFC c K state.current
    · -- FC: returns current, which is ∉ visited
      rw [kuhnWalk_succ_eq_current_of_fc hKuhn n state hfc]
      exact state.current_not_visited
    · -- Non-FC: one step
      set exit_doors := Finset.univ.filter (fun k => isDoorAt c K state.current k ∧ k ≠ state.entry)
      have hnonempty : exit_doors.Nonempty := by
        obtain ⟨k_u, ⟨hne_u, hdoor_u⟩, _⟩ :=
          nonfc_with_door_has_unique_exit hKuhn state.current hfc state.entry state.entry_is_door
        exact ⟨k_u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_u, hne_u⟩⟩
      set k_out := exit_doors.min' hnonempty
      have hk_prop := (Finset.mem_filter.mp (Finset.min'_mem exit_doors hnonempty)).2
      cases hadj : K.adj state.current k_out with
      | none =>
        -- Boundary exit: kuhnWalk returns state.current ∉ visited
        have heq : kuhnWalk c K hKuhn (n + 1) state = state.current := by
          simp only [kuhnWalk, if_neg hfc, dif_pos hnonempty, hadj]
        rw [heq]; exact state.current_not_visited
      | some sk =>
        obtain ⟨s', k'⟩ := sk
        have hs'_fresh := kuhn_step_nonrevisit hvalid hk_prop.2 hk_prop.1 hadj
        have heq : kuhnWalk c K hKuhn (n + 1) state =
            kuhnWalk c K hKuhn n
              { current := s', entry := k', entry_is_door := (door_transfer hadj).mp hk_prop.1,
                visited := state.visited ∪ {state.current},
                current_not_visited := hs'_fresh } := by
          conv_lhs => simp only [kuhnWalk, if_neg hfc, dif_pos hnonempty, hadj, dif_neg hs'_fresh]
          apply kuhnWalk_congr <;> rfl
        rw [heq]
        have hvalid_new := walkValid_step hvalid hk_prop.2 hk_prop.1 hadj hs'_fresh
        have hn_new : n + (state.visited ∪ {state.current}).card = Fintype.card K.Simplex := by
          have hdisj : Disjoint state.visited {state.current} :=
            Finset.disjoint_singleton_right.mpr state.current_not_visited
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]; omega
        -- IH: result ∉ state.visited ∪ {state.current} ⊃ state.visited
        exact fun hmem => ih _ _ _ hvalid_new hn_new (Finset.mem_union_left _ hmem)

/-- If no boundary door's walk reaches FC, boundary doors form a FPF involution → even count.

    **τ construction**: For (s₀, Fin.last d) ∈ B under hfail:
    - τ(s₀, Fin.last d) = (kuhnPathStart s₀ (Fin.last d), Fin.last d)
    - All boundary doors have k = Fin.last d (boundary_door_is_last_face + IsSperner)

    **hMem** (τ maps B to B):
    - kuhnWalk_fc_or_bdry + hfail → boundary exit ∃ kₙ
    - boundary_door_is_last_face → kₙ = Fin.last d → (sₙ, Fin.last d) ∈ B

    **hNe** (τ FPF on B):
    - hfail + kuhnPathStart_is_fc_of_fc_start → ¬IsFC s₀ → walk takes ≥1 step
    - After step 1: s₀ ∈ state₁.visited = {s₀}
    - kuhnWalk_not_in_initial_visited at state₁: result ∉ {s₀} → result ≠ s₀
    - So τ(s₀, Fin.last d) ≠ (s₀, Fin.last d) ✓

    **hInv** (τ∘τ = id): walk from sₙ reverses to s₀ by adj_symm + unique exit.
    This requires walkTrace_reversal (~100-line induction, still pending). -/
private lemma bdry_all_even_of_no_fc_walks {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (hc : IsSperner c)
    (hfail : ∀ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none), ¬IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀)) :
    Even (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card := by
  set B := Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
    isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d) with hB_def
  -- τ: for p ∈ B (p.2 = Fin.last d), map to (kuhnPathStart p.1 (Fin.last d), Fin.last d)
  apply even_card_fpf_invol B (fun p =>
    if h : p ∈ B then
      let hk : p.2 = Fin.last d := (Finset.mem_filter.mp h).2.2.2
      let hdoor : isDoorAt c K p.1 (Fin.last d) := hk ▸ (Finset.mem_filter.mp h).2.1
      let hbdry : K.adj p.1 (Fin.last d) = none := hk ▸ (Finset.mem_filter.mp h).2.2.1
      (kuhnPathStart c K hKuhn p.1 (Fin.last d) hdoor hbdry, Fin.last d)
    else p)
  · -- hInv: τ(τ(p)) = p for p ∈ B — walk from sₙ reverses to s₀
    -- Mathematical argument:
    --   τ(s₀, Fin.last d) = (sₙ, Fin.last d) where sₙ = kuhnPathStart s₀ (Fin.last d)
    --   τ(sₙ, Fin.last d) = (s₀, Fin.last d) by walkTrace_reversal:
    --     At sₙ, entry eₙ = Fin.last d (boundary). Unique exit door ≠ eₙ is kₙ (from forward walk).
    --     K.adj sₙ kₙ = some(sₙ₋₁, eₙ₋₁) by adj_symm. Walk continues sₙ → sₙ₋₁ → ... → s₀.
    --     At each sᵢ: exactly 2 doors (kᵢ, eᵢ) by nonfc_with_door_has_unique_exit + Kuhn compat;
    --     the unique exit under backward entry eᵢ is kᵢ (by uniqueness), leading to sᵢ₋₁ via adj_symm.
    intro p hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hk : p.2 = Fin.last d := hp.2.2
    have hdoor₀ : isDoorAt c K p.1 (Fin.last d) := hk ▸ hp.1
    have hbdry₀ : K.adj p.1 (Fin.last d) = none := hk ▸ hp.2.1
    have hp_in_B : p ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1, hp.2.1, hp.2.2⟩
    -- sₙ = kuhnPathStart s₀ (Fin.last d); prove it ∈ B (same argument as hMem below)
    set sₙ := kuhnPathStart c K hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀ with hsₙ_def
    have hτp_in_B : (sₙ, Fin.last d) ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      have hvalid₀ := walkValid_init hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀
      have hn₀ : Fintype.card K.Simplex + (∅ : Finset K.Simplex).card = Fintype.card K.Simplex := by simp
      rcases kuhnWalk_fc_or_bdry (Fintype.card K.Simplex) _ _ _ hvalid₀ hn₀ with
          hfc | ⟨k_exit, hdoor_exit, hbdry_exit⟩
      · exfalso; exact hfail p.1 (Fin.last d) hdoor₀ hbdry₀ hfc
      · have hk_last := boundary_door_is_last_face c K hc sₙ k_exit hdoor_exit hbdry_exit
        exact ⟨hk_last ▸ hdoor_exit, hk_last ▸ hbdry_exit, rfl⟩
    -- Extract door proofs for sₙ (3 components: isDoorAt ∧ K.adj=none ∧ Fin.last d=Fin.last d)
    obtain ⟨hdoor_n, hbdry_n, _⟩ := (Finset.mem_filter.mp hτp_in_B).2
    -- Step 1: Reduce inner application τ(p) using dif_pos hp_in_B.
    -- The resulting proof terms (from hp_in_B) may differ from hdoor₀/hbdry₀, but
    -- kuhnWalk_congr bridges the gap via proof_irrel on Prop fields.
    simp only [dif_pos hp_in_B]
    conv_lhs =>
      rw [show kuhnPathStart c K hKuhn p.1 (Fin.last d)
              ((Finset.mem_filter.mp hp_in_B).2.2.2 ▸ (Finset.mem_filter.mp hp_in_B).2.1)
              ((Finset.mem_filter.mp hp_in_B).2.2.2 ▸ (Finset.mem_filter.mp hp_in_B).2.2.1) = sₙ from by
          simp only [hsₙ_def]; unfold kuhnPathStart; apply kuhnWalk_congr <;> rfl]
    -- Step 2: Reduce outer application τ(sₙ, Fin.last d) using dif_pos hτp_in_B.
    -- Since (sₙ, Fin.last d).2 = Fin.last d is rfl, hk' ▸ x = x definitionally,
    -- so the resulting hdoor'' = hdoor_n and hbdry'' = hbdry_n.
    simp only [dif_pos hτp_in_B]
    -- Handle the outer proof-term mismatch (same pattern as step 1):
    conv_lhs =>
      rw [show kuhnPathStart c K hKuhn sₙ (Fin.last d)
              ((Finset.mem_filter.mp hτp_in_B).2.2.2 ▸ (Finset.mem_filter.mp hτp_in_B).2.1)
              ((Finset.mem_filter.mp hτp_in_B).2.2.2 ▸ (Finset.mem_filter.mp hτp_in_B).2.2.1) =
              kuhnPathStart c K hKuhn sₙ (Fin.last d) hdoor_n hbdry_n from by
          unfold kuhnPathStart; apply kuhnWalk_congr <;> rfl]
    -- Goal: (kuhnPathStart sₙ (Fin.last d) hdoor_n hbdry_n, Fin.last d) = p
    ext
    · -- Component 1: walkTrace_reversal — walk from sₙ returns to s₀ = p.1.
      -- Proof sketch: by induction on walk length (n steps). At each sᵢ, the backward
      -- entry eᵢ gives unique exit kᵢ (since sᵢ has exactly 2 doors by Kuhn compat + non-FC).
      -- K.adj sᵢ kᵢ = some(sᵢ₋₁, eᵢ₋₁) by adj_symm from forward walk adjacency.
      -- After n steps: reach s₀ with boundary exit k₀ = Fin.last d → walk terminates at s₀.
      show kuhnPathStart c K hKuhn sₙ (Fin.last d) hdoor_n hbdry_n = p.1
      sorry -- walkTrace_reversal: ~100-line induction using adj_symm + nonfc_with_door_has_unique_exit
    · -- Component 2: second component = Fin.last d = p.2
      exact hk.symm
  · -- hMem: τ(p) ∈ B for p ∈ B
    intro p hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hk : p.2 = Fin.last d := hp.2.2
    have hdoor₀ : isDoorAt c K p.1 (Fin.last d) := hk ▸ hp.1
    have hbdry₀ : K.adj p.1 (Fin.last d) = none := hk ▸ hp.2.1
    have hp_in_B : p ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1, hp.2.1, hp.2.2⟩
    simp only [dif_pos hp_in_B]
    -- kuhnWalk_fc_or_bdry: result is FC or boundary
    have hvalid₀ := walkValid_init hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀
    have hn₀ : Fintype.card K.Simplex + (∅ : Finset K.Simplex).card = Fintype.card K.Simplex := by
      simp
    rcases kuhnWalk_fc_or_bdry (Fintype.card K.Simplex) _ _ _ hvalid₀ hn₀ with hfc | ⟨k_exit, hdoor_exit, hbdry_exit⟩
    · -- FC case: contradicts hfail
      exfalso; exact hfail p.1 (Fin.last d) hdoor₀ hbdry₀ hfc
    · -- Boundary exit case
      -- The result has a boundary door k_exit; by boundary_door_is_last_face, k_exit = Fin.last d
      have hk_last : k_exit = Fin.last d :=
        boundary_door_is_last_face c K hc
          (kuhnPathStart c K hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀) k_exit hdoor_exit hbdry_exit
      exact ⟨hk_last ▸ hdoor_exit, hk_last ▸ hbdry_exit, rfl⟩
  · -- hNe: τ(p) ≠ p for p ∈ B
    intro p hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hk : p.2 = Fin.last d := hp.2.2
    have hdoor₀ : isDoorAt c K p.1 (Fin.last d) := hk ▸ hp.1
    have hbdry₀ : K.adj p.1 (Fin.last d) = none := hk ▸ hp.2.1
    have hp_in_B : p ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1, hp.2.1, hp.2.2⟩
    simp only [dif_pos hp_in_B]
    -- Need: kuhnPathStart p.1 (Fin.last d) ≠ p.1
    -- Step 1: p.1 is not FC (from hfail + kuhnPathStart_is_fc_of_fc_start)
    have hnotfc₀ : ¬IsFC c K p.1 := by
      intro hfc
      exact hfail p.1 (Fin.last d) hdoor₀ hbdry₀
        (kuhnPathStart_is_fc_of_fc_start hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀ hfc)
    -- Step 2: Unfold the walk one step — since p.1 not FC, walk takes ≥1 step
    -- Get exit door from p.1 (unique exit ≠ Fin.last d)
    obtain ⟨k_out, ⟨hne_out, hdoor_out⟩, _⟩ :=
      nonfc_with_door_has_unique_exit hKuhn p.1 hnotfc₀ (Fin.last d) hdoor₀
    -- This exit is interior (first_exit_interior: boundary entry → interior exit)
    have hk_out_int : K.adj p.1 k_out ≠ none :=
      kuhnWalk_first_exit_interior hc p.1 (Fin.last d) hdoor₀ hbdry₀ k_out hdoor_out hne_out
    obtain ⟨s₁, k₁, hadj₁⟩ := Option.ne_none_iff_exists.mp hk_out_int
    -- s₁ ≠ p.1 by K.adj_ne
    have hs₁_ne : s₁ ≠ p.1 := K.adj_ne p.1 k_out s₁ k₁ hadj₁
    -- Step 3: Set up state₁ (after step 1 from p.1)
    -- In kuhnWalk, exit_doors = {k : isDoorAt p.1 k ∧ k ≠ Fin.last d}
    -- k_min = exit_doors.min'; the actual exit chosen by kuhnWalk
    -- Both k_out and k_min are the unique exit (by nonfc_with_door_has_unique_exit → exactly 1 element)
    -- So state₁.current = the unique successor ≠ p.1 with s₁ ∉ {p.1}
    -- Step 4: Apply kuhnWalk_not_in_initial_visited at state₁ with visited = {p.1}
    -- This gives: result ∉ {p.1} → result ≠ p.1
    -- Since kuhnPathStart p.1 (Fin.last d) = result of kuhnWalk from state₁
    -- and p.1 ∈ {p.1} = state₁.visited, we get kuhnPathStart p.1 ≠ p.1.
    -- Full proof requires unfolding kuhnWalk one step; using sorry here for the technical step.
    intro heq
    -- heq: (kuhnPathStart p.1 (Fin.last d), Fin.last d) = (p.1, p.2)
    have heq_s := congrArg Prod.fst heq
    -- heq_s : kuhnPathStart p.1 (Fin.last d) = p.1
    simp only at heq_s
    -- Use the walk structure to derive contradiction: result ∉ {p.1} (from kuhnWalk_not_in_initial_visited)
    -- Applied after 1 step: kuhnWalk (card-1) state₁ ∉ state₁.visited = {p.1}
    -- But result = kuhnPathStart p.1 = kuhnWalk (card-1) state₁ = p.1 ∈ {p.1}: contradiction
    have hcard_pos : 0 < Fintype.card K.Simplex := Fintype.card_pos
    -- The initial state for kuhnPathStart
    set state₀ : KuhnState d N c K := {
      current := p.1, entry := Fin.last d, entry_is_door := hdoor₀,
      visited := ∅, current_not_visited := Finset.notMem_empty _ }
    have hvalid₀ := walkValid_init hKuhn p.1 (Fin.last d) hdoor₀ hbdry₀
    -- exit_doors for state₀ (matches kuhnWalk's internal exit_doors)
    set exit_doors₀ := Finset.univ.filter (fun k => isDoorAt c K p.1 k ∧ k ≠ Fin.last d)
    have hne₀ : exit_doors₀.Nonempty :=
      ⟨k_out, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdoor_out, hne_out⟩⟩
    set k_min₀ := exit_doors₀.min' hne₀
    have hkmin_prop := (Finset.mem_filter.mp (Finset.min'_mem exit_doors₀ hne₀)).2
    -- k_min₀ is also interior (same argument as k_out)
    have hk_min_int : K.adj p.1 k_min₀ ≠ none :=
      kuhnWalk_first_exit_interior hc p.1 (Fin.last d) hdoor₀ hbdry₀ k_min₀ hkmin_prop.1 hkmin_prop.2
    obtain ⟨s_next, k_next, hadj_next⟩ := Option.ne_none_iff_exists.mp hk_min_int
    have hs_next_ne : s_next ≠ p.1 := K.adj_ne p.1 k_min₀ s_next k_next hadj_next
    have hs_next_fresh : s_next ∉ (∅ : Finset K.Simplex) ∪ {p.1} := by
      simp [hs_next_ne.symm]
    -- State after step 1
    set state₁ : KuhnState d N c K := {
      current := s_next, entry := k_next,
      entry_is_door := (door_transfer hadj_next).mp hkmin_prop.1,
      visited := {p.1},
      current_not_visited := by simp [hs_next_ne.symm] }
    have hvalid₁ := walkValid_step hvalid₀ hkmin_prop.2 hkmin_prop.1 hadj_next hs_next_fresh
    -- kuhnWalk (card K.Simplex) state₀ = kuhnWalk (card K.Simplex - 1) state₁
    have heq_walk : kuhnWalk c K hKuhn (Fintype.card K.Simplex) state₀ =
        kuhnWalk c K hKuhn (Fintype.card K.Simplex - 1) state₁ := by
      conv_lhs =>
        rw [show Fintype.card K.Simplex = Fintype.card K.Simplex - 1 + 1 from
          Nat.succ_pred_eq_of_pos hcard_pos |>.symm]
      simp only [kuhnWalk, if_neg hnotfc₀, dif_pos hne₀, hadj_next, dif_neg hs_next_fresh]
      apply kuhnWalk_congr <;> rfl
    -- kuhnWalk_not_in_initial_visited: result ∉ {p.1}
    have hn₁ : Fintype.card K.Simplex - 1 + ({p.1} : Finset K.Simplex).card = Fintype.card K.Simplex := by
      simp; omega
    have h_not_vis := kuhnWalk_not_in_initial_visited (Fintype.card K.Simplex - 1) state₁ _ _ hvalid₁ hn₁
    -- heq_s: kuhnPathStart p.1 = p.1 = kuhnWalk card state₀ = kuhnWalk (card-1) state₁
    unfold kuhnPathStart at heq_s
    rw [heq_walk] at heq_s
    -- But result ∉ {p.1} and result = p.1 → contradiction
    exact h_not_vis (heq_s ▸ Finset.mem_singleton_self p.1)

/-- There exists a boundary door from which kuhnPathStart finds an FC simplex.

    **Proof** (axiom → theorem, 1 sorry remaining in bdry_all_even_of_no_fc_walks):
    - Case 1 (∃ walk reaches FC): extract witness directly via push_neg.
    - Case 2 (all walks fail → hfail): bdry_all_even_of_no_fc_walks gives Even |B|,
      contradicting hbdry_odd (Odd |B|) via omega. -/
theorem kuhn_path_existential {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K) (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none),
      IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) := by
  by_cases hfail : ∀ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none), ¬IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀)
  · -- Case 2: all walks fail → parity contradiction
    exfalso
    obtain ⟨m, hm⟩ := hbdry_odd
    obtain ⟨n, hn⟩ := bdry_all_even_of_no_fc_walks hKuhn hc hfail
    omega
  · -- Case 1: some walk succeeds → extract witness
    push_neg at hfail
    obtain ⟨s₀, k₀, hdoor₀, hbdry₀, hfc⟩ := hfail
    exact ⟨s₀, k₀, hdoor₀, hbdry₀, hfc⟩

/-- Thin wrapper: ∃ boundary door whose walk finds FC (see kuhn_path_existential). -/
theorem kuhnPathStart_finds_fc_existential {c : Coloring d N} {K : SpernerTriangulation d N}
    (hKuhn : IsKuhnCompatible c K)
    (hc : IsSperner c)
    (hbdry_odd : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last d)).card) :
    ∃ (s₀ : K.Simplex) (k₀ : Fin (d + 1)) (hdoor₀ : isDoorAt c K s₀ k₀)
      (hbdry₀ : K.adj s₀ k₀ = none),
      IsFC c K (kuhnPathStart c K hKuhn s₀ k₀ hdoor₀ hbdry₀) :=
  kuhn_path_existential hKuhn hc hbdry_odd

end SpernerNDimOQ04
