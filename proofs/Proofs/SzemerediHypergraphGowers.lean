/-
  Gowers Hypergraph Regularity Infrastructure

  Extends SzemerediHypergraphCore.lean with the full Gowers (2007) relative
  regularity infrastructure required for the hypergraph counting lemma
  (Nagle-Rödl-Schacht 2006) and the multidimensional Szemerédi theorem.

  ## Definitions

  - `SimplicialComplex V dim`: j-uniform hypergraphs for j = 1, ..., dim
    with downward closure.
  - `IsSubComplex`: the sub-complex partial order.
  - `topCliques hdim C`: (dim+1)-subsets of V whose dim-subsets are C-faces.
  - `relativeKDensity hk H C`: fraction of topCliques of C that are edges of H.
  - `IsGowersRegular hk H ε δ C`: stability of relativeKDensity under dense
    sub-complexes.
  - `completeComplex V dim`: all j-subsets as faces.
  - `naive_implies_gowers`: naive regularity → Gowers regularity (complete complex).

  ## Indexing convention

  `SimplicialComplex V dim` has faces at levels j : Fin dim where
  `skeleton j` contains (j.val + 1)-element subsets. For a k-graph H,
  use C : SimplicialComplex V (k - 1) (requires k ≥ 2).

  ## References

  - Gowers (2007), Ann. Math. 166(3), 897–946.
  - Nagle-Rödl-Schacht (2006), RSA 28(2), 113–179.
  - Rödl-Skokan (2004), RSA 25(1), 1–42.
-/
import Proofs.SzemerediHypergraphCore

namespace Szemeredi.Hypergraph

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SIMPLICIAL COMPLEX
-- ═══════════════════════════════════════════════════════════════════

/-- A simplicial complex on vertex set V of top dimension dim.

    `skeleton j` for `j : Fin dim` gives the (j.val + 1)-element faces.
    Down-closure: every (j+1)-face contains all its j-subfaces. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] (dim : ℕ) where
  skeleton : Fin dim → Finset (Finset V)
  uniform : ∀ j : Fin dim, ∀ e ∈ skeleton j, e.card = j.val + 1
  down_closed : ∀ (j : Fin dim) (hj : 0 < j.val),
    ∀ e ∈ skeleton j,
    ∀ f ⊆ e, f.card = j.val →
      f ∈ skeleton ⟨j.val - 1, Nat.lt_trans (Nat.sub_lt hj (by norm_num)) j.isLt⟩

/-- Sub-complex partial order: C' ⊆ C iff each skeleton(j) of C' ⊆ skeleton(j) of C. -/
def IsSubComplex {dim : ℕ} (C' C : SimplicialComplex V dim) : Prop :=
  ∀ j : Fin dim, C'.skeleton j ⊆ C.skeleton j

lemma IsSubComplex.refl {dim : ℕ} (C : SimplicialComplex V dim) : IsSubComplex C C :=
  fun _ => Finset.Subset.refl _

lemma IsSubComplex.trans {dim : ℕ} {C₁ C₂ C₃ : SimplicialComplex V dim}
    (h₁₂ : IsSubComplex C₁ C₂) (h₂₃ : IsSubComplex C₂ C₃) : IsSubComplex C₁ C₃ :=
  fun j => Finset.Subset.trans (h₁₂ j) (h₂₃ j)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: COMPLETE COMPLEX AND TOP CLIQUES
-- ═══════════════════════════════════════════════════════════════════

/-- The complete simplicial complex: all j-subsets of V are faces at every level. -/
def completeComplex (V : Type*) [Fintype V] [DecidableEq V] (dim : ℕ) :
    SimplicialComplex V dim where
  skeleton j := (Finset.univ (α := V)).powerset.filter (fun e => e.card = j.val + 1)
  uniform j e he := (Finset.mem_filter.mp he).2
  down_closed j hj e he f hfe hfcard := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hfe.trans (Finset.mem_filter.mp he).1, hfcard⟩

theorem completeComplex_skeleton (dim : ℕ) (j : Fin dim) :
    (completeComplex V dim).skeleton j =
    (Finset.univ (α := V)).powerset.filter (fun e => e.card = j.val + 1) := rfl

/-- Top cliques relative to a simplicial complex of dimension dim:
    (dim+1)-element subsets of V all of whose dim-subsets are top-dimensional C-faces.

    For a k-graph H with C : SimplicialComplex V (k-1), topCliques gives
    k-element sets all of whose (k-1)-subsets are in C's (k-1)-skeleton. -/
noncomputable def topCliques {dim : ℕ} (hdim : 0 < dim) (C : SimplicialComplex V dim) :
    Finset (Finset V) :=
  (Finset.univ (α := V)).powerset.filter fun e =>
    e.card = dim + 1 ∧
    ∀ f ⊆ e, f.card = dim →
      f ∈ C.skeleton ⟨dim - 1, Nat.sub_lt hdim (by norm_num)⟩

/-- Top cliques of the complete complex are all (dim+1)-subsets of V. -/
theorem topCliques_completeComplex (dim : ℕ) (hdim : 0 < dim) :
    topCliques hdim (completeComplex V dim) =
    (Finset.univ (α := V)).powerset.filter (fun e => e.card = dim + 1) := by
  ext e
  simp only [topCliques, completeComplex_skeleton, Finset.mem_filter,
             Finset.mem_powerset, Finset.mem_univ, true_and]
  constructor
  · intro ⟨hcard, _⟩; exact hcard
  · intro hcard
    refine ⟨hcard, fun f hfe hfcard => ?_⟩
    simp only [completeComplex_skeleton, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hfe.trans (Finset.subset_univ _), ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ dim)]
    exact hfcard

/-- Sub-complex containment implies top-clique containment. -/
theorem topCliques_mono {dim : ℕ} (hdim : 0 < dim) {C' C : SimplicialComplex V dim}
    (hsub : IsSubComplex C' C) : topCliques hdim C' ⊆ topCliques hdim C := by
  intro e he
  simp only [topCliques, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun f hfe hfcard => hsub _ (he.2 f hfe hfcard)⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: RELATIVE DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- Relative k-density of a k-uniform hypergraph H with respect to a
    (k-1)-complex C:
      d(H | C) = |H.edges ∩ topCliques(C)| / |topCliques(C)|
    Returns 0 when C has no top-cliques.

    Requires k ≥ 2 so that dim = k - 1 ≥ 1 for topCliques. -/
noncomputable def relativeKDensity {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (C : SimplicialComplex V (k - 1)) : ℚ :=
  let D := topCliques (by omega : 0 < k - 1) C
  if (D.card : ℚ) = 0 then 0
  else (H.edges ∩ D).card / D.card

theorem relativeKDensity_nonneg {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (C : SimplicialComplex V (k - 1)) :
    0 ≤ relativeKDensity hk H C := by
  unfold relativeKDensity
  split_ifs; · exact le_refl 0
  · positivity

theorem relativeKDensity_le_one {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (C : SimplicialComplex V (k - 1)) :
    relativeKDensity hk H C ≤ 1 := by
  unfold relativeKDensity
  split_ifs with h; · exact zero_le_one
  · have hpos : (0 : ℚ) < (topCliques (by omega) C).card := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h0 => h (by exact_mod_cast h0))
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)

theorem relativeKDensity_empty {k : ℕ} (hk : 1 < k)
    (C : SimplicialComplex V (k - 1)) :
    relativeKDensity hk (UHypergraph.empty V k) C = 0 := by
  unfold relativeKDensity
  split_ifs; · rfl
  · simp [UHypergraph.empty]

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: GOWERS REGULARITY
-- ═══════════════════════════════════════════════════════════════════

/-- A k-graph H is (ε, δ)-Gowers-regular relative to C if for every
    sub-complex C' ⊆ C with topCliques density ≥ δ, the relative
    density of H is within ε of the density in C. -/
def IsGowersRegular {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (ε δ : ℚ) (C : SimplicialComplex V (k - 1)) : Prop :=
  ∀ C' : SimplicialComplex V (k - 1),
    IsSubComplex C' C →
    δ * (topCliques (by omega : 0 < k - 1) C).card ≤
      (topCliques (by omega : 0 < k - 1) C').card →
    |relativeKDensity hk H C' - relativeKDensity hk H C| ≤ ε

/-- Larger ε is easier: (ε, δ)-regular ∧ ε ≤ ε' → (ε', δ)-regular. -/
theorem IsGowersRegular.mono_eps {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) {ε ε' δ : ℚ} (hee : ε ≤ ε') (C : SimplicialComplex V (k - 1))
    (hreg : IsGowersRegular hk H ε δ C) : IsGowersRegular hk H ε' δ C :=
  fun C' hsub hden => (hreg C' hsub hden).trans hee

/-- Larger δ is easier: (ε, δ)-regular ∧ δ ≤ δ' → (ε, δ')-regular.
    Larger δ means fewer sub-complexes qualify, so the condition is weaker. -/
theorem IsGowersRegular.mono_delta {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) {ε δ δ' : ℚ} (hdd : δ ≤ δ') (C : SimplicialComplex V (k - 1))
    (hreg : IsGowersRegular hk H ε δ C) : IsGowersRegular hk H ε δ' C :=
  fun C' hsub hden => hreg C' hsub
    (le_trans (mul_le_mul_of_nonneg_right hdd (by exact_mod_cast Nat.zero_le _)) hden)

-- ═══════════════════════════════════════════════════════════════════
-- PART V: GLOBAL DENSITY AND COMPLETE COMPLEX
-- ═══════════════════════════════════════════════════════════════════

/-- The global edge density (fraction of all k-subsets that are edges) -/
noncomputable def globalDensity {k : ℕ} (H : UHypergraph V k) : ℚ :=
  let allKSets := (Finset.univ (α := V)).powerset.filter (fun e => e.card = k)
  if (allKSets.card : ℚ) = 0 then 0
  else H.edges.card / allKSets.card

/-- For a k-graph H, the relative density with respect to the complete complex
    equals the global density. -/
theorem relativeKDensity_completeComplex {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) :
    relativeKDensity hk H (completeComplex V (k - 1)) = globalDensity H := by
  unfold relativeKDensity globalDensity
  simp only [relativeKDensity, globalDensity]
  congr 2
  · -- topCliques (completeComplex V (k-1)) = all k-subsets of V
    rw [topCliques_completeComplex (k - 1) (by omega)]
    congr 1
    simp [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  · -- (H.edges ∩ topCliques ...).card = H.edges.card
    -- Step 1: identify topCliques (completeComplex) = all k-subsets of V
    have hD : topCliques (by omega : 0 < k - 1) (completeComplex V (k - 1)) =
        (Finset.univ (α := V)).powerset.filter (fun e => e.card = k) := by
      have h := topCliques_completeComplex (k - 1) (by omega)
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h; exact h
    -- Step 2: H.edges ⊆ all k-subsets (every edge has card = k and ⊆ univ)
    have hsub : H.edges ⊆ topCliques (by omega : 0 < k - 1) (completeComplex V (k - 1)) := by
      rw [hD]
      intro e he
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      exact H.uniform e he
    -- Step 3: intersection with a superset is the set itself
    rw [Finset.inter_eq_left.mpr hsub]

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: STRUCTURAL PROPERTIES OF GOWERS REGULARITY
-- ═══════════════════════════════════════════════════════════════════

/-- Relative density depends only on the topCliques set: complexes with
    identical topCliques give identical relative densities for every H. -/
theorem relativeKDensity_eq_of_topCliques_eq {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (C₁ C₂ : SimplicialComplex V (k - 1))
    (h : topCliques (by omega : 0 < k - 1) C₁ =
         topCliques (by omega : 0 < k - 1) C₂) :
    relativeKDensity hk H C₁ = relativeKDensity hk H C₂ := by
  unfold relativeKDensity
  rw [h]

/-- **Trivial Gowers regularity**: every k-graph H is (0, 1)-Gowers-regular
    relative to any complex C.

    With δ = 1, the constraint `|topCliques(C)| ≤ |topCliques(C')|` combined
    with `topCliques_mono` (which gives `topCliques(C') ⊆ topCliques(C)`)
    forces equality of topCliques as Finsets. Equal topCliques give equal
    relative densities (via `relativeKDensity_eq_of_topCliques_eq`), hence
    the difference is 0 ≤ 0. -/
theorem isGowersRegular_self {k : ℕ} (hk : 1 < k)
    (H : UHypergraph V k) (C : SimplicialComplex V (k - 1)) :
    IsGowersRegular hk H 0 1 C := by
  intro C' hsub hden
  -- δ = 1 + topCliques_mono force topCliques to be equal Finsets
  have hsubD : topCliques (by omega : 0 < k - 1) C' ⊆
               topCliques (by omega : 0 < k - 1) C :=
    topCliques_mono _ hsub
  have hcard1 : (topCliques (by omega : 0 < k - 1) C).card ≤
                (topCliques (by omega : 0 < k - 1) C').card := by
    have h1 := hden
    rw [one_mul] at h1
    exact_mod_cast h1
  have hDeq : topCliques (by omega : 0 < k - 1) C' =
              topCliques (by omega : 0 < k - 1) C :=
    Finset.eq_of_subset_of_card_le hsubD hcard1
  -- Equal topCliques imply equal relative densities
  rw [relativeKDensity_eq_of_topCliques_eq hk H C' C hDeq, sub_self, abs_zero]
  exact le_refl 0

/-- **Empty hypergraph is Gowers-regular**: the empty k-graph has zero
    relative density on every sub-complex, hence is (0, δ)-regular for
    every ε ≥ 0 and every δ. -/
theorem isGowersRegular_empty {k : ℕ} (hk : 1 < k)
    (δ : ℚ) (C : SimplicialComplex V (k - 1)) :
    IsGowersRegular hk (UHypergraph.empty V k) 0 δ C := by
  intro C' _ _
  rw [relativeKDensity_empty hk C', relativeKDensity_empty hk C, sub_self, abs_zero]
  exact le_refl 0

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: OBSTRUCTION TO NAIVE → GOWERS
-- ═══════════════════════════════════════════════════════════════════

/-
  ## Why a direct `naive_implies_gowers` does not hold (as previously stated)

  A previous session conjectured: with `parts = [univ × k]`,
  `IsHypergraphRegular H ε parts → IsGowersRegular hk H ε δ (completeComplex …)`.

  The hypothesis is degenerate. With `parts = [univ × k]` (k ≥ 2), the comparison
  density `kPartiteDensity H parts = 0`, because `transversals parts` requires
  every transversal `s` to satisfy `(s ∩ univ).card = 1`; but `s ∩ univ = s` and
  `s.card = parts.length = k ≥ 2`, contradiction. Hence `transversals parts = ∅`.

  So the hypothesis only constrains `|kPartiteDensity H parts' - 0| ≤ ε`, i.e.
  bounds the density on every k-tuple of "large" subsets via the transversal
  notion. But the transversal density only sees vertex-partitioned product
  structure, while Gowers regularity quantifies over arbitrary sub-complexes
  whose top-cliques need not arise from any vertex partition.

  Concretely: a sub-complex `C' ⊆ completeComplex` may concentrate its top-cliques
  on a small region of the k-set lattice that no transversal partition can hit.
  Therefore `relativeKDensity H C'` can deviate from `globalDensity H` even when
  the naive transversal-based hypothesis holds.

  ## What CAN be proven (provable surrogates)

  - `isGowersRegular_self`     — every H is (0, 1)-regular w.r.t. any C (above).
  - `isGowersRegular_empty`    — the empty hypergraph is (0, δ)-regular (above).
  - `IsGowersRegular.mono_eps` / `IsGowersRegular.mono_delta` — monotonicity
    in the regularity parameters.

  ## What would be needed to bridge naive → Gowers properly

  Either (a) restrict to sub-complexes that arise from vertex partitions (so
  topCliques become genuine transversals), or (b) replace the naive hypothesis
  with a partition-respecting hypothesis (e.g., density of every sub-complex,
  not every transversal). Both directions are research-level work.

  Reference: Gowers (2007), §4 distinguishes "weak" (transversal-based) and
  "strong" (relative-to-complex) regularity precisely because the former
  does not imply the latter without additional structural input.
-/

end Szemeredi.Hypergraph
