/-
  Szemerédi Regularity Lemma — OQ-01: symmetry of edge density and ε-regularity

  The gallery file `SzemerediRegularity.lean` (bridged to Mathlib's
  `szemeredi_regularity`) develops the edge density `edgeDensity G A B` and the
  ε-regularity predicate `IsEpsilonRegular G eps A B`, but never records the basic
  structural fact that both are *symmetric* in their two vertex-set arguments:
  for an undirected graph the pair `(A, B)` and the pair `(B, A)` carry the same
  edge density, and one is ε-regular iff the other is.

  Standard textbook treatments state regularity for unordered pairs precisely
  because of this symmetry; this file supplies it formally.

  * `edgeDensity_comm`        — `d(A, B) = d(B, A)`, via the gallery's
    `edgeDensity_eq_mathlib` bridge and Mathlib's `SimpleGraph.edgeDensity_comm`.
  * `isEpsilonRegular_comm`   — `IsEpsilonRegular G ε A B ↔ IsEpsilonRegular G ε B A`:
    the ε-regularity witnesses `(A', B')` for one orientation are exactly the
    swapped witnesses for the other, and the density difference is unchanged by
    `edgeDensity_comm`.
  * `edgeDensity_empty_left` / `edgeDensity_empty_right` — the degenerate
    boundary values `d(∅, B) = d(A, ∅) = 0`.
  * `irregularPairs_swap_mem` — the set of ordered irregular pairs underlying
    `IsRegularPartition` is closed under swapping coordinates: irregularity is a
    symmetric relation on parts.
  * `edgeDensity_compl` — **complement transfer**: for disjoint nonempty `A, B`,
    `d_{Gᶜ}(A, B) = 1 − d_G(A, B)`, via Mathlib's
    `SimpleGraph.edgeDensity_add_edgeDensity_compl` and the gallery bridge.
  * `edgeDensity_mem_Icc` — the range is packaged as a single membership
    `d(A, B) ∈ Set.Icc 0 1` for downstream positivity/interval reasoning.
  * `isEpsilonRegular_compl` — **complement regularity transfer**: for `0 < eps`
    and disjoint nonempty `A, B`, the pair is ε-regular in `Gᶜ` iff in `G`.  The
    ε-threshold forces every witness nonempty (empty witnesses cannot meet
    `|A'| ≥ eps·|A| > 0`), so `edgeDensity_compl` applies uniformly and the two
    density gaps agree in absolute value.

  * `isEpsilonRegular_mono` — **monotonicity in the parameter**: `eps₁ ≤ eps₂` and
    ε-regularity at `eps₁` imply ε-regularity at `eps₂` (larger `eps` is a weaker
    requirement).  Consequences: `irregularOrderedPairs_antitone` (the irregular-pair
    set shrinks as `eps` grows) and `card_irregularOrderedPairs_antitone` (its count is
    non-increasing in `eps`).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Szemerédi (1975); Komlós–Simonovits (1996).
-/

import Mathlib
import Proofs.SzemerediRegularity

namespace Szemeredi.Regularity.OQ01

open Classical Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Symmetry of edge density.**  For an undirected graph the edge density is
    unchanged by swapping the two vertex sets: `d(A, B) = d(B, A)`.  Proved by
    transporting along the gallery's `edgeDensity_eq_mathlib` bridge to Mathlib's
    `SimpleGraph.edgeDensity`, which is symmetric (`G.symm`). -/
theorem edgeDensity_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeDensity G A B = edgeDensity G B A := by
  rw [edgeDensity_eq_mathlib, edgeDensity_eq_mathlib, G.edgeDensity_comm]

/-- **Symmetry of ε-regularity.**  `IsEpsilonRegular G ε A B` holds iff
    `IsEpsilonRegular G ε B A`.  A witness `(A', B')` for the `(B, A)` orientation
    becomes the witness `(B', A')` for `(A, B)`, and the density difference
    `|d(A', B') − d(B, A)|` equals `|d(B', A') − d(A, B)|` by `edgeDensity_comm`. -/
theorem isEpsilonRegular_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    IsEpsilonRegular G eps A B ↔ IsEpsilonRegular G eps B A := by
  -- One implication suffices by symmetry of the statement.
  have key : ∀ X Y : Finset V, IsEpsilonRegular G eps X Y →
      IsEpsilonRegular G eps Y X := by
    intro X Y h A' B' hA' hB' hcA' hcB'
    have hxy := h B' A' hB' hA' hcB' hcA'
    rwa [edgeDensity_comm G B' A', edgeDensity_comm G X Y] at hxy
  exact ⟨key A B, key B A⟩

/-- The empty left set has zero edge density. -/
theorem edgeDensity_empty_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : edgeDensity G ∅ B = 0 := by
  simp [edgeDensity]

/-- The empty right set has zero edge density. -/
theorem edgeDensity_empty_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : edgeDensity G A ∅ = 0 := by
  simp [edgeDensity]

/-- **Irregularity is a symmetric relation on parts.**  The ordered-pair set that
    `IsRegularPartition` thresholds — distinct parts that fail to be ε-regular —
    is closed under swapping coordinates.  Combined with `isEpsilonRegular_comm`,
    this shows the irregular pairs come in matched `(P, Q)`/`(Q, P)` transpositions. -/
theorem irregularPairs_swap_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) (P Q : Finset V)
    (_hP : P ∈ parts) (_hQ : Q ∈ parts)
    (hpair : P ≠ Q ∧ ¬IsEpsilonRegular G eps P Q) :
    Q ≠ P ∧ ¬IsEpsilonRegular G eps Q P := by
  refine ⟨fun h => hpair.1 h.symm, ?_⟩
  rw [isEpsilonRegular_comm]
  exact hpair.2

/-- **Complement transfer of edge density.**  For *disjoint*, nonempty vertex sets
    `A` and `B`, every cross pair is either a `G`-edge or a `Gᶜ`-edge (disjointness
    rules out the diagonal `a = b`), so the two densities are complementary:

        d_{Gᶜ}(A, B) = 1 − d_G(A, B).

    Proved by transporting both gallery densities to Mathlib via `edgeDensity_eq_mathlib`
    and invoking `SimpleGraph.edgeDensity_add_edgeDensity_compl`.  This is the density
    half of "regularity passes to the complement graph": the density *gap* on any
    disjoint sub-pair is preserved (`|d_{Gᶜ} − d_{Gᶜ}| = |d_G − d_G|`). -/
theorem edgeDensity_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) (h : Disjoint A B) :
    edgeDensity Gᶜ A B = 1 - edgeDensity G A B := by
  have hsum := G.edgeDensity_add_edgeDensity_compl hA hB h
  rw [edgeDensity_eq_mathlib, edgeDensity_eq_mathlib]
  linarith [hsum]

/-- **Edge density lies in `[0, 1]`.**  Packages `edgeDensity_nonneg` and
    `edgeDensity_le_one` into a single interval membership, convenient for
    downstream positivity and `Set.Icc` reasoning. -/
theorem edgeDensity_mem_Icc (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : edgeDensity G A B ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨edgeDensity_nonneg G A B, edgeDensity_le_one G A B⟩

/-- **Complement regularity transfer.**  For a positive parameter `eps` and
    *disjoint*, nonempty vertex sets `A, B`, the pair `(A, B)` is ε-regular in the
    complement graph `Gᶜ` iff it is ε-regular in `G`:

        `IsEpsilonRegular Gᶜ eps A B ↔ IsEpsilonRegular G eps A B`.

    This upgrades the density identity `edgeDensity_compl` (`d_{Gᶜ} = 1 − d_G` on
    disjoint nonempty pairs) to the full ε-regularity predicate.  The subtlety
    flagged as a follow-up — that the ε-regularity witnesses `A' ⊆ A`, `B' ⊆ B`
    could be *empty*, where `edgeDensity_compl` does not apply — dissolves once
    `0 < eps`: a witness must satisfy `|A'| ≥ eps·|A| > 0` (as `A` is nonempty),
    forcing `A'` (and likewise `B'`) nonempty.  Every witness pair is therefore
    disjoint (subsets of the disjoint `A, B`) and nonempty, so `edgeDensity_compl`
    applies uniformly and the two density gaps agree in absolute value:

        `|d_{Gᶜ}(A', B') − d_{Gᶜ}(A, B)| = |d_G(A', B') − d_G(A, B)|`,

    since `(1 − x) − (1 − y) = −(x − y)`.  Both directions of the iff are then a
    single rewrite along this equality. -/
theorem isEpsilonRegular_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B) :
    IsEpsilonRegular Gᶜ eps A B ↔ IsEpsilonRegular G eps A B := by
  -- A witness meeting the ε-threshold against a nonempty set is itself nonempty.
  have hpos : ∀ S T : Finset V, T.Nonempty → (S.card : ℚ) ≥ eps * T.card →
      S.Nonempty := by
    intro S T hT hc
    rw [← Finset.card_pos]
    have h1 : (0 : ℚ) < eps * T.card :=
      mul_pos heps (by exact_mod_cast Finset.card_pos.mpr hT)
    exact_mod_cast lt_of_lt_of_le h1 hc
  -- On every valid witness pair the two density gaps have equal absolute value.
  have main : ∀ A' B' : Finset V, A' ⊆ A → B' ⊆ B →
      (A'.card : ℚ) ≥ eps * A.card → (B'.card : ℚ) ≥ eps * B.card →
      |edgeDensity Gᶜ A' B' - edgeDensity Gᶜ A B|
        = |edgeDensity G A' B' - edgeDensity G A B| := by
    intro A' B' hA' hB' hcA' hcB'
    have hA'ne : A'.Nonempty := hpos A' A hA hcA'
    have hB'ne : B'.Nonempty := hpos B' B hB hcB'
    have hdisj : Disjoint A' B' := hAB.mono hA' hB'
    rw [edgeDensity_compl G hA'ne hB'ne hdisj, edgeDensity_compl G hA hB hAB]
    have hrw : (1 - edgeDensity G A' B') - (1 - edgeDensity G A B)
        = -(edgeDensity G A' B' - edgeDensity G A B) := by ring
    rw [hrw, abs_neg]
  constructor
  · intro h A' B' hA' hB' hcA' hcB'
    rw [← main A' B' hA' hB' hcA' hcB']
    exact h A' B' hA' hB' hcA' hcB'
  · intro h A' B' hA' hB' hcA' hcB'
    rw [main A' B' hA' hB' hcA' hcB']
    exact h A' B' hA' hB' hcA' hcB'

/-- **A fixed-point-free involution forces even cardinality.**  If `σ : α → α`
    maps `S` to itself, is an involution on `S`, and has no fixed point on `S`,
    then `S` splits into two-element orbits `{x, σ x}`, so `S.card` is even.
    Proved by strong induction, removing one orbit at a time.  (General helper,
    kept local so this file stays self-contained.) -/
theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α]
    {S : Finset α} {σ : α → α}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨0, by simp⟩
    · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hS
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      have hpair_sub : {a, σ a} ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; subst hx'; exact hσ_mem a ha
      have hmem : ∀ x, x ∈ S \ {a, σ a} ↔ x ∈ S ∧ x ≠ a ∧ x ≠ σ a := fun x => by
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      have hT_mem : ∀ x ∈ S \ {a, σ a}, σ x ∈ S \ {a, σ a} := by
        intro x hx
        rw [hmem] at hx ⊢
        refine ⟨hσ_mem x hx.1, ?_, ?_⟩
        · intro heq; apply hx.2.2; rw [← hσ_inv x hx.1, heq]
        · intro heq; apply hx.2.1; rw [← hσ_inv x hx.1, heq, hσ_inv a ha]
      have hT_inv : ∀ x ∈ S \ {a, σ a}, σ (σ x) = x :=
        fun x hx => hσ_inv x (Finset.mem_sdiff.mp hx).1
      have hT_ne : ∀ x ∈ S \ {a, σ a}, σ x ≠ x :=
        fun x hx => hσ_ne x (Finset.mem_sdiff.mp hx).1
      have hsub : S \ {a, σ a} ⊆ S := Finset.sdiff_subset
      have hT_lt : S \ {a, σ a} ⊂ S := by
        rw [Finset.ssubset_iff_of_subset hsub]
        exact ⟨a, ha, by simp⟩
      obtain ⟨k, hk⟩ := ih (S \ {a, σ a}) hT_lt hT_mem hT_inv hT_ne
      have hcard_pair : ({a, σ a} : Finset α).card = 2 :=
        Finset.card_pair hσa_ne.symm
      have h2 : 2 ≤ S.card := by
        rw [← hcard_pair]; exact Finset.card_le_card hpair_sub
      have hcard : (S \ {a, σ a}).card = S.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpair_sub, hcard_pair]
      rw [hcard] at hk
      exact ⟨k + 1, by omega⟩

/-- The **ordered irregular pairs** of a partition: cross pairs `(P, Q)` with
    `P ≠ Q` drawn from `parts` that fail ε-regularity. -/
noncomputable def irregularOrderedPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) : Finset (Finset V × Finset V) :=
  (parts ×ˢ parts).filter (fun p => p.1 ≠ p.2 ∧ ¬IsEpsilonRegular G eps p.1 p.2)

/-- **The number of ordered irregular pairs is even.**  By `irregularPairs_swap_mem`
    together with `isEpsilonRegular_comm`, coordinate-swap `Prod.swap` is a
    fixed-point-free involution on `irregularOrderedPairs` (fixed-point-free because
    every member has `P ≠ Q`).  Hence the irregular pairs come in matched
    `(P, Q)`/`(Q, P)` transpositions and their count is even — the quantitative
    refinement of the swap-closure `irregularPairs_swap_mem`. -/
theorem even_card_irregularOrderedPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) :
    Even (irregularOrderedPairs G eps parts).card := by
  apply even_card_of_fpf_involution (σ := Prod.swap)
  · -- swap preserves membership
    intro x hx
    obtain ⟨P, Q⟩ := x
    simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product,
      Prod.swap_prod_mk] at hx ⊢
    obtain ⟨⟨hP, hQ⟩, hne, hreg⟩ := hx
    refine ⟨⟨hQ, hP⟩, ?_, ?_⟩
    · exact fun h => hne h.symm
    · rw [isEpsilonRegular_comm]; exact hreg
  · -- involution
    intro x _; exact Prod.swap_swap x
  · -- fixed-point-free: swap (P, Q) = (P, Q) would force P = Q
    intro x hx
    obtain ⟨P, Q⟩ := x
    simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨_, hne, _⟩ := hx
    intro heq
    rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    exact hne heq.2

/-- **Monotonicity of ε-regularity in the parameter.**  Larger `eps` is a *weaker*
    regularity requirement: if `(A, B)` is `eps₁`-regular and `eps₁ ≤ eps₂`, it is also
    `eps₂`-regular.  Two effects both point the same way — raising the parameter shrinks
    the class of witnesses that must be tested (a witness meeting `|A'| ≥ eps₂·|A|` a
    fortiori meets `|A'| ≥ eps₁·|A|`) and simultaneously relaxes the density-gap bound
    from `≤ eps₁` to `≤ eps₂`.  No sign hypothesis on the parameters is needed: the
    threshold comparison only uses `Nat.cast_nonneg` of the cardinalities. -/
theorem isEpsilonRegular_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps₁ eps₂ : ℚ} (h : eps₁ ≤ eps₂) {A B : Finset V}
    (hreg : IsEpsilonRegular G eps₁ A B) : IsEpsilonRegular G eps₂ A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- Meeting the `eps₂` threshold implies meeting the smaller `eps₁` threshold.
  have hA2 : (A'.card : ℚ) ≥ eps₁ * A.card :=
    le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) hcA'
  have hB2 : (B'.card : ℚ) ≥ eps₁ * B.card :=
    le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)) hcB'
  exact le_trans (hreg A' B' hA' hB' hA2 hB2) h

/-- **The irregular-pair set is antitone in `eps`.**  Since ε-regularity only weakens as
    `eps` grows (`isEpsilonRegular_mono`), a pair that is irregular at the larger `eps₂`
    was already irregular at the smaller `eps₁`; hence the ordered irregular pairs at
    `eps₂` are a subset of those at `eps₁`. -/
theorem irregularOrderedPairs_antitone (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps₁ eps₂ : ℚ} (h : eps₁ ≤ eps₂) (parts : Finset (Finset V)) :
    irregularOrderedPairs G eps₂ parts ⊆ irregularOrderedPairs G eps₁ parts := by
  intro x hx
  simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product] at hx ⊢
  obtain ⟨hmem, hne, hreg⟩ := hx
  exact ⟨hmem, hne, fun hcon => hreg (isEpsilonRegular_mono G h hcon)⟩

/-- **The irregular-pair count is monotone (non-increasing) in `eps`.**  Cardinality form
    of `irregularOrderedPairs_antitone`: raising the regularity parameter can only reduce
    the number of ordered irregular pairs — the quantitative statement behind "coarser
    regularity is easier to satisfy". -/
theorem card_irregularOrderedPairs_antitone (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps₁ eps₂ : ℚ} (h : eps₁ ≤ eps₂) (parts : Finset (Finset V)) :
    (irregularOrderedPairs G eps₂ parts).card ≤ (irregularOrderedPairs G eps₁ parts).card :=
  Finset.card_le_card (irregularOrderedPairs_antitone G h parts)

/-- **A partition is exactly as irregular for `Gᶜ` as for `G`.**  Lifting the per-pair
    `isEpsilonRegular_compl` to the whole partition: for a positive parameter `eps` and a
    family of *pairwise-disjoint, nonempty* parts (the standing hypotheses of a genuine
    vertex partition), the ordered irregular pairs of the complement graph coincide with
    those of `G`:

        `irregularOrderedPairs Gᶜ eps parts = irregularOrderedPairs G eps parts`.

    Every irregular pair `(P, Q)` has `P ≠ Q` with `P, Q ∈ parts`, so `P` and `Q` are
    nonempty and disjoint — exactly the hypotheses under which `isEpsilonRegular_compl`
    equates ε-regularity in `Gᶜ` and `G`.  The filter conditions defining the two sets are
    therefore pointwise equivalent.  Consequence: ε-regularity of a partition is a
    *self-complementary* property — a partition witnesses (ir)regularity for a graph iff it
    does for the complement graph. -/
theorem irregularOrderedPairs_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (parts : Finset (Finset V))
    (hne : ∀ P ∈ parts, P.Nonempty)
    (hdisj : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) :
    irregularOrderedPairs Gᶜ eps parts = irregularOrderedPairs G eps parts := by
  ext x
  obtain ⟨P, Q⟩ := x
  simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hP, hQ⟩, hne', hreg⟩
    refine ⟨⟨hP, hQ⟩, hne', ?_⟩
    rwa [isEpsilonRegular_compl G eps heps (hne P hP) (hne Q hQ) (hdisj P hP Q hQ hne')] at hreg
  · rintro ⟨⟨hP, hQ⟩, hne', hreg⟩
    refine ⟨⟨hP, hQ⟩, hne', ?_⟩
    rwa [← isEpsilonRegular_compl G eps heps (hne P hP) (hne Q hQ) (hdisj P hP Q hQ hne')] at hreg

/-- **The irregular-pair count is complement-invariant.**  Cardinality form of
    `irregularOrderedPairs_compl`: a graph and its complement have the *same* number of
    ordered irregular pairs on any pairwise-disjoint, nonempty partition.  In particular the
    `IsRegularPartition` threshold `card irregular ≤ eps·(#parts)²` holds for `G` iff it holds
    for `Gᶜ`. -/
theorem card_irregularOrderedPairs_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (parts : Finset (Finset V))
    (hne : ∀ P ∈ parts, P.Nonempty)
    (hdisj : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) :
    (irregularOrderedPairs Gᶜ eps parts).card = (irregularOrderedPairs G eps parts).card := by
  rw [irregularOrderedPairs_compl G eps heps parts hne hdisj]

/-- **Irregular pairs are off-diagonal.**  Every ordered irregular pair `(P, Q)`
    is drawn from `parts` with `P ≠ Q`, i.e. lies in `parts.offDiag`.  The extra
    `¬IsEpsilonRegular` filter condition only removes more pairs, so the irregular
    set is contained in the off-diagonal. -/
theorem irregularOrderedPairs_subset_offDiag (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) :
    irregularOrderedPairs G eps parts ⊆ parts.offDiag := by
  intro x hx
  simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product] at hx
  rw [Finset.mem_offDiag]
  exact ⟨hx.1.1, hx.1.2, hx.2.1⟩

/-- **Trivial upper bound on the irregular-pair count.**  There are at most
    `n·n − n = n(n−1)` ordered irregular pairs, where `n = #parts`: the irregular
    set embeds in `parts.offDiag`, whose cardinality is `Finset.offDiag_card`.
    This is the ceiling against which the `IsRegularPartition` threshold
    `card irregular ≤ eps·n²` is compared, and the complement of the antitone
    lower-side bookkeeping (`card_irregularOrderedPairs_antitone`). -/
theorem card_irregularOrderedPairs_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) :
    (irregularOrderedPairs G eps parts).card ≤ parts.card * parts.card - parts.card := by
  calc (irregularOrderedPairs G eps parts).card
      ≤ parts.offDiag.card :=
        Finset.card_le_card (irregularOrderedPairs_subset_offDiag G eps parts)
    _ = parts.card * parts.card - parts.card := Finset.offDiag_card parts

/-- **A partition with at most one part has no irregular pairs.**  The base case
    of any regularity-partition induction: with `#parts ≤ 1` there are no two
    *distinct* parts to be irregular, so the ordered irregular set is empty.
    Reads off the trivial upper bound `card_irregularOrderedPairs_le` at
    `parts.card ≤ 1`, where the off-diagonal ceiling `n·n − n` collapses to `0`.
    Pairs with `card_irregularOrderedPairs_le` (the general ceiling) to pin the
    count exactly at the degenerate end of the range. -/
theorem card_irregularOrderedPairs_eq_zero_of_card_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) (h : parts.card ≤ 1) :
    (irregularOrderedPairs G eps parts).card = 0 := by
  have hle := card_irregularOrderedPairs_le G eps parts
  have hz : parts.card * parts.card - parts.card = 0 := by
    interval_cases parts.card <;> decide
  rw [hz] at hle
  exact Nat.le_zero.mp hle

/-- **Every pair is ε-regular once `eps ≥ 1`.**  The density gap between any two
    sub-densities is at most `1` (both edge densities lie in `[0, 1]`, so their
    difference is in `[-1, 1]`), which is `≤ eps` as soon as `1 ≤ eps`.  Thus `eps = 1`
    is the trivial-regularity threshold: at or above it the ε-regularity condition
    imposes no constraint at all.  This is the large-parameter extreme complementing
    `isEpsilonRegular_mono` (regularity only weakens as `eps` grows). -/
theorem isEpsilonRegular_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    IsEpsilonRegular G eps A B := by
  intro A' B' _ _ _ _
  have h1 := edgeDensity_mem_Icc G A' B'
  have h2 := edgeDensity_mem_Icc G A B
  rw [Set.mem_Icc] at h1 h2
  rw [abs_le]
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- **No irregular pairs once `eps ≥ 1`.**  Since every pair is ε-regular at `eps ≥ 1`
    (`isEpsilonRegular_of_one_le`), the ordered irregular set is empty for any partition.
    The high-`eps` counterpart of `card_irregularOrderedPairs_eq_zero_of_card_le_one`
    (which is the few-parts extreme): the irregular count vanishes at *both* ends of the
    regularity regime. -/
theorem irregularOrderedPairs_eq_empty_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (parts : Finset (Finset V)) :
    irregularOrderedPairs G eps parts = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  rintro x hx
  simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product] at hx
  exact hx.2.2 (isEpsilonRegular_of_one_le G heps x.1 x.2)

/-- **The irregular-pair count vanishes for `eps ≥ 1`.**  Cardinality form of
    `irregularOrderedPairs_eq_empty_of_one_le`: at or above the trivial threshold the
    `IsRegularPartition` irregular-count bound is satisfied vacuously by every partition. -/
theorem card_irregularOrderedPairs_eq_zero_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (parts : Finset (Finset V)) :
    (irregularOrderedPairs G eps parts).card = 0 := by
  rw [irregularOrderedPairs_eq_empty_of_one_le G heps parts, Finset.card_empty]

end Szemeredi.Regularity.OQ01
