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

  * `even_card_of_fpf_involution` — a reusable combinatorial lemma: a
    fixed-point-free involution on a `Finset` forces even cardinality.
  * `even_card_irregularOrderedPairs` — **counting consequence of symmetry**: the
    set of ordered irregular pairs `(P, Q)` (distinct parts failing ε-regularity) has
    *even* cardinality, since `Prod.swap` acts on it as a fixed-point-free involution
    (via `isEpsilonRegular_comm`).  Equivalently, the ordered irregular pairs number
    exactly twice the underlying unordered irregular pairs.

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

/-- **Fixed-point-free involution ⟹ even cardinality.**  If `f` maps `s` to itself,
    is an involution on `s` (`f (f a) = a`), and has no fixed point on `s`
    (`f a ≠ a`), then `s` has even cardinality: its elements pair off into
    two-element orbits `{a, f a}`.  Proved by strong induction, removing one such
    orbit `{a, f a}` at a time. -/
theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α] (f : α → α)
    (s : Finset α) : (∀ a ∈ s, f a ∈ s) → (∀ a ∈ s, f (f a) = a) →
      (∀ a ∈ s, f a ≠ a) → Even s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hmem hinv hfree
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, rfl⟩
    · have hfa : f a ∈ s := hmem a ha
      have hne : f a ≠ a := hfree a ha
      have hane : a ≠ f a := fun h => hne h.symm
      have hfa_mem : f a ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hfa⟩
      set t := (s.erase a).erase (f a) with ht
      have hasub : t ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hant : a ∉ t := by
        rw [ht]; exact fun h => Finset.notMem_erase a s (Finset.mem_of_mem_erase h)
      have hssub : t ⊂ s := (Finset.ssubset_iff_of_subset hasub).mpr ⟨a, ha, hant⟩
      -- `t` is again closed under `f`: neither `f b = a` nor `f b = f a` can hold
      -- for `b ∈ t`, since applying the involution would force `b = f a` or `b = a`.
      have hmem' : ∀ b ∈ t, f b ∈ t := by
        intro b hb
        rw [ht, Finset.mem_erase, Finset.mem_erase] at hb
        obtain ⟨hbfa, hba, hbs⟩ := hb
        rw [ht, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hmem b hbs⟩
        · intro h
          have hbe : b = a := by
            have := congrArg f h; rwa [hinv b hbs, hinv a ha] at this
          exact hba hbe
        · intro h
          have hbe : b = f a := by
            have := congrArg f h; rwa [hinv b hbs] at this
          exact hbfa hbe
      have hinv' : ∀ b ∈ t, f (f b) = b := fun b hb => hinv b (hssub.subset hb)
      have hfree' : ∀ b ∈ t, f b ≠ b := fun b hb => hfree b (hssub.subset hb)
      obtain ⟨k, hk⟩ := ih t hssub hmem' hinv' hfree'
      have h2card : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨a, ha, f a, hfa, hane⟩
      have hc1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have hc2 : t.card = (s.erase a).card - 1 := by
        rw [ht]; exact Finset.card_erase_of_mem hfa_mem
      exact ⟨k + 1, by omega⟩

/-- **The ordered irregular-pair count is even.**  Fix a partition `parts` and
    threshold `eps`.  The set of ordered pairs `(P, Q)` of parts that are *distinct*
    and *fail* to be ε-regular is closed under the coordinate swap `Prod.swap`
    (by `isEpsilonRegular_comm`) and has no fixed point (distinctness rules out
    `(P, P)`), so by `even_card_of_fpf_involution` its cardinality is even —
    it is exactly twice the number of *unordered* irregular pairs.

    This realizes the symmetry-to-counting observation: `IsRegularPartition`
    thresholds ordered irregular pairs, but the underlying unordered irregular
    pairs number half as many. -/
theorem even_card_irregularOrderedPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) :
    Even (((parts ×ˢ parts).filter
      (fun p => p.1 ≠ p.2 ∧ ¬IsEpsilonRegular G eps p.1 p.2)).card) := by
  apply even_card_of_fpf_involution Prod.swap
  · -- swap-closed
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Prod.swap_prod_mk] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hne, hreg⟩ := hp
    exact ⟨⟨hy, hx⟩, fun h => hne h.symm, by rw [isEpsilonRegular_comm]; exact hreg⟩
  · -- involution
    intro p _; exact Prod.swap_swap p
  · -- fixed-point-free
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    rw [Prod.swap_prod_mk]
    intro h
    rw [Prod.mk.injEq] at h
    exact hp.2.1 h.2

end Szemeredi.Regularity.OQ01
