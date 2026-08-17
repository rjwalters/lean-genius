import Proofs.Erdos85BinarySquareCrossRootTransitionReversal

/-! # Composition of cross-root transition factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Relational composition of two finite relations on the same ambient type. -/
def composePairFinset
    {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset (A × A)) : Finset (A × A) :=
  ((Finset.univ : Finset A) ×ˢ (Finset.univ : Finset A)).filter fun p =>
    ∃ b, (p.1, b) ∈ S ∧ (b, p.2) ∈ T

theorem mem_composePairFinset_iff
    {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset (A × A)) (a c : A) :
    (a, c) ∈ composePairFinset S T ↔
      ∃ b, (a, b) ∈ S ∧ (b, c) ∈ T := by
  simp [composePairFinset]

theorem mem_transposePairFinset_iff
    {A : Type*} [DecidableEq A]
    (S : Finset (A × A)) (a b : A) :
    (a, b) ∈ transposePairFinset S ↔ (b, a) ∈ S := by
  classical
  constructor
  · intro h
    rw [transposePairFinset] at h
    obtain ⟨p, hp, hswap⟩ := Finset.mem_image.mp h
    have : p = (b, a) := by
      apply Prod.ext
      · simpa using congrArg Prod.snd hswap
      · simpa using congrArg Prod.fst hswap
    simpa [this] using hp
  · intro h
    rw [transposePairFinset]
    exact Finset.mem_image.mpr ⟨(b, a), h, rfl⟩

/-- Finite relational composition is associative. -/
theorem composePairFinset_assoc
    {A : Type*} [Fintype A] [DecidableEq A]
    (R S T : Finset (A × A)) :
    composePairFinset (composePairFinset R S) T =
      composePairFinset R (composePairFinset S T) := by
  classical
  ext ⟨a, d⟩
  simp only [mem_composePairFinset_iff]
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, c, hbc, hcd⟩
  · rintro ⟨b, hab, c, hbc, hcd⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

/-- Transposing a composite reverses the order of its factors. -/
theorem transposePairFinset_composePairFinset
    {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset (A × A)) :
    transposePairFinset (composePairFinset S T) =
      composePairFinset (transposePairFinset T) (transposePairFinset S) := by
  classical
  ext ⟨c, a⟩
  simp only [mem_transposePairFinset_iff, mem_composePairFinset_iff]
  constructor <;> rintro ⟨b, h₁, h₂⟩ <;> exact ⟨b, h₂, h₁⟩

/-- Identity relation for finite transition composition. -/
def identityPairFinset
    {A : Type*} [Fintype A] [DecidableEq A] : Finset (A × A) :=
  (Finset.univ : Finset A).image fun a => (a, a)

theorem mem_identityPairFinset_iff
    {A : Type*} [Fintype A] [DecidableEq A] (a b : A) :
    (a, b) ∈ (identityPairFinset : Finset (A × A)) ↔ a = b := by
  classical
  simp [identityPairFinset, Prod.ext_iff]

theorem composePairFinset_identity
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) :
    composePairFinset S identityPairFinset = S := by
  classical
  ext ⟨a, b⟩
  simp [mem_composePairFinset_iff, mem_identityPairFinset_iff]

theorem identity_composePairFinset
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) :
    composePairFinset identityPairFinset S = S := by
  classical
  ext ⟨a, b⟩
  simp [mem_composePairFinset_iff, mem_identityPairFinset_iff]

/-- Ordered relational composite of a finite list of transition factors. -/
def composePairFinsetList
    {A : Type*} [Fintype A] [DecidableEq A] :
    List (Finset (A × A)) → Finset (A × A)
  | [] => identityPairFinset
  | S :: factors => composePairFinset S (composePairFinsetList factors)

theorem composePairFinsetList_append
    {A : Type*} [Fintype A] [DecidableEq A]
    (xs ys : List (Finset (A × A))) :
    composePairFinsetList (xs ++ ys) =
      composePairFinset (composePairFinsetList xs)
        (composePairFinsetList ys) := by
  induction xs with
  | nil =>
      simp [composePairFinsetList, identity_composePairFinset]
  | cons S xs ih =>
      simp only [List.cons_append, composePairFinsetList]
      rw [ih, composePairFinset_assoc]

theorem composePairFinsetList_singleton
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) :
    composePairFinsetList [S] = S := by
  simp [composePairFinsetList, composePairFinset_identity]

/-- Reversing a finite transition path and transposing every edge factor
transposes the composite path relation. -/
theorem transposePairFinset_composePairFinsetList
    {A : Type*} [Fintype A] [DecidableEq A]
    (factors : List (Finset (A × A))) :
    transposePairFinset (composePairFinsetList factors) =
      composePairFinsetList
        (factors.reverse.map transposePairFinset) := by
  induction factors with
  | nil =>
      ext ⟨a, b⟩
      simp [composePairFinsetList, transposePairFinset,
        identityPairFinset, Prod.ext_iff]
  | cons S factors ih =>
      rw [composePairFinsetList,
        transposePairFinset_composePairFinset, ih]
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      rw [composePairFinsetList_append, composePairFinsetList_singleton]

/-- For two consecutive ordered root pairs, reversing the root path
transposes its composed remote-target transition relation. -/
theorem crossRoot_twoStepTransition_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y z : d.supp) :
    transposePairFinset
      (composePairFinset
        (crossRootCenterPairFinset G hfree hde x y)
        (crossRootCenterPairFinset G hfree hde y z)) =
      composePairFinset
        (crossRootCenterPairFinset G hfree hde z y)
        (crossRootCenterPairFinset G hfree hde y x) := by
  rw [transposePairFinset_composePairFinset,
    ← crossRootCenterPairFinset_swap_roots G hfree hde y z,
    ← crossRootCenterPairFinset_swap_roots G hfree hde x y]

end

end Erdos85
