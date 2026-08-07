import Proofs.Erdos85SquareMinimumDoubleCoverEscape
import Proofs.Erdos85CoverAdmissibleFiberParity

/-!
# Deck-odd cancellation for the mass-two double cover

The unique mass-two escape is a cyclic double cover.  Its incidence map is
constant on the two points in every deck fiber, so it annihilates functions
which are odd under the deck involution.  This is the valid local operator
consequence of the double-cover structure; the full adjacency operator need
not preserve functions supported on the doubled component.
-/

namespace Erdos85

noncomputable section

/-- A function on a cyclic double cover which changes sign under the deck
half-turn has total sum zero. -/
theorem sum_eq_zero_of_halfTurn_antiInvariant
    {K : Type*} [AddCommGroup K] {r : ℕ} [NeZero r]
    (F : ZMod (2 * r) → K)
    (hanti : ∀ y, F (y + (r : ZMod (2 * r))) = -F y) :
    ∑ y, F y = 0 := by
  classical
  apply Finset.sum_involution
      (s := Finset.univ) (f := F)
      (fun y _ ↦ y + (r : ZMod (2 * r)))
  · intro y _
    rw [hanti]
    exact add_neg_cancel (F y)
  · intro y _ _
    have hrPos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hrCast : (r : ZMod (2 * r)) ≠ 0 := by
      intro hz
      have hdvd : 2 * r ∣ r :=
        (ZMod.natCast_eq_zero_iff r (2 * r)).mp hz
      have hle : 2 * r ≤ r := Nat.le_of_dvd hrPos hdvd
      omega
    intro heq
    apply hrCast
    have h := congrArg (fun z : ZMod (2 * r) ↦ z - y) heq
    simpa using h
  · intro y _
    simp
  · intro y _
    calc
      y + (r : ZMod (2 * r)) + (r : ZMod (2 * r)) =
          y + ((r : ZMod (2 * r)) + (r : ZMod (2 * r))) := add_assoc _ _ _
      _ = y + ((2 * r : ℕ) : ZMod (2 * r)) := by
        rw [← Nat.cast_add, show r + r = 2 * r by omega]
      _ = y := by rw [ZMod.natCast_self, add_zero]

/-- A deck-invariant selector has zero pairing with every deck-odd
function.  In the graph application the selector is a row of the incidence
block from the minimum cycle to its doubled target. -/
theorem sum_indicator_eq_zero_of_halfTurn
    {K : Type*} [AddCommGroup K] {r : ℕ} [NeZero r]
    (f : ZMod (2 * r) → ZMod r)
    (hf : ∀ y, f (y + (r : ZMod (2 * r))) = f y)
    (w : ZMod (2 * r) → K)
    (hw : ∀ y, w (y + (r : ZMod (2 * r))) = -w y)
    (x : ZMod r) :
    ∑ y, (if x = f y then w y else 0) = 0 := by
  apply sum_eq_zero_of_halfTurn_antiInvariant
  intro y
  rw [hf, hw]
  split_ifs <;> simp_all

/-- Oriented cyclic double-cover incidence annihilates deck-odd functions.
This packages the preceding cancellation using the orientation hypothesis
already produced by cycle-cover rigidity. -/
theorem cycleCover_indicator_mulVec_deckOdd_eq_zero
    {K : Type*} [AddCommGroup K] {r : ℕ} [NeZero r]
    (f : ZMod (2 * r) → ZMod r)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (w : ZMod (2 * r) → K)
    (hw : ∀ y, w (y + (r : ZMod (2 * r))) = -w y)
    (x : ZMod r) :
    ∑ y, (if x = f y then w y else 0) = 0 := by
  exact sum_indicator_eq_zero_of_halfTurn f
    (cycleCoverMap_halfTurn_invariant f horient) w hw x

/-- The parity defect of a cyclic double cover is completely explicit: the
only admissible displacement divisible by the source length is the deck
half-turn.  Thus the exceptional zero fiber is a singleton, rather than an
unspecified odd set. -/
theorem doubleCover_admissible_sourceLength_dvd_eq_singleton
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) :
    (admissibleDifferences (2 * r)).filter
        (fun δ : ZMod (2 * r) ↦ r ∣ δ.val) =
      {(r : ZMod (2 * r))} := by
  classical
  ext δ
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hadm, hdvd⟩
    have hδ0 : δ ≠ 0 := (mem_admissibleDifferences_iff δ).mp hadm |>.1
    obtain ⟨k, hk⟩ := hdvd
    have hrPos : 0 < r := by omega
    have hkLt : k < 2 := by
      have hvalLt := ZMod.val_lt δ
      rw [hk] at hvalLt
      nlinarith
    have hkPos : 0 < k := by
      by_contra hkNot
      have hk0 : k = 0 := by omega
      have hval0 : δ.val = 0 := by rw [hk, hk0, mul_zero]
      exact hδ0 (δ.val_eq_zero.mp hval0)
    have hk1 : k = 1 := by omega
    apply ZMod.val_injective
    rw [hk, hk1, mul_one, ZMod.val_cast_of_lt]
    omega
  · rintro rfl
    have hrn : r ∣ 2 * r := by
      use 2
      omega
    have hval : ((r : ZMod (2 * r))).val = r := by
      rw [ZMod.val_cast_of_lt]
      omega
    refine ⟨(mem_admissibleDifferences_iff _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hz
      have hzero : r = 0 := by
        simpa [hval] using congrArg ZMod.val hz
      omega
    · exact (sourceLength_dvd_val_ne_one_negOne hr3 hrn _
        (by rw [hval])).1
    · exact (sourceLength_dvd_val_ne_one_negOne hr3 hrn _
        (by rw [hval])).2
    · rw [hval]

/-- The diagonal anchor support on the doubled target contains at most one
point from each deck fiber.  The other common neighbor of an antipodal pair
is already its base-cycle vertex, so `C₄`-freeness excludes the target
anchor from being a second one. -/
theorem cycleCover_diagAnchor_not_both_halfTurns
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (v : ZMod (2 * r) → V)
    (hsep : ∀ x y, u x ≠ v y)
    (hvinj : Function.Injective v)
    (f : ZMod (2 * r) → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (y : ZMod (2 * r)) :
    ¬ (y ∈ mixedAnchorSupport G (v 0) v ∧
      y + (r : ZMod (2 * r)) ∈ mixedAnchorSupport G (v 0) v) := by
  rw [mem_mixedAnchorSupport_iff, mem_mixedAnchorSupport_iff]
  exact cycleCover_halfTurn_commonNeighbor_exclusive G hfree u v hvinj f
    hadj horient y (v 0) (Ne.symm (hsep (f y) 0))

/-- An antipodal matching on a doubled cycle cannot coexist with all cycle
edges: two consecutive matching edges and the corresponding two cycle edges
are the rim of a `C₄`.  Consequently, if the exceptional half-turn diagonal
edge occurs, the doubled defect component cannot be triangle-free colored. -/
theorem no_halfTurn_matching_of_cycle_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (v : ZMod (2 * r) → V) (hvinj : Function.Injective v)
    (hcycle : ∀ y, G.Adj (v y) (v (y + 1)))
    (hmatch : ∀ y, G.Adj (v y)
      (v (y + (r : ZMod (2 * r))))) : False := by
  letI : Fact (1 < 2 * r) := ⟨by omega⟩
  let z0 : ZMod (2 * r) := 0
  let z1 : ZMod (2 * r) := 1
  let zr : ZMod (2 * r) := (r : ZMod (2 * r))
  let zr1 : ZMod (2 * r) := ((r + 1 : ℕ) : ZMod (2 * r))
  have hval0 : z0.val = 0 := by simp [z0]
  have hval1 : z1.val = 1 := by
    simp [z1, ZMod.val_one]
  have hvalr : zr.val = r := by
    dsimp only [zr]
    rw [ZMod.val_cast_of_lt]
    omega
  have hvalr1 : zr1.val = r + 1 := by
    dsimp only [zr1]
    rw [ZMod.val_cast_of_lt]
    omega
  have hne {x y : ZMod (2 * r)} (hxy : x.val ≠ y.val) : v x ≠ v y :=
    hvinj.ne (fun h ↦ hxy (congrArg ZMod.val h))
  have h01 : G.Adj (v z0) (v z1) := by
    simpa [z0, z1] using hcycle 0
  have h1r1 : G.Adj (v z1) (v zr1) := by
    simpa [z1, zr1, Nat.cast_add, add_comm] using hmatch 1
  have hr1r : G.Adj (v zr1) (v zr) := by
    have h := (hcycle zr).symm
    simpa [zr, zr1, Nat.cast_add, add_assoc] using h
  have hr0 : G.Adj (v zr) (v z0) := by
    simpa [zr, z0] using (hmatch 0).symm
  apply hfree
  exact containsC4_of_rim h01 h1r1 hr1r hr0
    (hne (by rw [hval0, hvalr1]; omega))
    (hne (by rw [hval1, hvalr]; omega))
    (hne (by rw [hval1, hval0]; omega))
    (hne (by rw [hval1, hvalr1]; omega))
    (hne (by rw [hvalr, hval0]; omega))
    (hne (by rw [hvalr, hvalr1]; omega))

end

end Erdos85
