import Proofs.Erdos85SizeTwoEigenlineCycleCoordinateNormalization
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Grid coordinates from a parity-normalized component cycle

This file supplies the graph-facing consumer of the abstract `C_{2q}`
normalization.  The product coordinate `(x,b) : Fin q × Fin 2` is sent to
the cycle coordinate `b + 2x`; the two parity classes therefore become the
two `ZMod q` axes used by the eigenline grid.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

variable {q : Nat} [NeZero q]

@[simp] private theorem zmod_finEquiv_symm_val (x : ZMod q) :
    ((ZMod.finEquiv q).symm x).val = x.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The standard product coordinate `b + 2x` on `C_{2q}`. -/
def sizeTwoCyclePairCoord (x : ZMod q) (b : Fin 2) : Fin (2 * q) :=
  finCongr (Nat.mul_comm q 2) <|
    finProdFinEquiv ((ZMod.finEquiv q).symm x, b)

@[simp] theorem sizeTwoCyclePairCoord_val (x : ZMod q) (b : Fin 2) :
    (sizeTwoCyclePairCoord x b).val = b.val + 2 * x.val := by
  simp [sizeTwoCyclePairCoord, finProdFinEquiv]

/-- The even and odd product coordinates partition the whole cycle. -/
def sizeTwoCyclePairEquiv : ZMod q × Fin 2 ≃ Fin (2 * q) :=
  (ZMod.finEquiv q).symm.toEquiv.prodCongr (Equiv.refl (Fin 2)) |>.trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm q 2)))

@[simp] theorem sizeTwoCyclePairEquiv_apply (xb : ZMod q × Fin 2) :
    sizeTwoCyclePairEquiv xb = sizeTwoCyclePairCoord xb.1 xb.2 := rfl

theorem sizeTwoCyclePairCoord_injective :
    Function.Injective (fun xb : ZMod q × Fin 2 =>
      sizeTwoCyclePairCoord xb.1 xb.2) := by
  intro a b h
  apply (@sizeTwoCyclePairEquiv q _).injective
  exact h

/-- In product coordinates the cycle edges between the even and odd axes
are exactly the two normalized shifts `y=x` and `y=x-1`. -/
theorem cycleGraph_adj_sizeTwoCyclePairCoord_zero_one
    (hq : 2 ≤ q) (x y : ZMod q) :
    (cycleGraph (2 * q)).Adj
      (sizeTwoCyclePairCoord x 0) (sizeTwoCyclePairCoord y 1) ↔
      y = x ∨ y = x - 1 := by
  letI : Fact (1 < q) := ⟨by omega⟩
  rw [cycleGraph_adj']
  have hsecond :
      ((sizeTwoCyclePairCoord y 1 - sizeTwoCyclePairCoord x 0).val = 1) ↔
        y = x := by
    constructor
    · intro h
      apply ZMod.val_injective q
      by_cases hxy : x.val ≤ y.val
      · have hle : sizeTwoCyclePairCoord x 0 ≤
            sizeTwoCyclePairCoord y 1 := by
          change (sizeTwoCyclePairCoord x 0).val ≤
            (sizeTwoCyclePairCoord y 1).val
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        rw [Fin.sub_val_of_le hle] at h
        simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one] at h
        omega
      · have hlt : (sizeTwoCyclePairCoord y 1).val <
            (sizeTwoCyclePairCoord x 0).val := by
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        have hv :
            (sizeTwoCyclePairCoord y 1 -
              sizeTwoCyclePairCoord x 0).val =
              2 * q - (sizeTwoCyclePairCoord x 0).val +
                (sizeTwoCyclePairCoord y 1).val := by
          rw [Fin.val_sub, Nat.mod_eq_of_lt]
          omega
        rw [hv] at h
        simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one] at h
        have hx := x.val_lt
        have hy := y.val_lt
        omega
    · rintro rfl
      rw [Fin.sub_val_of_le]
      · simp [sizeTwoCyclePairCoord_val]
      · change (sizeTwoCyclePairCoord y 0).val ≤
          (sizeTwoCyclePairCoord y 1).val
        simp [sizeTwoCyclePairCoord_val]
  have hfirst :
      ((sizeTwoCyclePairCoord x 0 - sizeTwoCyclePairCoord y 1).val = 1) ↔
        y = x - 1 := by
    constructor
    · intro h
      by_cases hyx : y.val < x.val
      · have hle : sizeTwoCyclePairCoord y 1 ≤
            sizeTwoCyclePairCoord x 0 := by
          change (sizeTwoCyclePairCoord y 1).val ≤
            (sizeTwoCyclePairCoord x 0).val
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        rw [Fin.sub_val_of_le hle] at h
        simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one] at h
        have hv : x.val = y.val + 1 := by omega
        rw [← ZMod.natCast_zmod_val y, ← ZMod.natCast_zmod_val x]
        rw [hv]
        push_cast
        ring
      · have hlt : (sizeTwoCyclePairCoord x 0).val <
            (sizeTwoCyclePairCoord y 1).val := by
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        have hv :
            (sizeTwoCyclePairCoord x 0 -
              sizeTwoCyclePairCoord y 1).val =
              2 * q - (sizeTwoCyclePairCoord y 1).val +
                (sizeTwoCyclePairCoord x 0).val := by
          rw [Fin.val_sub, Nat.mod_eq_of_lt]
          omega
        rw [hv] at h
        simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one] at h
        have hx := x.val_lt
        have hy := y.val_lt
        have hx0 : x.val = 0 := by omega
        have hyq : y.val + 1 = q := by omega
        rw [← ZMod.natCast_zmod_val y, ← ZMod.natCast_zmod_val x]
        have hcast := congrArg (fun n : Nat => (n : ZMod q)) hyq
        push_cast at hcast
        rw [ZMod.natCast_self] at hcast
        rw [hx0]
        linear_combination hcast
    · intro hyx
      have hyx' : y + 1 = x := by rw [hyx]; ring
      have hval := congrArg ZMod.val hyx'
      rw [ZMod.val_add] at hval
      simp only [ZMod.val_one] at hval
      have hy := y.val_lt
      by_cases hlt : y.val + 1 < q
      · rw [Nat.mod_eq_of_lt hlt] at hval
        have hle : sizeTwoCyclePairCoord y 1 ≤
            sizeTwoCyclePairCoord x 0 := by
          change (sizeTwoCyclePairCoord y 1).val ≤
            (sizeTwoCyclePairCoord x 0).val
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        rw [Fin.sub_val_of_le hle]
        simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
        omega
      · have hyq : y.val + 1 = q := by omega
        rw [hyq, Nat.mod_self] at hval
        have hlt' : (sizeTwoCyclePairCoord x 0).val <
            (sizeTwoCyclePairCoord y 1).val := by
          simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        rw [Fin.val_sub, Nat.mod_eq_of_lt]
        · simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
        · simp only [sizeTwoCyclePairCoord_val, Fin.val_zero, Fin.val_one]
          omega
  tauto

section GraphCoordinates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The exact coordinate package expected by the graph-derived cyclic grid. -/
structure SizeTwoCycleGridCoordinates
    (c : H.ConnectedComponent) (s : V → ℤ) (q : Nat) where
  pval : ZMod q → V
  nval : ZMod q → V
  p_mem_sign : ∀ x, pval x ∈ c.supp ∧ s (pval x) = 1
  n_mem_sign : ∀ y, nval y ∈ c.supp ∧ s (nval y) = -1
  p_injective : Function.Injective pval
  n_injective : Function.Injective nval
  p_surjective : ∀ z, z ∈ c.supp → s z = 1 → ∃ x, pval x = z
  n_surjective : ∀ z, z ∈ c.supp → s z = -1 → ∃ y, nval y = z
  adj_iff : ∀ x y, H.Adj (pval x) (nval y) ↔ y = x ∨ y = x - 1

theorem cycleSign_at_pairCoord_zero
    (c : H.ConnectedComponent) (s : V → ℤ)
    (e : Fin (2 * q) ≃ c.supp)
    (hs : ∀ i, s (e i).1 = (-1 : ℤ) ^ i.val * s (e 0).1)
    (hphase : s (e 0).1 = 1) (x : ZMod q) :
    s (e (sizeTwoCyclePairCoord x 0)).1 = 1 := by
  rw [hs, hphase, sizeTwoCyclePairCoord_val]
  simp [pow_mul]

theorem cycleSign_at_pairCoord_one
    (c : H.ConnectedComponent) (s : V → ℤ)
    (e : Fin (2 * q) ≃ c.supp)
    (hs : ∀ i, s (e i).1 = (-1 : ℤ) ^ i.val * s (e 0).1)
    (hphase : s (e 0).1 = 1) (x : ZMod q) :
    s (e (sizeTwoCyclePairCoord x 1)).1 = -1 := by
  rw [hs, hphase, sizeTwoCyclePairCoord_val]
  simp [pow_add, pow_mul]

/-- A positively phased parity-normalized component equivalence supplies all
`pval/nval` coordinate hypotheses used by the graph-side grid theorem. -/
def SizeTwoCycleGridCoordinates.ofPositiveNormalizedCycle
    (hq : 2 ≤ q)
    (c : H.ConnectedComponent) (s : V → ℤ)
    (e : Fin (2 * q) ≃ c.supp)
    (he : ∀ i j, (cycleGraph (2 * q)).Adj i j ↔
      H.Adj (e i).1 (e j).1)
    (hs : ∀ i, s (e i).1 = (-1 : ℤ) ^ i.val * s (e 0).1)
    (hphase : s (e 0).1 = 1) :
    SizeTwoCycleGridCoordinates H c s q where
  pval x := (e (sizeTwoCyclePairCoord x 0)).1
  nval y := (e (sizeTwoCyclePairCoord y 1)).1
  p_mem_sign x := ⟨(e (sizeTwoCyclePairCoord x 0)).2,
    cycleSign_at_pairCoord_zero H c s e hs hphase x⟩
  n_mem_sign y := ⟨(e (sizeTwoCyclePairCoord y 1)).2,
    cycleSign_at_pairCoord_one H c s e hs hphase y⟩
  p_injective := by
    intro x y hxy
    have heq : e (sizeTwoCyclePairCoord x 0) =
        e (sizeTwoCyclePairCoord y 0) := Subtype.ext hxy
    have hc := e.injective heq
    have hp : (x, (0 : Fin 2)) = (y, (0 : Fin 2)) :=
      sizeTwoCyclePairEquiv.injective hc
    exact congrArg Prod.fst hp
  n_injective := by
    intro x y hxy
    have heq : e (sizeTwoCyclePairCoord x 1) =
        e (sizeTwoCyclePairCoord y 1) := Subtype.ext hxy
    have hc := e.injective heq
    have hp : (x, (1 : Fin 2)) = (y, (1 : Fin 2)) :=
      sizeTwoCyclePairEquiv.injective hc
    exact congrArg Prod.fst hp
  p_surjective := by
    intro z hz hsz
    let zi : c.supp := ⟨z, hz⟩
    obtain ⟨⟨x, b⟩, hb⟩ :=
      sizeTwoCyclePairEquiv.surjective (e.symm zi)
    have heq : e (sizeTwoCyclePairCoord x b) = zi := by
      calc
        e (sizeTwoCyclePairCoord x b) =
            e (sizeTwoCyclePairEquiv (x, b)) := by
              rw [sizeTwoCyclePairEquiv_apply]
        _ = e (e.symm zi) := congrArg e hb
        _ = zi := e.apply_symm_apply zi
    fin_cases b
    · exact ⟨x, congrArg Subtype.val (by simpa using heq)⟩
    · have hn := cycleSign_at_pairCoord_one H c s e hs hphase x
      have heq' : e (sizeTwoCyclePairCoord x 1) = zi := by simpa using heq
      rw [heq'] at hn
      simp only [zi] at hn
      omega
  n_surjective := by
    intro z hz hsz
    let zi : c.supp := ⟨z, hz⟩
    obtain ⟨⟨x, b⟩, hb⟩ :=
      sizeTwoCyclePairEquiv.surjective (e.symm zi)
    have heq : e (sizeTwoCyclePairCoord x b) = zi := by
      calc
        e (sizeTwoCyclePairCoord x b) =
            e (sizeTwoCyclePairEquiv (x, b)) := by
              rw [sizeTwoCyclePairEquiv_apply]
        _ = e (e.symm zi) := congrArg e hb
        _ = zi := e.apply_symm_apply zi
    fin_cases b
    · have hp := cycleSign_at_pairCoord_zero H c s e hs hphase x
      have heq' : e (sizeTwoCyclePairCoord x 0) = zi := by simpa using heq
      rw [heq'] at hp
      simp only [zi] at hp
      omega
    · exact ⟨x, congrArg Subtype.val (by simpa using heq)⟩
  adj_iff x y :=
    (he (sizeTwoCyclePairCoord x 0)
      (sizeTwoCyclePairCoord y 1)).symm.trans
        (cycleGraph_adj_sizeTwoCyclePairCoord_zero_one hq x y)

/-- Negating the sign exchanges the two axes.  Reindexing the new negative
axis by one step restores the standard `{0,-1}` adjacency convention. -/
def SizeTwoCycleGridCoordinates.ofNegated
    (c : H.ConnectedComponent) (s : V → ℤ)
    (base : SizeTwoCycleGridCoordinates H c (fun z => -s z) q) :
    SizeTwoCycleGridCoordinates H c s q where
  pval x := base.nval x
  nval y := base.pval (y + 1)
  p_mem_sign x := by
    obtain ⟨hx, hsx⟩ := base.n_mem_sign x
    exact ⟨hx, by omega⟩
  n_mem_sign y := by
    obtain ⟨hy, hsy⟩ := base.p_mem_sign (y + 1)
    exact ⟨hy, by omega⟩
  p_injective := base.n_injective
  n_injective := by
    intro x y hxy
    exact add_right_cancel (base.p_injective hxy)
  p_surjective := by
    intro z hz hsz
    obtain ⟨x, hx⟩ := base.n_surjective z hz (by omega)
    exact ⟨x, hx⟩
  n_surjective := by
    intro z hz hsz
    obtain ⟨x, hx⟩ := base.p_surjective z hz (by omega)
    refine ⟨x - 1, ?_⟩
    simpa only [sub_add_cancel] using hx
  adj_iff x y := by
    rw [H.adj_comm]
    rw [base.adj_iff]
    constructor
    · rintro (h | h)
      · right; rw [h]; ring
      · left; rw [h]; ring
    · rintro (h | h)
      · right; rw [h]; ring
      · left; rw [h]; ring

/-- **Graph-specific `C₂q` consumer bridge.**  A size-`2q` component of a
finite two-regular graph with a `{±1}` edge-flipping sign admits the complete
`ZMod q × ZMod q` axis-coordinate package expected by the cyclic eigenline
grid.  The construction is uniform in `q` and handles the global sign phase
by exchanging and reindexing the two axes. -/
theorem exists_sizeTwoCycleGridCoordinates
    (hdeg : ∀ x, H.degree x = 2)
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (c : H.ConnectedComponent) (hc : c.supp.ncard = 2 * q)
    (s : V → ℤ)
    (hsign : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Nonempty (SizeTwoCycleGridCoordinates H c s q) := by
  obtain ⟨e, he, hs⟩ :=
    exists_componentCycleEquiv_sign_normalized H hdeg q (by omega) c hc s hflip
  rcases hsign (e 0).1 (e 0).2 with hphase | hphase
  · have hsneg : ∀ i, -s (e i).1 =
        (-1 : ℤ) ^ i.val * (-s (e 0).1) := by
      intro i
      calc
        -s (e i).1 = -((-1 : ℤ) ^ i.val * s (e 0).1) :=
          congrArg Neg.neg (hs i)
        _ = (-1 : ℤ) ^ i.val * (-s (e 0).1) := by ring
    have hphaseNeg : -s (e 0).1 = 1 := by omega
    let base := SizeTwoCycleGridCoordinates.ofPositiveNormalizedCycle
      H hq c (fun z => -s z) e he hsneg hphaseNeg
    exact ⟨SizeTwoCycleGridCoordinates.ofNegated H c s base⟩
  · exact ⟨SizeTwoCycleGridCoordinates.ofPositiveNormalizedCycle
      H hq c s e he hs hphase⟩

end GraphCoordinates

end

end Erdos85

#print axioms Erdos85.exists_sizeTwoCycleGridCoordinates
