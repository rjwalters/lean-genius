import Proofs.Erdos85PolarityOddSecant

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

/-- In odd characteristic, the absolute locus of the orthogonal polarity has
at least `q + 1` points.  An explicit rational parametrization of the conic
gives an injection from `Option K` into the absolute locus. -/
theorem card_absolutePoints_ge_card_add_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    Nat.card K + 1 ≤ (absolutePoints K).card := by
  letI := Fintype.ofFinite K
  obtain ⟨a, haa⟩ := exists_selfOrthogonal K
  obtain ⟨b, habno⟩ := Projectivization.exists_not_self_orthogonal a
  have haavec : a.rep ⬝ᵥ a.rep = 0 :=
    (Projectivization.orthogonal_mk a.rep_nonzero a.rep_nonzero).mp
      (by simpa using haa)
  have habvec : a.rep ⬝ᵥ b.rep ≠ 0 := by
    intro hdot
    apply habno
    simpa using
      (Projectivization.orthogonal_mk a.rep_nonzero b.rep_nonzero).mpr hdot
  let w : Fin 3 → K := a.rep ⨯₃ b.rep
  let alpha : K → K := fun t =>
    -(b.rep ⬝ᵥ b.rep + t ^ 2 * (w ⬝ᵥ w)) /
      (2 * (a.rep ⬝ᵥ b.rep))
  let x : K → Fin 3 → K := fun t => b.rep + t • w + alpha t • a.rep
  have haw : a.rep ⬝ᵥ w = 0 := by simp [w]
  have hbw : b.rep ⬝ᵥ w = 0 := by simp [w]
  have hwa : w ⬝ᵥ a.rep = 0 := by rw [dotProduct_comm]; exact haw
  have hwb : w ⬝ᵥ b.rep = 0 := by rw [dotProduct_comm]; exact hbw
  have hwwEq : w ⬝ᵥ w = -(a.rep ⬝ᵥ b.rep) ^ 2 := by
    dsimp [w]
    rw [cross_dot_cross, haavec]
    rw [show b.rep ⬝ᵥ a.rep = a.rep ⬝ᵥ b.rep by
      exact dotProduct_comm b.rep a.rep]
    ring
  have hww : w ⬝ᵥ w ≠ 0 := by
    rw [hwwEq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 habvec)
  have hxiso : ∀ t, x t ⬝ᵥ x t = 0 := by
    intro t
    simp only [x, alpha, add_dotProduct, dotProduct_add, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [haavec, haw, hwa, hbw, hwb]
    rw [show b.rep ⬝ᵥ a.rep = a.rep ⬝ᵥ b.rep by
      exact dotProduct_comm b.rep a.rep]
    field_simp
    ring
  have hax : ∀ t, a.rep ⬝ᵥ x t = a.rep ⬝ᵥ b.rep := by
    intro t
    simp only [x, alpha, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [haavec, haw]
    ring
  have hwx : ∀ t, w ⬝ᵥ x t = t * (w ⬝ᵥ w) := by
    intro t
    simp only [x, alpha, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [hwa, hwb]
    ring
  have hx0 : ∀ t, x t ≠ 0 := by
    intro t ht
    have hz : a.rep ⬝ᵥ x t = 0 := by rw [ht]; simp
    exact habvec ((hax t).symm.trans hz)
  let xp : K → Projectivization K (Fin 3 → K) := fun t =>
    Projectivization.mk K (x t) (hx0 t)
  have hxpabs : ∀ t, Projectivization.orthogonal (xp t) (xp t) := by
    intro t
    exact (Projectivization.orthogonal_mk (hx0 t) (hx0 t)).mpr (hxiso t)
  have haxpno : ∀ t, ¬ Projectivization.orthogonal a (xp t) := by
    intro t hat
    have hz : a.rep ⬝ᵥ x t = 0 :=
      (Projectivization.orthogonal_mk a.rep_nonzero (hx0 t)).mp
        (by simpa [xp] using hat)
    exact habvec ((hax t).symm.trans hz)
  have hxpinj : Function.Injective xp := by
    intro s t hst
    obtain ⟨lam, hlam⟩ :=
      (Projectivization.mk_eq_mk_iff' K (x s) (x t) (hx0 s) (hx0 t)).mp
        (by simpa [xp] using hst)
    have hlam1 : lam = 1 := by
      have hd := congrArg (fun z => a.rep ⬝ᵥ z) hlam
      simp only [dotProduct_smul, smul_eq_mul, hax] at hd
      apply mul_right_cancel₀ habvec
      simpa using hd
    subst lam
    simp only [one_smul] at hlam
    have hd := congrArg (fun z => w ⬝ᵥ z) hlam
    rw [hwx, hwx] at hd
    exact mul_right_cancel₀ hww hd.symm
  let f : Option K → {p // p ∈ absolutePoints K} := fun o =>
    match o with
    | none => ⟨a, (mem_absolutePoints K a).mpr haa⟩
    | some t => ⟨xp t, (mem_absolutePoints K (xp t)).mpr (hxpabs t)⟩
  have hf : Function.Injective f := by
    intro s t hst
    cases s with
    | none =>
        cases t with
        | none => rfl
        | some t =>
            exfalso
            have heq : a = xp t := congrArg Subtype.val hst
            exact haxpno t (by rw [← heq]; exact haa)
    | some s =>
        cases t with
        | none =>
            exfalso
            have heq : xp s = a := congrArg Subtype.val hst
            exact haxpno s (by rw [heq]; exact haa)
        | some t =>
            have heq : xp s = xp t := congrArg Subtype.val hst
            exact congrArg some (hxpinj heq)
  have hc := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_option, Nat.card_eq_fintype_card] using hc

/-- Deleting any number of absolute points up to `q + 1` leaves an
odd-characteristic polarity witness with minimum degree at least `q - 1`. -/
theorem c4FreeMinDegreeWitness_odd_absolute_band
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {k : ℕ} (hk : k ≤ Nat.card K + 1) :
    C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - k) (Nat.card K - 1) := by
  apply c4FreeMinDegreeWitness_odd_delete_absolute_card K h2
    (hk.trans (card_absolutePoints_ge_card_add_one K h2))
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have hsize : Nat.card K + 2 ≤
      (Nat.card K + 1) * Nat.card K + 1 := by nlinarith
  omega

/-- Throughout the `q + 1`-point odd-characteristic conic-deletion band, the
threshold is one of the two consecutive values `q` and `q + 1`. -/
theorem minDegreeForC4_odd_absolute_band_bounds
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {k : ℕ} (hk : k ≤ Nat.card K + 1) :
    Nat.card K ≤ minDegreeForC4
        ((Nat.card K + 1) * Nat.card K + 1 - k) ∧
      minDegreeForC4 ((Nat.card K + 1) * Nat.card K + 1 - k) ≤
        Nat.card K + 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have horder : 4 ≤ (Nat.card K + 1) * Nat.card K + 1 - k := by
    have hsquare : 4 ≤ Nat.card K * Nat.card K := by nlinarith
    apply hsquare.trans
    apply Nat.le_sub_of_add_le
    nlinarith
  constructor
  · have hw := c4FreeMinDegreeWitness_odd_absolute_band K h2 hk
    have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 horder).1 hw
    omega
  · by_cases hk0 : k = 0
    · subst k
      simpa using (minDegreeForC4_projectivePlane K).le
    · apply minDegreeForC4_le_of_le_mul_pred (by omega)
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      change (Nat.card K + 1) * Nat.card K + 1 - k ≤
        (Nat.card K + 1) * Nat.card K
      omega

end Erdos85.Polarity
