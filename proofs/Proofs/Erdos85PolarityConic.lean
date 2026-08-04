import Proofs.Erdos85PolarityOddSecant

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

private theorem eq_smul_isotropic_of_two_orthogonal
    {K : Type*} [Field K]
    (a b d : Fin 3 → K) (haa : a ⬝ᵥ a = 0) (hab : a ⬝ᵥ b ≠ 0)
    (had : a ⬝ᵥ d = 0) (hwd : (a ⨯₃ b) ⬝ᵥ d = 0) :
    ∃ lam : K, lam • a = d := by
  let w := a ⨯₃ b
  let lam := (b ⬝ᵥ d) / (b ⬝ᵥ a)
  let z := d - lam • a
  have hba : b ⬝ᵥ a ≠ 0 := by
    rw [dotProduct_comm]
    exact hab
  have haz : a ⬝ᵥ z = 0 := by
    simp [z, dotProduct_sub, dotProduct_smul, haa, had]
  have hwz : w ⬝ᵥ z = 0 := by
    have hwa : w ⬝ᵥ a = 0 := by
      rw [dotProduct_comm]
      simp [w]
    simp [z, dotProduct_sub, dotProduct_smul, hwa, hwd, w]
  have hbz : b ⬝ᵥ z = 0 := by
    simp only [z, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    dsimp [lam]
    field_simp
    ring
  let A : Matrix (Fin 3) (Fin 3) K := ![a, b, w]
  have hAz : A *ᵥ z = 0 := by
    funext i
    fin_cases i <;> simp [A, Matrix.mulVec, haz, hbz, hwz]
  have hdetEq : A.det = -(a ⬝ᵥ b) ^ 2 := by
    dsimp [A]
    rw [← triple_product_eq_det, cross_cross_eq_smul_sub_smul']
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, haa, mul_zero]
    ring
  have hz : z = 0 := by
    by_contra hz0
    have hdet0 : A.det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨z, hz0, hAz⟩
    exact (neg_ne_zero.mpr (pow_ne_zero 2 hab)) (hdetEq.symm.trans hdet0)
  refine ⟨lam, ?_⟩
  dsimp [z] at hz
  exact sub_eq_zero.mp hz |>.symm

/-- In odd characteristic, the absolute locus of the orthogonal polarity has
at least `q + 1` points.  An explicit rational parametrization of the conic
gives an injection from `Option K` into the absolute locus. -/
theorem card_absolutePoints_eq_card_add_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    (absolutePoints K).card = Nat.card K + 1 := by
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
  have hfsurj : Function.Surjective f := by
    rintro ⟨p, hp⟩
    have hpp : Projectivization.orthogonal p p :=
      (mem_absolutePoints K p).mp hp
    by_cases hpa : p = a
    · subst p
      exact ⟨none, rfl⟩
    · have hapno : ¬ Projectivization.orthogonal a p := by
        intro hap
        have hadj : (graph K).Adj a p :=
          (graph_adj_iff a p).mpr ⟨Ne.symm hpa, hap⟩
        exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj haa) hpp
      have hpvec : p.rep ⬝ᵥ p.rep = 0 :=
        (Projectivization.orthogonal_mk p.rep_nonzero p.rep_nonzero).mp
          (by simpa using hpp)
      have hapvec : a.rep ⬝ᵥ p.rep ≠ 0 := by
        intro hz
        apply hapno
        simpa using
          (Projectivization.orthogonal_mk a.rep_nonzero p.rep_nonzero).mpr hz
      let mu : K := (a.rep ⬝ᵥ b.rep) / (a.rep ⬝ᵥ p.rep)
      let y : Fin 3 → K := mu • p.rep
      have hay : a.rep ⬝ᵥ y = a.rep ⬝ᵥ b.rep := by
        simp only [y, dotProduct_smul, smul_eq_mul]
        dsimp [mu]
        field_simp
      have hyiso : y ⬝ᵥ y = 0 := by
        simp [y, smul_dotProduct, dotProduct_smul, hpvec]
      let t : K := (w ⬝ᵥ y) / (w ⬝ᵥ w)
      have had : a.rep ⬝ᵥ (y - x t) = 0 := by
        rw [dotProduct_sub, hay, hax]
        ring
      have hwd : w ⬝ᵥ (y - x t) = 0 := by
        rw [dotProduct_sub, hwx]
        dsimp [t]
        field_simp
        ring
      obtain ⟨lam, hlam⟩ := eq_smul_isotropic_of_two_orthogonal
        a.rep b.rep (y - x t) haavec habvec had (by simpa [w] using hwd)
      have hyEq : y = x t + lam • a.rep := by
        rw [hlam]
        abel
      have hxta : x t ⬝ᵥ a.rep = a.rep ⬝ᵥ b.rep := by
        rw [dotProduct_comm]
        exact hax t
      have hi := hyiso
      rw [hyEq] at hi
      simp only [add_dotProduct, dotProduct_add, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at hi
      rw [hxiso, hax, hxta, haavec] at hi
      have hprod : lam * (2 * (a.rep ⬝ᵥ b.rep)) = 0 := by
        linear_combination hi
      have hlam0 : lam = 0 :=
        (mul_eq_zero.mp hprod).resolve_right (mul_ne_zero h2 habvec)
      have hyx : y = x t := by simpa [hlam0] using hyEq
      refine ⟨some t, ?_⟩
      apply Subtype.ext
      change xp t = p
      rw [← Projectivization.mk_rep p]
      change Projectivization.mk K (x t) (hx0 t) =
        Projectivization.mk K p.rep p.rep_nonzero
      apply (Projectivization.mk_eq_mk_iff' K (x t) p.rep
        (hx0 t) p.rep_nonzero).mpr
      refine ⟨mu, ?_⟩
      change y = x t
      exact hyx
  have hc' := Fintype.card_le_of_surjective f hfsurj
  apply Nat.le_antisymm
  · simpa [Fintype.card_option, Nat.card_eq_fintype_card] using hc'
  · simpa [Fintype.card_option, Nat.card_eq_fintype_card] using hc

/-- Lower-bound orientation of the exact odd-characteristic conic count. -/
theorem card_absolutePoints_ge_card_add_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    Nat.card K + 1 ≤ (absolutePoints K).card := by
  rw [card_absolutePoints_eq_card_add_one K h2]

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
