import Proofs.Erdos85CycleCoverRigidity

/-!
# Binary rigidity for equal odd-cycle blocks

After the discrete d'Alembert decomposition, an equal-cycle intertwiner has
the form `f(y-x)+g(y+x)`.  A genuinely binary matrix cannot contain both a
nonconstant travelling and a nonconstant reflected wave: the four corners of
the resulting additive rectangle would have to be the crossed `0/1` pattern,
which violates the rectangle identity.  Hence every binary block is either
circulant or reverse-circulant.
-/

namespace Erdos85

/-- On an odd cyclic group, invariance under translation by two is the same
as constancy. -/
theorem oddZMod_twoPeriodic_constant
    {r : ℕ} [NeZero r] (hr : Odd r) (p : ZMod r → ℤ)
    (hstep : ∀ z, p (z + 2) = p z) :
    ∀ z w, p z = p w := by
  have htwo : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hr)
  have hsurj : Function.Surjective (fun t : ZMod r ↦ 2 * t) :=
    (Finite.injective_iff_bijective.mp htwo.mul_right_injective).surjective
  intro z w
  obtain ⟨t, ht⟩ := hsurj (w - z)
  have hiter : ∀ k : ℕ, p (z + 2 * (k : ZMod r)) = p z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          p (z + 2 * ((k + 1 : ℕ) : ZMod r)) =
              p ((z + 2 * (k : ZMod r)) + 2) := by
                congr 1
                push_cast
                ring
          _ = p (z + 2 * (k : ZMod r)) := hstep _
          _ = p z := ih
  have htval := hiter t.val
  rw [ZMod.natCast_zmod_val] at htval
  have hzw : z + 2 * t = w := by
    have ht' : 2 * t = w - z := by simpa using ht
    rw [ht']
    ring
  rw [hzw] at htval
  exact htval.symm

/-- Discrete d'Alembert decomposition on an odd cyclic grid.  The displayed
rectangle equation is the cycle-intertwining recurrence after the invertible
coordinate change `(x,y) ↦ (y-x,y+x)`. -/
theorem oddZMod_dalembert_decomposition
    {r : ℕ} [NeZero r] (hr : Odd r)
    (F : ZMod r → ZMod r → ℤ)
    (hrect : ∀ u v,
      F (u + 1) (v - 1) + F (u - 1) (v + 1) =
        F (u + 1) (v + 1) + F (u - 1) (v - 1)) :
    ∃ f g : ZMod r → ℤ, ∀ u v, F u v = f u + g v := by
  have hdiff (u v : ZMod r) :
      F (u + 2) (v + 2) - F u (v + 2) =
        F (u + 2) v - F u v := by
    have h := hrect (u + 1) (v + 1)
    have hu1m : u + 1 - 1 = u := by ring
    have hv1m : v + 1 - 1 = v := by ring
    have hu1p : u + 1 + 1 = u + 2 := by ring
    have hv1p : v + 1 + 1 = v + 2 := by ring
    rw [hu1m, hv1m, hu1p, hv1p] at h
    omega
  have hdiff_const (u v : ZMod r) :
      F (u + 2) v - F u v = F (u + 2) 0 - F u 0 := by
    let p : ZMod r → ℤ := fun w ↦ F (u + 2) w - F u w
    have hp : ∀ w, p (w + 2) = p w := by
      intro w
      exact hdiff u w
    exact oddZMod_twoPeriodic_constant hr p hp v 0
  have hseparate (u v : ZMod r) :
      F u v - F u 0 = F 0 v - F 0 0 := by
    let p : ZMod r → ℤ := fun w ↦ F w v - F w 0
    have hp : ∀ w, p (w + 2) = p w := by
      intro w
      dsimp only [p]
      have h := hdiff_const w v
      linear_combination h
    exact oddZMod_twoPeriodic_constant hr p hp u 0
  refine ⟨(fun u ↦ F u 0), (fun v ↦ F 0 v - F 0 0), ?_⟩
  intro u v
  have h := hseparate u v
  dsimp
  linear_combination h

/-- Two integer-valued functions whose every pairwise sum is binary cannot
both be nonconstant. -/
theorem binary_additive_rectangle_dichotomy
    {X Y : Type*} (f : X → ℤ) (g : Y → ℤ)
    (hbinary : ∀ x y, f x + g y = 0 ∨ f x + g y = 1) :
    (∀ x₀ x₁, f x₀ = f x₁) ∨ (∀ y₀ y₁, g y₀ = g y₁) := by
  by_cases hf : ∀ x₀ x₁, f x₀ = f x₁
  · exact Or.inl hf
  · right
    push_neg at hf
    obtain ⟨x₀, x₁, hx⟩ := hf
    intro y₀ y₁
    rcases hbinary x₀ y₀ with h00 | h00 <;>
      rcases hbinary x₀ y₁ with h01 | h01 <;>
      rcases hbinary x₁ y₀ with h10 | h10 <;>
      rcases hbinary x₁ y₁ with h11 | h11 <;> omega

/-- Once a cycle-intertwining block has been decomposed into its two discrete
travelling waves, binary entries force one global orientation. -/
theorem binary_dalembertBlock_orientation
    {r : ℕ} [NeZero r]
    (hr : Odd r)
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (f g : ZMod r → ℤ)
    (hdecomp : ∀ x y, B x y = f (y - x) + g (y + x))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1) :
    (∀ x y, B (x + 1) (y + 1) = B x y) ∨
      (∀ x y, B (x + 1) (y - 1) = B x y) := by
  have hsums : ∀ u v, f u + g v = 0 ∨ f u + g v = 1 := by
    intro u v
    have htwo : IsUnit (2 : ZMod r) := by
      simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
        (Nat.coprime_two_left.mpr hr)
    have hbij : Function.Surjective (fun z : ZMod r ↦ 2 * z) :=
      (Finite.injective_iff_bijective.mp htwo.mul_right_injective).surjective
    obtain ⟨x, hx⟩ := hbij (v - u)
    have hx' : 2 * x = v - u := by simpa using hx
    let y : ZMod r := u + x
    have hyx : y - x = u := by dsimp [y]; ring
    have hyplus : y + x = v := by
      dsimp [y]
      calc
        u + x + x = u + 2 * x := by ring
        _ = u + (v - u) := by rw [hx']
        _ = v := by ring
    have hb := hbinary x y
    rw [hdecomp, hyx, hyplus] at hb
    exact hb
  rcases binary_additive_rectangle_dichotomy f g hsums with hf | hg
  · right
    intro x y
    rw [hdecomp, hdecomp, hf (y - 1 - (x + 1)) (y - x)]
    congr 1
    ring
  · left
    intro x y
    rw [hdecomp, hdecomp, hg (y + 1 + (x + 1)) (y + x)]
    congr 1
    ring

/-- Direct cycle-block form of the binary orientation dichotomy.  An integer
binary matrix intertwining two equal odd cycles is either circulant or
reverse-circulant. -/
theorem binary_oddCycleIntertwiner_orientation
    {r : ℕ} [NeZero r]
    (hr : Odd r)
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1) :
    (∀ x y, B (x + 1) (y + 1) = B x y) ∨
      (∀ x y, B (x + 1) (y - 1) = B x y) := by
  have htwo : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hr)
  obtain ⟨h, hh⟩ := htwo.exists_right_inv
  let F : ZMod r → ZMod r → ℤ := fun u v ↦
    B ((v - u) * h) ((u + v) * h)
  have hrect : ∀ u v,
      F (u + 1) (v - 1) + F (u - 1) (v + 1) =
        F (u + 1) (v + 1) + F (u - 1) (v - 1) := by
    intro u v
    let x : ZMod r := (v - u) * h
    let y : ZMod r := (u + v) * h
    have hx₁ : (v - 1 - (u + 1)) * h = x - 1 := by
      calc
        (v - 1 - (u + 1)) * h = x - 2 * h := by dsimp [x]; ring
        _ = x - 1 := by rw [hh]
    have hx₂ : (v + 1 - (u - 1)) * h = x + 1 := by
      calc
        (v + 1 - (u - 1)) * h = x + 2 * h := by dsimp [x]; ring
        _ = x + 1 := by rw [hh]
    have hy₀a : (u + 1 + (v - 1)) * h = y := by dsimp [y]; ring
    have hy₀b : (u - 1 + (v + 1)) * h = y := by dsimp [y]; ring
    have hx₀a : (v + 1 - (u + 1)) * h = x := by dsimp [x]; ring
    have hx₀b : (v - 1 - (u - 1)) * h = x := by dsimp [x]; ring
    have hy₁ : (u + 1 + (v + 1)) * h = y + 1 := by
      calc
        (u + 1 + (v + 1)) * h = y + 2 * h := by dsimp [y]; ring
        _ = y + 1 := by rw [hh]
    have hy₂ : (u - 1 + (v - 1)) * h = y - 1 := by
      calc
        (u - 1 + (v - 1)) * h = y - 2 * h := by dsimp [y]; ring
        _ = y - 1 := by rw [hh]
    simpa only [F, hx₁, hx₂, hy₀a, hy₀b, hx₀a, hx₀b, hy₁, hy₂] using hinter x y
  obtain ⟨f, g, hfg⟩ := oddZMod_dalembert_decomposition hr F hrect
  have hdecomp : ∀ x y, B x y = f (y - x) + g (y + x) := by
    intro x y
    have hx : (y + x - (y - x)) * h = x := by
      calc
        (y + x - (y - x)) * h = x * (2 * h) := by ring
        _ = x := by rw [hh, mul_one]
    have hy : (y - x + (y + x)) * h = y := by
      calc
        (y - x + (y + x)) * h = y * (2 * h) := by ring
        _ = y := by rw [hh, mul_one]
    have hf := hfg (y - x) (y + x)
    simpa only [F, hx, hy] using hf
  exact binary_dalembertBlock_orientation hr B f g hdecomp hbinary

/-- Graph form: the adjacency block between two parametrized equal odd
components of a commuting two-factor has one of the two global cyclic
orientations. -/
theorem graph_equalOddCycleBlock_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hr : Odd r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u v : ZMod r → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hu : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hv : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)}) :
    (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y + 1)) =
        G.adjMatrix ℤ (u x) (v y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y - 1)) =
        G.adjMatrix ℤ (u x) (v y)) := by
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (v y)
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 x)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y ↦
    hvinj.ne (zmod_sub_one_ne_add_one_of_three_le hr3 y)
  have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D u v
    (1 : ZMod r) (1 : ZMod r) hcomm hu hv hupair hvpair
  have hinterB : ∀ x y,
      B (x - 1) y + B (x + 1) y = B x (y + 1) + B x (y - 1) := by
    simpa only [B] using hinter
  have hbinary : ∀ x y, B x y = 0 ∨ B x y = 1 := by
    intro x y
    simp only [B, SimpleGraph.adjMatrix_apply]
    split <;> simp
  exact binary_oddCycleIntertwiner_orientation hr B hinterB hbinary

/-! ## Normalizing reflected coordinates -/

/-- Reflecting the target coordinate converts a reverse-circulant block to
a circulant block. -/
theorem reverseInvariant_targetReflection_translationInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hrev : ∀ x y, B (x + 1) (y - 1) = B x y) :
    ∀ x y, B (x + 1) (-(y + 1)) = B x (-y) := by
  intro x y
  have h := hrev x (-y)
  have hy : -y - 1 = -(y + 1) := by ring
  rw [hy] at h
  exact h

/-- Reflecting the source coordinate also converts a reverse-circulant block
to a circulant block. -/
theorem reverseInvariant_sourceReflection_translationInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hrev : ∀ x y, B (x + 1) (y - 1) = B x y) :
    ∀ x y, B (-(x + 1)) (y + 1) = B (-x) y := by
  intro x y
  have h := hrev (-(x + 1)) (y + 1)
  have hx : -(x + 1) + 1 = -x := by ring
  have hy : y + 1 - 1 = y := by ring
  rw [hx, hy] at h
  exact h.symm

/-- Reflecting the source coordinate toggles a circulant block to a
reverse-circulant one. -/
theorem translationInvariant_sourceReflection_reverseInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (htrans : ∀ x y, B (x + 1) (y + 1) = B x y) :
    ∀ x y, B (-(x + 1)) (y - 1) = B (-x) y := by
  intro x y
  have h := htrans (-(x + 1)) (y - 1)
  have hx : -(x + 1) + 1 = -x := by ring
  have hy : y - 1 + 1 = y := by ring
  rw [hx, hy] at h
  exact h.symm

/-- Reflecting the target coordinate toggles a circulant block to a
reverse-circulant one. -/
theorem translationInvariant_targetReflection_reverseInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (htrans : ∀ x y, B (x + 1) (y + 1) = B x y) :
    ∀ x y, B (x + 1) (-(y - 1)) = B x (-y) := by
  intro x y
  have h := htrans x (-y)
  have hy : -y + 1 = -(y - 1) := by ring
  rw [hy] at h
  exact h

/-! ## Intersections of the two orientations -/

/-- A simultaneously translation-invariant matrix depends only on the
coordinate difference. -/
theorem translationInvariant_eq_of_sub_eq
    {r : ℕ} [NeZero r] (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y + 1) = B x y)
    {x y x' y' : ZMod r} (hsub : y - x = y' - x') :
    B x y = B x' y' := by
  let t : ZMod r := x' - x
  have hiter : ∀ k : ℕ,
      B (x + (k : ZMod r)) (y + (k : ZMod r)) = B x y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          B (x + ((k + 1 : ℕ) : ZMod r))
              (y + ((k + 1 : ℕ) : ZMod r)) =
              B ((x + (k : ZMod r)) + 1)
                ((y + (k : ZMod r)) + 1) := by
                  congr 1 <;> push_cast <;> ring
          _ = B (x + (k : ZMod r)) (y + (k : ZMod r)) := hB _ _
          _ = B x y := ih
  have ht := hiter t.val
  rw [ZMod.natCast_zmod_val] at ht
  have hx : x + t = x' := by dsimp [t]; ring
  have hy : y + t = y' := by
    dsimp [t]
    rw [sub_eq_sub_iff_add_eq_add] at hsub
    linear_combination hsub
  rw [hx, hy] at ht
  exact ht.symm

/-- A reverse-translation-invariant matrix depends only on the coordinate
sum. -/
theorem reverseTranslationInvariant_eq_of_add_eq
    {r : ℕ} [NeZero r] (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y - 1) = B x y)
    {x y x' y' : ZMod r} (hadd : y + x = y' + x') :
    B x y = B x' y' := by
  let t : ZMod r := x' - x
  have hiter : ∀ k : ℕ,
      B (x + (k : ZMod r)) (y - (k : ZMod r)) = B x y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          B (x + ((k + 1 : ℕ) : ZMod r))
              (y - ((k + 1 : ℕ) : ZMod r)) =
              B ((x + (k : ZMod r)) + 1)
                ((y - (k : ZMod r)) - 1) := by
                  congr 1 <;> push_cast <;> ring
          _ = B (x + (k : ZMod r)) (y - (k : ZMod r)) := hB _ _
          _ = B x y := ih
  have ht := hiter t.val
  rw [ZMod.natCast_zmod_val] at ht
  have hx : x + t = x' := by dsimp [t]; ring
  have hy : y - t = y' := by
    dsimp [t]
    linear_combination hadd
  rw [hx, hy] at ht
  exact ht.symm

/-- A reverse-circulant self-block on an odd cycle is determined by its
diagonal.  In particular, a loopless reverse-circulant block is zero: every
cyclic anti-diagonal meets the diagonal because multiplication by two is a
bijection. -/
theorem oddCycle_reverseTranslationInvariant_zero_of_diagonal_zero
    {r : ℕ} [NeZero r] (hr : Odd r)
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y - 1) = B x y)
    (hdiag : ∀ z, B z z = 0) :
    ∀ x y, B x y = 0 := by
  have htwo : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hr)
  have hsurj : Function.Surjective (fun z : ZMod r ↦ 2 * z) :=
    (Finite.injective_iff_bijective.mp htwo.mul_right_injective).surjective
  intro x y
  obtain ⟨z, hz⟩ := hsurj (y + x)
  have hadd : y + x = z + z := by
    rw [← two_mul]
    exact hz.symm
  exact (reverseTranslationInvariant_eq_of_add_eq B hB hadd).trans (hdiag z)

/-- Arithmetic core of the unique-intermediate obstruction.  If two cyclic
connection sets of sizes `a,b` uniquely factor a group of order `r`, then
`ab=r`.  If both are Sidon, their disjoint nonzero difference sets would
force the displayed inequality, which is impossible once `r≥3`.

The surrounding graph argument supplies this inequality by counting ordered
differences; this lemma isolates the parameter contradiction. -/
theorem no_unique_sidon_factor_degrees
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 3 ≤ r)
    (hprod : a * b = r)
    (hdiff : a * (a - 1) + b * (b - 1) ≤ r - 1) : False := by
  by_cases ha1 : a = 1
  · subst a
    simp only [one_mul] at hprod
    rw [← hprod] at hdiff
    have hb3 : 3 ≤ b := by omega
    have hmul : 2 * (b - 1) ≤ b * (b - 1) :=
      Nat.mul_le_mul_right (b - 1) (by omega)
    have : b - 1 < b * (b - 1) := by omega
    omega
  by_cases hb1 : b = 1
  · subst b
    simp only [mul_one] at hprod
    rw [← hprod] at hdiff
    have ha3 : 3 ≤ a := by omega
    have hmul : 2 * (a - 1) ≤ a * (a - 1) :=
      Nat.mul_le_mul_right (a - 1) (by omega)
    have : a - 1 < a * (a - 1) := by omega
    omega
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 :=
    ⟨a - 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 :=
    ⟨b - 2, by omega⟩
  have hprodZ : ((a' + 2 : ℕ) : ℤ) * (b' + 2) = r := by
    exact_mod_cast hprod
  have hdiffZ : ((a' + 2 : ℕ) : ℤ) * (a' + 1) +
      (b' + 2) * (b' + 1) ≤ (r : ℤ) - 1 := by
    norm_num at hdiff
    have hz : ((a' + 2 : ℕ) : ℤ) * (a' + 1) +
        (b' + 2) * (b' + 1) ≤ ((r - 1 : ℕ) : ℤ) := by
      exact_mod_cast hdiff
    rw [Nat.cast_sub (by omega : 1 ≤ r)] at hz
    exact hz
  push_cast at hprodZ hdiffZ
  nlinarith [sq_nonneg (2 * (a' : ℤ) - (b' : ℤ)),
    sq_nonneg (b' : ℤ)]

/-- On an odd cyclic grid, a nonempty circulant support and a nonempty
reverse-circulant support necessarily meet.  Geometrically, every cyclic
diagonal meets every cyclic anti-diagonal because doubling is invertible. -/
theorem oddCycle_circulant_reverseCirculant_intersect
    {r : ℕ} [NeZero r] (hr : Odd r)
    (P M : Matrix (ZMod r) (ZMod r) ℤ)
    (hP : ∀ x y, P (x + 1) (y + 1) = P x y)
    (hM : ∀ x y, M (x + 1) (y - 1) = M x y)
    (hPone : ∃ x y, P x y = 1)
    (hMone : ∃ x y, M x y = 1) :
    ∃ x y, P x y = 1 ∧ M x y = 1 := by
  obtain ⟨xp, yp, hp⟩ := hPone
  obtain ⟨xm, ym, hm⟩ := hMone
  let a : ZMod r := yp - xp
  let b : ZMod r := ym + xm
  have htwo : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hr)
  have hsurj : Function.Surjective (fun z : ZMod r ↦ 2 * z) :=
    (Finite.injective_iff_bijective.mp htwo.mul_right_injective).surjective
  obtain ⟨x, hx⟩ := hsurj (b - a)
  let y : ZMod r := a + x
  have hdiff : y - x = yp - xp := by dsimp [y, a]; ring
  have hsum : y + x = ym + xm := by
    have hx' : 2 * x = b - a := by simpa using hx
    dsimp [y]
    rw [show a + x + x = a + 2 * x by ring, hx']
    dsimp [b]
    ring
  refine ⟨x, y, ?_, ?_⟩
  · exact (translationInvariant_eq_of_sub_eq P hP hdiff).trans hp
  · exact (reverseTranslationInvariant_eq_of_add_eq M hM hsum).trans hm

/-- Consequently, nonempty blocks of opposite orientations cannot occur as
disjoint summands of a binary matrix.  This is the local mechanism forcing a
single orientation on all two-step contributions to an off-diagonal boundary
block. -/
theorem oddCycle_no_disjoint_opposite_orientations
    {r : ℕ} [NeZero r] (hr : Odd r)
    (P M : Matrix (ZMod r) (ZMod r) ℤ)
    (hP : ∀ x y, P (x + 1) (y + 1) = P x y)
    (hM : ∀ x y, M (x + 1) (y - 1) = M x y)
    (hPone : ∃ x y, P x y = 1)
    (hMone : ∃ x y, M x y = 1)
    (hdisjoint : ∀ x y, P x y + M x y ≤ 1) : False := by
  obtain ⟨x, y, hp, hm⟩ :=
    oddCycle_circulant_reverseCirculant_intersect hr P M hP hM hPone hMone
  have h := hdisjoint x y
  rw [hp, hm] at h
  omega

end Erdos85
