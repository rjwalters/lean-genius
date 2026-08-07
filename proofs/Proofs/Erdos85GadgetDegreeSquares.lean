import Proofs.Erdos85GadgetMultiplicity

/-!
# Degree-square bounds for compatible gadget graphs

The gadget graph in every compatible attachment is itself `C₄`-free.
Cherry counting therefore bounds its whole degree-square sum and strengthens
the required gadget size from square-root scale to linear scale near the
Moore-layer order.
-/

open SimpleGraph

namespace Erdos85

/-- Elementary form of the choose-two identity. -/
theorem two_mul_choose_two_add_self (n : ℕ) :
    2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose]
    simp only [Nat.choose_one_right]
    nlinarith

/-- Twice `choose(n,2)` is `n(n-1)`. -/
theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
    have h := two_mul_choose_two_add_self (n + 1)
    simp only [Nat.add_sub_cancel] at h ⊢
    nlinarith

/-- Contrapositive cherry bound for a `C₄`-free graph. -/
theorem sum_degree_choose_two_le_card_choose_two_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) :
    (∑ v : V, (G.degree v).choose 2) ≤ (Fintype.card V).choose 2 := by
  by_contra hnot
  exact hfree (containsC4_of_card_choose_two_lt G (Nat.lt_of_not_ge hnot))

/-- Every simple graph has total degree at most `m(m-1)`. -/
theorem sum_degrees_le_card_mul_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, G.degree v) ≤ Fintype.card V * (Fintype.card V - 1) := by
  calc
    (∑ v : V, G.degree v) ≤
        ∑ _v : V, (Fintype.card V - 1) := by
      apply Finset.sum_le_sum
      intro v _
      have := G.degree_lt_card_verts v
      omega
    _ = Fintype.card V * (Fintype.card V - 1) := by
      simp

/-- A `C₄`-free graph on `m` vertices satisfies
`Σ_v deg(v)² ≤ 2m(m-1)`. -/
theorem sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) :
    (∑ v : V, G.degree v * G.degree v) ≤
      2 * (Fintype.card V * (Fintype.card V - 1)) := by
  have hcherry :=
    sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hdegree := sum_degrees_le_card_mul_pred G
  have hid : (∑ v : V, G.degree v * G.degree v) =
      2 * (∑ v : V, (G.degree v).choose 2) + ∑ v : V, G.degree v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact (two_mul_choose_two_add_self (G.degree v)).symm
  rw [hid]
  have hchoose := two_mul_choose_two (Fintype.card V)
  nlinarith

/-- Cauchy--Schwarz for the degree sequence, in natural-number form. -/
theorem sum_degrees_sq_le_card_mul_sum_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, G.degree v) * (∑ v : V, G.degree v) ≤
      Fintype.card V * ∑ v : V, G.degree v * G.degree v := by
  have hz := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset V)) (f := fun v => (G.degree v : ℤ))
  norm_num [pow_two] at hz ⊢
  exact_mod_cast hz

/-- **Linear gadget-size obstruction.**  Compatibility makes `F` `C₄`-free,
so its degree-square correction is only `2m(m-1)`.  If `m-1 ≤ d`, then
`d² ≤ |V| + 2(m-1)`. -/
theorem degree_sq_le_card_add_two_mul_card_pred_of_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    d * d ≤ Fintype.card V + 2 * (Fintype.card W - 1) := by
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_of_gadgetCompatible
      G F A hmin hnew hcompat
  have hsq := sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    F (hcompat.gadget_not_containsC4 G F A)
  have hidentity :
      (∑ w : W, (d - F.degree w) * (d + F.degree w)) +
          ∑ w : W, F.degree w * F.degree w =
        Fintype.card W * (d * d) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : W, ((d - F.degree w) * (d + F.degree w) +
          F.degree w * F.degree w)) = ∑ _w : W, d * d := by
        apply Finset.sum_congr rfl
        intro w _
        have hr : F.degree w ≤ d := by
          have hrlt := F.degree_lt_card_verts w
          omega
        have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
        nlinarith
      _ = Fintype.card W * (d * d) := by simp
  have hmul : Fintype.card W * (d * d) ≤
      Fintype.card V * Fintype.card W +
        2 * (Fintype.card W * (Fintype.card W - 1)) := by
    rw [← hidentity]
    exact Nat.add_le_add hsum hsq
  have hfactor : Fintype.card V * Fintype.card W +
      2 * (Fintype.card W * (Fintype.card W - 1)) =
      Fintype.card W * (Fintype.card V + 2 * (Fintype.card W - 1)) := by ring
  rw [hfactor] at hmul
  have hmul' : (d * d) * Fintype.card W ≤
      (Fintype.card V + 2 * (Fintype.card W - 1)) * Fintype.card W := by
    simpa [Nat.mul_comm] using hmul
  exact Nat.le_of_mul_le_mul_right hmul' hW

/-- At Moore-layer order `d(d-1)+1`, every pure compatible gadget has linear
size: `d-1 ≤ 2(m-1)`. -/
theorem degree_pred_le_two_mul_card_pred_of_mooreOrder_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ} (hd : 1 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    d - 1 ≤ 2 * (Fintype.card W - 1) := by
  have hbound := degree_sq_le_card_add_two_mul_card_pred_of_gadgetCompatible
    G F A hW hsize hmin hnew hcompat
  rw [hcard] at hbound
  have hsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  nlinarith

/-- **Near-full linear obstruction.**  At Moore-layer order, Cauchy--Schwarz
and cherry counting sharpen the linear bound to
`(d-m)² ≤ 2(m-1)`.  Hence a pure compatible gadget must have
`m = d - O(√d)`. -/
theorem degree_sub_card_sq_le_two_mul_card_pred_of_mooreOrder_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ} (hd : 1 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    (d - Fintype.card W) * (d - Fintype.card W) ≤
      2 * (Fintype.card W - 1) := by
  let m := Fintype.card W
  let D := ∑ w : W, F.degree w
  let S := ∑ w : W, F.degree w * F.degree w
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_of_gadgetCompatible
      G F A hmin hnew hcompat
  have hidentity :
      (∑ w : W, (d - F.degree w) * (d + F.degree w)) + S =
        m * (d * d) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : W, ((d - F.degree w) * (d + F.degree w) +
          F.degree w * F.degree w)) = ∑ _w : W, d * d := by
        apply Finset.sum_congr rfl
        intro w _
        have hr : F.degree w ≤ d := by
          have hrlt := F.degree_lt_card_verts w
          omega
        have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
        nlinarith
      _ = m * (d * d) := by simp [m]
  have htotal : m * (d * d) ≤ Fintype.card V * m + S := by
    rw [← hidentity]
    exact Nat.add_le_add_right hsum S
  have hcherry :=
    sum_degree_choose_two_le_card_choose_two_of_not_containsC4
      F (hcompat.gadget_not_containsC4 G F A)
  have hsExact : S = 2 * (∑ w : W, (F.degree w).choose 2) + D := by
    dsimp [S, D]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    exact (two_mul_choose_two_add_self (F.degree w)).symm
  have hsUpper : S ≤ m * (m - 1) + D := by
    rw [hsExact]
    have hmchoose := two_mul_choose_two m
    change (∑ w : W, (F.degree w).choose 2) ≤ m.choose 2 at hcherry
    nlinarith
  have hDlower : m * (d - m) ≤ D := by
    rw [hcard] at htotal
    by_cases hmd : m ≤ d
    · have hsubdm : d - m + m = d := Nat.sub_add_cancel hmd
      have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
      have hmone : 1 ≤ m := hW
      have hmsub : m - 1 + 1 = m := Nat.sub_add_cancel hmone
      have hdinner : d * d = (d * (d - 1) + 1) + (d - 1) := by
        nlinarith
      have heq1 : m * (d * d) =
          (d * (d - 1) + 1) * m + m * (d - 1) := by
        rw [hdinner, Nat.mul_add, Nat.mul_comm m (d * (d - 1) + 1)]
      have htail : m * (d - 1) ≤ S := by
        rw [heq1] at htotal
        omega
      have hinner : d - 1 = (m - 1) + (d - m) := by omega
      have heq2 : m * (d - 1) = m * (m - 1) + m * (d - m) := by
        rw [hinner, Nat.mul_add]
      omega
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hmd)]
  have hCS := sum_degrees_sq_le_card_mul_sum_degree_sq F
  change D * D ≤ m * S at hCS
  have hsCoarse := sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    F (hcompat.gadget_not_containsC4 G F A)
  change S ≤ 2 * (m * (m - 1)) at hsCoarse
  have hcombined : (m * (d - m)) * (m * (d - m)) ≤
      m * (2 * (m * (m - 1))) := by
    exact (Nat.mul_le_mul hDlower hDlower).trans (hCS.trans (Nat.mul_le_mul_left m hsCoarse))
  have hfactor : (m * m) * ((d - m) * (d - m)) ≤
      (m * m) * (2 * (m - 1)) := by
    nlinarith
  have hmm : 0 < m * m := Nat.mul_pos hW hW
  exact Nat.le_of_mul_le_mul_left hfactor hmm

/-- Loss-corrected linear obstruction.  Even after old-edge deletion, the
gadget's `C₄`-free degree-square contribution is at most `2m(m-1)`; all
remaining deficit must be paid by attachment-weighted degree loss. -/
theorem card_mul_degree_sq_le_card_mul_card_add_two_card_mul_pred_add_weightedLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ H.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    Fintype.card W * (d * d) ≤
      Fintype.card V * Fintype.card W +
        2 * (Fintype.card W * (Fintype.card W - 1)) +
          ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a := by
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_add_weightedLoss
      H K hKH F A hmin hnew hcompat
  have hsq := sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    F (hcompat.gadget_not_containsC4 K F A)
  have hidentity :
      (∑ w : W, (d - F.degree w) * (d + F.degree w)) +
          ∑ w : W, F.degree w * F.degree w =
        Fintype.card W * (d * d) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : W, ((d - F.degree w) * (d + F.degree w) +
          F.degree w * F.degree w)) = ∑ _w : W, d * d := by
        apply Finset.sum_congr rfl
        intro w _
        have hr : F.degree w ≤ d := by
          have hrlt := F.degree_lt_card_verts w
          omega
        have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
        nlinarith
      _ = Fintype.card W * (d * d) := by simp
  rw [← hidentity]
  omega

/-- At Moore-layer order, a compensated `m`-vertex gadget below the linear
threshold must pay
`m(d-1-2(m-1))` in attachment-weighted old-edge loss. -/
theorem card_mul_degree_pred_sub_two_card_pred_le_weightedLoss_of_mooreOrder
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ} (hd : 1 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hsize : Fintype.card W - 1 ≤ d)
    (hlinear : 2 * (Fintype.card W - 1) ≤ d - 1)
    (hmin : d ≤ H.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    Fintype.card W * (d - 1 - 2 * (Fintype.card W - 1)) ≤
      ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a := by
  let m := Fintype.card W
  let s := m - 1
  let t := d - 1 - 2 * s
  let L := ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a
  have hbound :=
    card_mul_degree_sq_le_card_mul_card_add_two_card_mul_pred_add_weightedLoss
      H K hKH F A hsize hmin hnew hcompat
  change m * (d * d) ≤ Fintype.card V * m + 2 * (m * s) + L at hbound
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have htsub : t + 2 * s = d - 1 := by
    dsimp [t]
    exact Nat.sub_add_cancel hlinear
  have hinner : d * d = (d * (d - 1) + 1) + 2 * s + t := by
    nlinarith
  have heq : m * (d * d) = Fintype.card V * m + 2 * (m * s) + m * t := by
    rw [hinner, Nat.mul_add, Nat.mul_add, hcard]
    ring
  rw [heq] at hbound
  change m * t ≤ L
  omega

end Erdos85
