import Proofs.Erdos85PolarityConic
import Proofs.Erdos85ProblemConflict

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

private def nvec (K : Type u) [One K] : Fin 3 → K := ![1, 1, 1]

private theorem nvec_ne_zero (K : Type u) [Field K] : nvec K ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [nvec] at h0

noncomputable def nucleus (K : Type u) [Field K] :
    Projectivization K (Fin 3 → K) :=
  Projectivization.mk K (nvec K) (nvec_ne_zero K)

private theorem self_dot_eq_zero_iff_nvec_dot {K : Type u} [Field K]
    (h2 : (2 : K) = 0) :
    let n : Fin 3 → K := ![1, 1, 1]
    ∀ x : Fin 3 → K, x ⬝ᵥ x = 0 ↔ n ⬝ᵥ x = 0 := by
  dsimp
  intro x
  rw [vec3_dotProduct, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  simp only [one_mul]
  constructor
  · intro hx
    have hsquare : (x 0 + x 1 + x 2) ^ 2 = 0 := by
      calc
        (x 0 + x 1 + x 2) ^ 2 =
            x 0 * x 0 + x 1 * x 1 + x 2 * x 2 +
              2 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) := by ring
        _ = 0 := by rw [h2, hx]; simp
    exact (sq_eq_zero_iff).mp hsquare
  · intro hx
    calc
      x 0 * x 0 + x 1 * x 1 + x 2 * x 2 =
          (x 0 + x 1 + x 2) ^ 2 -
            2 * (x 0 * x 1 + x 0 * x 2 + x 1 * x 2) := by ring
      _ = 0 := by rw [h2, hx]; simp

private theorem nvec_not_iso {K : Type u} [Field K] (h2 : (2 : K) = 0) :
    let n : Fin 3 → K := ![1, 1, 1]
    n ⬝ᵥ n ≠ 0 := by
  dsimp
  rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  simp only [one_mul]
  have hone : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact h2
  rw [hone, zero_add]
  exact one_ne_zero

theorem selfOrthogonal_iff_nucleus_adj {K : Type u} [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) (p : Projectivization K (Fin 3 → K)) :
    Projectivization.orthogonal p p ↔ (graph K).Adj (nucleus K) p := by
  have heq : p.rep ⬝ᵥ p.rep = 0 ↔ nvec K ⬝ᵥ p.rep = 0 := by
    simpa [nvec] using (self_dot_eq_zero_iff_nvec_dot h2 p.rep)
  constructor
  · intro hpp
    have hdot : nvec K ⬝ᵥ p.rep = 0 := heq.mp
      ((Projectivization.orthogonal_mk p.rep_nonzero p.rep_nonzero).mp
        (by simpa using hpp))
    have hne : nucleus K ≠ p := by
      intro he
      have hnself : Projectivization.orthogonal (nucleus K) (nucleus K) := by
        simpa [he] using hpp
      have hnveczero : nvec K ⬝ᵥ nvec K = 0 :=
        (Projectivization.orthogonal_mk (nvec_ne_zero K) (nvec_ne_zero K)).mp
          (by simpa [nucleus] using hnself)
      have hnnonzero : nvec K ⬝ᵥ nvec K ≠ 0 := by
        simpa [nvec] using nvec_not_iso h2
      exact hnnonzero hnveczero
    apply (graph_adj_iff (nucleus K) p).mpr
    refine ⟨hne, ?_⟩
    simpa [nucleus] using
      (Projectivization.orthogonal_mk (nvec_ne_zero K) p.rep_nonzero).mpr hdot
  · intro hadj
    have hdot : nvec K ⬝ᵥ p.rep = 0 :=
      (Projectivization.orthogonal_mk (nvec_ne_zero K) p.rep_nonzero).mp
        (by simpa [nucleus] using ((graph_adj_iff (nucleus K) p).mp hadj).2)
    simpa using
      (Projectivization.orthogonal_mk p.rep_nonzero p.rep_nonzero).mpr
        (heq.mpr hdot)

theorem card_absolutePoints_eq_card_add_one_of_two_eq_zero {K : Type u} [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    (absolutePoints K).card = Nat.card K + 1 := by
  have heq : absolutePoints K = (graph K).neighborFinset (nucleus K) := by
    ext p
    rw [mem_absolutePoints, SimpleGraph.mem_neighborFinset]
    exact selfOrthogonal_iff_nucleus_adj h2 p
  rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
  apply degree_eq_card_add_one_of_not_selfOrthogonal
  intro hn
  have hnveczero : nvec K ⬝ᵥ nvec K = 0 :=
    (Projectivization.orthogonal_mk (nvec_ne_zero K) (nvec_ne_zero K)).mp
      (by simpa [nucleus] using hn)
  have hnnonzero : nvec K ⬝ᵥ nvec K ≠ 0 := by
    simpa [nvec] using nvec_not_iso h2
  exact hnnonzero hnveczero


/-- Over every finite field, the orthogonal polarity has exactly `q + 1`
absolute points.  Odd characteristic gives a nonsingular conic; in
characteristic two the absolute locus is the line polar to the nucleus. -/
theorem card_absolutePoints_eq_card_add_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K] :
    (absolutePoints K).card = Nat.card K + 1 := by
  by_cases h2 : (2 : K) = 0
  · exact card_absolutePoints_eq_card_add_one_of_two_eq_zero (K := K) h2
  · exact card_absolutePoints_eq_card_add_one_of_two_ne_zero K h2

/-- Any two distinct absolute points have a unique common neighbor in the
polarity graph, and that common neighbor is nonabsolute. -/
theorem existsUnique_nonabsolute_commonNeighbor_of_absolute
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    {a b : Projectivization K (Fin 3 → K)}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hab : a ≠ b) :
    ∃! z, (graph K).Adj a z ∧ (graph K).Adj b z ∧
      ¬ Projectivization.orthogonal z z := by
  have habno : ¬ Projectivization.orthogonal a b := by
    intro hortho
    have hadj : (graph K).Adj a b := (graph_adj_iff a b).mpr ⟨hab, hortho⟩
    exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj ha) hb
  obtain ⟨z, hza, hzb⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K))
      a b hab |>.exists
  have hzaOrtho : Projectivization.orthogonal z a :=
    (Configuration.ofField.mem_iff z a).mp hza
  have hzbOrtho : Projectivization.orthogonal z b :=
    (Configuration.ofField.mem_iff z b).mp hzb
  have hzneA : z ≠ a := by
    intro h
    apply habno
    simpa [h] using hzbOrtho
  have hzneB : z ≠ b := by
    intro h
    apply habno
    exact Projectivization.orthogonal_comm.mp (by simpa [h] using hzaOrtho)
  have haz : (graph K).Adj a z := (graph_adj_iff a z).mpr
    ⟨Ne.symm hzneA, Projectivization.orthogonal_comm.mp hzaOrtho⟩
  have hbz : (graph K).Adj b z := (graph_adj_iff b z).mpr
    ⟨Ne.symm hzneB, Projectivization.orthogonal_comm.mp hzbOrtho⟩
  have hznon : ¬ Projectivization.orthogonal z z :=
    not_selfOrthogonal_of_adj_selfOrthogonal haz ha
  refine ⟨z, ⟨haz, hbz, hznon⟩, ?_⟩
  intro w hw
  have hle := Finset.card_le_one.mp (commonNeighbors_le_one a b hab)
  symm
  apply hle z
  · simp [haz, hbz]
  · simp [hw.1, hw.2.1]

/-- Away from the nucleus, every nonabsolute polar line in characteristic two
meets the absolute line in exactly one point. -/
theorem card_neighborFinset_inter_absolute_eq_one_of_even (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0)
    (v : Projectivization K (Fin 3 → K))
    (hvself : ¬ Projectivization.orthogonal v v)
    (hvn : v ≠ nucleus K) :
    ((graph K).neighborFinset v ∩ absolutePoints K).card = 1 := by
  obtain ⟨p, hpv, hpn⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K))
      v (nucleus K) hvn |>.exists
  have hpvOrtho : Projectivization.orthogonal p v :=
    (Configuration.ofField.mem_iff p v).mp hpv
  have hpnOrtho : Projectivization.orthogonal p (nucleus K) :=
    (Configuration.ofField.mem_iff p (nucleus K)).mp hpn
  have hpne_v : p ≠ v := by
    intro heq
    apply hvself
    simpa [heq] using hpvOrtho
  have hpne_n : p ≠ nucleus K := by
    intro heq
    have hnself : Projectivization.orthogonal (nucleus K) (nucleus K) := by
      simpa [heq] using hpnOrtho
    exact (graph K).irrefl
      ((selfOrthogonal_iff_nucleus_adj h2 (nucleus K)).mp hnself)
  have hvp : (graph K).Adj v p :=
    (graph_adj_iff v p).mpr
      ⟨Ne.symm hpne_v, Projectivization.orthogonal_comm.mp hpvOrtho⟩
  have hnp : (graph K).Adj (nucleus K) p :=
    (graph_adj_iff (nucleus K) p).mpr
      ⟨Ne.symm hpne_n, Projectivization.orthogonal_comm.mp hpnOrtho⟩
  have hpabs : p ∈ absolutePoints K :=
    (mem_absolutePoints K p).mpr
      ((selfOrthogonal_iff_nucleus_adj h2 p).mpr hnp)
  have hpos : 0 < ((graph K).neighborFinset v ∩ absolutePoints K).card :=
    Finset.card_pos.mpr ⟨p, by simp [hvp, hpabs]⟩
  have habsEq : absolutePoints K = (graph K).neighborFinset (nucleus K) := by
    ext y
    rw [mem_absolutePoints, SimpleGraph.mem_neighborFinset]
    exact selfOrthogonal_iff_nucleus_adj h2 y
  have hle : ((graph K).neighborFinset v ∩ absolutePoints K).card ≤ 1 := by
    rw [habsEq]
    exact commonNeighbors_le_one v (nucleus K) hvn
  omega

/-- The characteristic-two deletion set: the absolute line together with its
nucleus. -/
noncomputable def evenDeletedSet
    (K : Type u) [Field K] [Finite K] [DecidableEq K] :
    Finset (Projectivization K (Fin 3 → K)) :=
  insert (nucleus K) (absolutePoints K)

/-- The induced polarity graph after deleting the absolute line and nucleus. -/
noncomputable abbrev evenCore
    (K : Type u) [Field K] [Finite K] [DecidableEq K] :=
  deleteVertexSetGraph (graph K) (evenDeletedSet K)

theorem card_neighborFinset_inter_evenDeletedSet_eq_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0)
    (v : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K}) :
    ((graph K).neighborFinset v.1 ∩ evenDeletedSet K).card = 1 := by
  have hvnotabs : v.1 ∉ absolutePoints K := by
    intro hv
    exact v.2 (by simp [evenDeletedSet, hv])
  have hvself : ¬ Projectivization.orthogonal v.1 v.1 := by
    simpa [mem_absolutePoints] using hvnotabs
  have hvn : v.1 ≠ nucleus K := by
    intro heq
    apply v.2
    simp [evenDeletedSet, heq]
  have hnadj : ¬ (graph K).Adj (nucleus K) v.1 := by
    simpa [selfOrthogonal_iff_nucleus_adj h2 v.1] using hvself
  have hinter : (graph K).neighborFinset v.1 ∩ evenDeletedSet K =
      (graph K).neighborFinset v.1 ∩ absolutePoints K := by
    ext y
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      evenDeletedSet, Finset.mem_insert]
    constructor
    · rintro ⟨hvy, rfl | hyabs⟩
      · exact False.elim
          (hnadj (((graph K).adj_comm (nucleus K) v.1).mpr hvy))
      · exact ⟨hvy, hyabs⟩
    · rintro ⟨hvy, hyabs⟩
      exact ⟨hvy, Or.inr hyabs⟩
  rw [hinter]
  exact card_neighborFinset_inter_absolute_eq_one_of_even K h2 v.1 hvself hvn

/-- The characteristic-two core on `q² - 1` vertices is exactly `q`-regular,
not merely of minimum degree at least `q`. -/
theorem evenCore_isRegular
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    (evenCore K).IsRegularOfDegree (Nat.card K) := by
  intro v
  have hvnotabs : v.1 ∉ absolutePoints K := by
    intro hv
    exact v.2 (by simp [evenDeletedSet, hv])
  have hvself : ¬ Projectivization.orthogonal v.1 v.1 := by
    simpa [mem_absolutePoints] using hvnotabs
  have hs := degree_deleteVertexSetGraph_add (graph K) (evenDeletedSet K) v
  rw [card_neighborFinset_inter_evenDeletedSet_eq_one K h2 v,
    degree_eq_card_add_one_of_not_selfOrthogonal hvself] at hs
  have hs' : (evenCore K).degree v + 1 = Nat.card K + 1 := by
    simpa [evenCore] using hs
  omega

/-- In characteristic two, delete the full absolute line and its nucleus.
Every survivor is nonabsolute, is not adjacent to the nucleus, and has at most
one neighbor on the absolute line.  The resulting graph has order `q² - 1`
and minimum degree at least `q`. -/
theorem c4FreeMinDegreeWitness_even_delete_absolute_nucleus (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    C4FreeMinDegreeWitness (Nat.card K * Nat.card K - 1) (Nat.card K) := by
  let E : Finset (Projectivization K (Fin 3 → K)) :=
    insert (nucleus K) (absolutePoints K)
  have hnself : ¬ Projectivization.orthogonal (nucleus K) (nucleus K) := by
    intro hn
    exact (graph K).irrefl
      ((selfOrthogonal_iff_nucleus_adj h2 (nucleus K)).mp hn)
  have hnmem : nucleus K ∉ absolutePoints K := by
    simpa [mem_absolutePoints] using hnself
  have hEcard : E.card = Nat.card K + 2 := by
    rw [Finset.card_insert_of_notMem hnmem,
      card_absolutePoints_eq_card_add_one K]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have hremain : 1 ≤ (Nat.card K + 1) * Nat.card K + 1 - E.card := by
    rw [hEcard]
    apply Nat.le_sub_of_add_le
    nlinarith
  have habsEq : absolutePoints K = (graph K).neighborFinset (nucleus K) := by
    ext p
    rw [mem_absolutePoints, SimpleGraph.mem_neighborFinset]
    exact selfOrthogonal_iff_nucleus_adj h2 p
  have hw : C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - E.card) (Nat.card K) := by
    apply c4FreeMinDegreeWitness_delete_vertex_set_of_compensated_degrees
      (graph K) E
    · rw [Fintype.card_eq_nat_card, card_points_tight K]
    · rfl
    · exact hremain
    · exact graph_not_containsC4
    · intro v
      have hvnotabs : v.1 ∉ absolutePoints K := by
        intro hv
        exact v.2 (by simp [E, hv])
      have hvself : ¬ Projectivization.orthogonal v.1 v.1 := by
        simpa [mem_absolutePoints] using hvnotabs
      have hvn : v.1 ≠ nucleus K := by
        intro heq
        apply v.2
        simp [E, heq]
      have hnadj : ¬ (graph K).Adj (nucleus K) v.1 := by
        simpa [selfOrthogonal_iff_nucleus_adj h2 v.1] using hvself
      have hinter : (graph K).neighborFinset v.1 ∩ E =
          (graph K).neighborFinset v.1 ∩ absolutePoints K := by
        ext y
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          E, Finset.mem_insert]
        constructor
        · rintro ⟨hvy, rfl | hyabs⟩
          · exact False.elim
              (hnadj (((graph K).adj_comm (nucleus K) v.1).mpr hvy))
          · exact ⟨hvy, hyabs⟩
        · rintro ⟨hvy, hyabs⟩
          exact ⟨hvy, Or.inr hyabs⟩
      have hinc : ((graph K).neighborFinset v.1 ∩ E).card ≤ 1 := by
        rw [hinter, habsEq]
        exact commonNeighbors_le_one v.1 (nucleus K) hvn
      rw [degree_eq_card_add_one_of_not_selfOrthogonal hvself]
      change Nat.card K + ((graph K).neighborFinset v.1 ∩ E).card ≤
        Nat.card K + 1
      omega
  have hN : (Nat.card K + 1) * Nat.card K + 1 =
      Nat.card K * Nat.card K + Nat.card K + 1 := by ring
  have horderEq : (Nat.card K + 1) * Nat.card K + 1 - E.card =
      Nat.card K * Nat.card K - 1 := by
    rw [hEcard, hN]
    omega
  rw [horderEq] at hw
  exact hw

/-- The characteristic-two nucleus deletion pins down another exact value:
`f(q² - 1) = q + 1`. -/
theorem minDegreeForC4_even_square_sub_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    minDegreeForC4 (Nat.card K * Nat.card K - 1) = Nat.card K + 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  by_cases hq2 : Nat.card K = 2
  · rw [hq2]
    norm_num
    exact minDegreeForC4_eq_self_of_le_three (by omega) (by omega)
  · have hq3 : 3 ≤ Nat.card K := by omega
    apply Nat.le_antisymm
    · apply minDegreeForC4_le_of_le_mul_pred
      · apply Nat.le_sub_of_add_le
        nlinarith
      · rw [Nat.add_sub_cancel_right]
        exact (Nat.sub_le _ _).trans (by nlinarith)
    · have hw := c4FreeMinDegreeWitness_even_delete_absolute_nucleus K h2
      have horder : 4 ≤ Nat.card K * Nat.card K - 1 := by
        apply Nat.le_sub_of_add_le
        nlinarith
      have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 horder).1 hw
      omega

/-- Characteristic-two polarity graphs therefore supply an infinite family of
verified monotone steps, immediately before the exact `q² - 1` values. -/
theorem minDegreeForC4_even_monotone_before_square_sub_one
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    minDegreeForC4 (Nat.card K * Nat.card K - 2) ≤
      minDegreeForC4 (Nat.card K * Nat.card K - 1) := by
  rw [minDegreeForC4_even_square_sub_one K h2]
  apply minDegreeForC4_le_of_le_mul_pred
  · have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
    apply Nat.le_sub_of_add_le
    nlinarith
  · rw [Nat.add_sub_cancel_right]
    exact (Nat.sub_le _ _).trans (by nlinarith)

/-- A safe pair in the even core determines a deleted absolute common
neighbor in the ambient projective plane. -/

private theorem safe_pair_common_absolute (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0)
    (S : Finset {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K})
    (hsafe : CommonNeighborIndependent (evenCore K) S)
    {x y : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K}}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ p ∈ absolutePoints K, x.1 ∈ p ∧ y.1 ∈ p := by
  have hxyv : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  obtain ⟨p, hpx, hpy⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K))
      x.1 y.1 hxyv |>.exists
  have hxnotabs : x.1 ∉ absolutePoints K := by
    intro h
    exact x.2 (by simp [evenDeletedSet, h])
  have hynotabs : y.1 ∉ absolutePoints K := by
    intro h
    exact y.2 (by simp [evenDeletedSet, h])
  have hxself : ¬ Projectivization.orthogonal x.1 x.1 := by
    simpa [mem_absolutePoints] using hxnotabs
  have hyself : ¬ Projectivization.orthogonal y.1 y.1 := by
    simpa [mem_absolutePoints] using hynotabs
  have hpnex : p ≠ x.1 := by
    intro heq
    apply hxself
    exact (Configuration.ofField.mem_iff x.1 x.1).mp (by simpa [heq] using hpx)
  have hpney : p ≠ y.1 := by
    intro heq
    apply hyself
    exact (Configuration.ofField.mem_iff y.1 y.1).mp (by simpa [heq] using hpy)
  have hxp : (graph K).Adj x.1 p := by
    apply (graph_adj_iff x.1 p).mpr
    refine ⟨Ne.symm hpnex, ?_⟩
    exact Projectivization.orthogonal_comm.mp
      ((Configuration.ofField.mem_iff p x.1).mp hpx)
  have hyp : (graph K).Adj y.1 p := by
    apply (graph_adj_iff y.1 p).mpr
    refine ⟨Ne.symm hpney, ?_⟩
    exact Projectivization.orthogonal_comm.mp
      ((Configuration.ofField.mem_iff p y.1).mp hpy)
  have hpdel : p ∈ evenDeletedSet K := by
    by_contra hp
    let z : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K} := ⟨p, hp⟩
    have hxz : (evenCore K).Adj x z := by
      change (graph K).Adj x.1 p
      exact hxp
    have hyz : (evenCore K).Adj y z := by
      change (graph K).Adj y.1 p
      exact hyp
    have hzmem : z ∈ (evenCore K).neighborFinset x ∩
        (evenCore K).neighborFinset y := by
      rw [Finset.mem_inter]
      constructor <;> simpa only [SimpleGraph.mem_neighborFinset]
    have hzero := hsafe hx hy hxy
    rw [Finset.card_eq_zero] at hzero
    exact Finset.notMem_empty z (hzero ▸ hzmem)
  have hpneN : p ≠ nucleus K := by
    intro heq
    have hnx : (graph K).Adj (nucleus K) x.1 := by simpa [heq] using hxp.symm
    have hxself' := (selfOrthogonal_iff_nucleus_adj h2 x.1).mpr hnx
    exact hxself hxself'
  have hpabs : p ∈ absolutePoints K := by
    simpa [evenDeletedSet, hpneN] using hpdel
  have hxpMem : x.1 ∈ p := (Configuration.ofField.mem_iff x.1 p).mpr
    (Projectivization.orthogonal_comm.mp
      ((Configuration.ofField.mem_iff p x.1).mp hpx))
  have hypMem : y.1 ∈ p := (Configuration.ofField.mem_iff y.1 p).mpr
    (Projectivization.orthogonal_comm.mp
      ((Configuration.ofField.mem_iff p y.1).mp hpy))
  exact ⟨p, hpabs, hxpMem, hypMem⟩

/-- A safe one-vertex attachment set in the even polarity core has at most
`q - 1` vertices.  Geometrically, any two of its points determine a deleted
absolute common neighbor, forcing the whole set onto one polar line through
the nucleus.  Thus the natural `q`-regular core cannot be extended at degree
`q` by the standard common-neighbor-independent attachment. -/
theorem card_commonNeighborIndependent_evenCore_le (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0)
    (S : Finset {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K})
    (hsafe : CommonNeighborIndependent (evenCore K) S) :
    S.card ≤ Nat.card K - 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  by_contra hbound
  have hqS : Nat.card K ≤ S.card := by omega
  have htwo : 1 < S.card := lt_of_lt_of_le (by omega) hqS
  rw [Finset.one_lt_card] at htwo
  obtain ⟨x, hx, y, hy, hxy⟩ := htwo
  obtain ⟨p₀, hp₀abs, hxp₀, hyp₀⟩ :=
    safe_pair_common_absolute K h2 S hsafe hx hy hxy
  have hxneN : x.1 ≠ nucleus K := by
    intro heq
    exact x.2 (by simp [evenDeletedSet, heq])
  have hnmem₀ : nucleus K ∈ p₀ := by
    apply (Configuration.ofField.mem_iff (nucleus K) p₀).mpr
    have hnp₀ : (graph K).Adj (nucleus K) p₀ :=
      (selfOrthogonal_iff_nucleus_adj h2 p₀).mp
        ((mem_absolutePoints K p₀).mp hp₀abs)
    exact ((graph_adj_iff (nucleus K) p₀).mp hnp₀).2
  have hall : ∀ z ∈ S, z.1 ∈ p₀ := by
    intro z hz
    by_cases hzx : z = x
    · simpa [hzx] using hxp₀
    · obtain ⟨p, hpabs, hxp, hzp⟩ :=
        safe_pair_common_absolute K h2 S hsafe hx hz (Ne.symm hzx)
      have hnmem : nucleus K ∈ p := by
        apply (Configuration.ofField.mem_iff (nucleus K) p).mpr
        have hnp : (graph K).Adj (nucleus K) p :=
          (selfOrthogonal_iff_nucleus_adj h2 p).mp
            ((mem_absolutePoints K p).mp hpabs)
        exact ((graph_adj_iff (nucleus K) p).mp hnp).2
      have hlines : p₀ = p :=
        (Configuration.Nondegenerate.eq_or_eq hxp₀ hnmem₀ hxp hnmem).resolve_left
          hxneN
      simpa [hlines] using hzp
  let emb : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K} ↪
      Projectivization K (Fin 3 → K) := Function.Embedding.subtype _
  let T := S.map emb
  have hsub : T ⊆ (graph K).neighborFinset p₀ \ {nucleus K} := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨z, hzS, rfl⟩ := hz
    have hznotabs : z.1 ∉ absolutePoints K := by
      intro ha
      exact z.2 (by simp [evenDeletedSet, ha])
    have hpne : p₀ ≠ z.1 := by
      intro heq
      exact hznotabs (by simpa [← heq] using hp₀abs)
    have hadj : (graph K).Adj p₀ z.1 := by
      apply (graph_adj_iff p₀ z.1).mpr
      refine ⟨hpne, ?_⟩
      exact Projectivization.orthogonal_comm.mp
        ((Configuration.ofField.mem_iff z.1 p₀).mp (hall z hzS))
    have hzne : z.1 ≠ nucleus K := by
      intro heq
      exact z.2 (by simp [evenDeletedSet, heq])
    simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
      Finset.mem_singleton]
    dsimp [emb]
    exact ⟨hadj, hzne⟩
  have hnAdj : (graph K).Adj p₀ (nucleus K) := by
    exact ((graph K).adj_comm (nucleus K) p₀).mp
      ((selfOrthogonal_iff_nucleus_adj h2 p₀).mp
        ((mem_absolutePoints K p₀).mp hp₀abs))
  have htarget : ((graph K).neighborFinset p₀ \ {nucleus K}).card =
      Nat.card K - 1 := by
    have hnmem : nucleus K ∈ (graph K).neighborFinset p₀ := by
      simpa only [SimpleGraph.mem_neighborFinset] using hnAdj
    rw [Finset.card_sdiff]
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      degree_eq_card_of_selfOrthogonal
        ((mem_absolutePoints K p₀).mp hp₀abs)]
    simp [hnmem]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, htarget] at hcard
  omega

/-- The `q - 1` upper bound is sharp: the surviving points on the polar line
of any absolute point form a safe attachment set of cardinality `q - 1`. -/
theorem exists_commonNeighborIndependent_evenCore_card_eq (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    ∃ S : Finset {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K},
      CommonNeighborIndependent (evenCore K) S ∧ S.card = Nat.card K - 1 := by
  obtain ⟨p, hp⟩ := exists_selfOrthogonal K
  have hpabs : p ∈ absolutePoints K := (mem_absolutePoints K p).mpr hp
  let T : Finset (Projectivization K (Fin 3 → K)) :=
    (graph K).neighborFinset p \ {nucleus K}
  let S : Finset {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K} :=
    Finset.univ.filter fun v => v.1 ∈ T
  have hnAdj : (graph K).Adj p (nucleus K) :=
    ((graph K).adj_comm (nucleus K) p).mp
      ((selfOrthogonal_iff_nucleus_adj h2 p).mp hp)
  have hTcard : T.card = Nat.card K - 1 := by
    have hnmem : nucleus K ∈ (graph K).neighborFinset p := by
      simpa only [SimpleGraph.mem_neighborFinset] using hnAdj
    rw [Finset.card_sdiff, SimpleGraph.card_neighborFinset_eq_degree,
      degree_eq_card_of_selfOrthogonal hp]
    simp [hnmem]
  let emb : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K} ↪
      Projectivization K (Fin 3 → K) := Function.Embedding.subtype _
  have hmap : S.map emb = T := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      dsimp [emb]
      simpa [S] using hv
    · intro hz
      have hzAdj : (graph K).Adj p z := by
        simpa only [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_sdiff.mp hz).1
      have hzNeN : z ≠ nucleus K := by
        simpa using (Finset.mem_sdiff.mp hz).2
      have hznotabs : z ∉ absolutePoints K := by
        intro hzabs
        exact (not_selfOrthogonal_of_adj_selfOrthogonal hzAdj hp)
          ((mem_absolutePoints K z).mp hzabs)
      have hzcore : z ∉ evenDeletedSet K := by
        simp [evenDeletedSet, hzNeN, hznotabs]
      let v : {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K} :=
        ⟨z, hzcore⟩
      rw [Finset.mem_map]
      refine ⟨v, ?_, rfl⟩
      simp [S, v, hz]
  refine ⟨S, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter] at hz
    have hpx : (graph K).Adj p x.1 := by
      have hxT : x.1 ∈ T := by simpa [S] using hx
      simpa only [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hxT).1
    have hpy : (graph K).Adj p y.1 := by
      have hyT : y.1 ∈ T := by simpa [S] using hy
      simpa only [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hyT).1
    have hxz : (graph K).Adj x.1 z.1 := by
      have hxzCore : (evenCore K).Adj x z := by
        simpa only [SimpleGraph.mem_neighborFinset] using hz.1
      change (graph K).Adj x.1 z.1 at hxzCore
      exact hxzCore
    have hyz : (graph K).Adj y.1 z.1 := by
      have hyzCore : (evenCore K).Adj y z := by
        simpa only [SimpleGraph.mem_neighborFinset] using hz.2
      change (graph K).Adj y.1 z.1 at hyzCore
      exact hyzCore
    have hxyv : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hone := Finset.card_le_one.mp (commonNeighbors_le_one x.1 y.1 hxyv)
    have hpMem : p ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset y.1 := by simp [hpx.symm, hpy.symm]
    have hzMem : z.1 ∈ (graph K).neighborFinset x.1 ∩
        (graph K).neighborFinset y.1 := by simp [hxz, hyz]
    have hpz : p = z.1 := hone p hpMem z.1 hzMem
    apply z.2
    rw [← hpz]
    simp [evenDeletedSet, hpabs]
  · have hc : S.card = T.card := by
      rw [← hmap]
      exact (Finset.card_map emb).symm
    rw [hc, hTcard]

/-- Exact obstruction invariant: the common-neighbor conflict graph of the
even core has independence number precisely `q - 1`. -/
theorem commonNeighborConflict_evenCore_indepNum
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    (commonNeighborConflict (evenCore K)).indepNum = Nat.card K - 1 := by
  apply Nat.le_antisymm
  · obtain ⟨S, hsafe, hcard⟩ :=
      exists_commonNeighborIndependent_card_eq_indepNum (evenCore K)
    rw [← hcard]
    exact card_commonNeighborIndependent_evenCore_le K h2 S hsafe
  · obtain ⟨S, hsafe, hcard⟩ :=
      exists_commonNeighborIndependent_evenCore_card_eq K h2
    have hind : (commonNeighborConflict (evenCore K)).IsIndepSet S :=
      (commonNeighborIndependent_iff_isIndepSet (evenCore K) S).mp hsafe
    rw [← hcard]
    exact hind.card_le_indepNum

/-- Direct failure of the conflict-independence sufficient criterion at
degree `q` for the even core. -/
theorem not_card_le_commonNeighborConflict_evenCore_indepNum
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    ¬ Nat.card K ≤ (commonNeighborConflict (evenCore K)).indepNum := by
  rw [commonNeighborConflict_evenCore_indepNum K h2]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  omega

/-- Equivalently, no safe old-neighbor set can give one attached vertex
degree `q` over the even core. -/
theorem not_exists_commonNeighborIndependent_evenCore_card_ge
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) = 0) :
    ¬ ∃ S : Finset
        {v : Projectivization K (Fin 3 → K) // v ∉ evenDeletedSet K},
      Nat.card K ≤ S.card ∧ CommonNeighborIndependent (evenCore K) S := by
  rintro ⟨S, hcard, hsafe⟩
  have hle := card_commonNeighborIndependent_evenCore_le K h2 S hsafe
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  omega





end Erdos85.Polarity
