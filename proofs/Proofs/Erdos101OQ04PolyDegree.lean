import Proofs.Erdos101OQ04

/-!
# Erdős #101 OQ-04 — the exact collinearity bound for a polynomial graph (companion)

The mother module `Proofs.Erdos101OQ04` proves `noFiveCollinear_of_onPolyGraph`: a point set
lying on the graph `y = Poly.eval x` of a polynomial with `2 ≤ deg Poly ≤ 4` has no five
collinear points.  That lemma is capped twice — at the fixed count *five* and at degree *four*
— which are artefacts of the specific quartic construction `y = x⁴ − 5x²`, not of the geometry.

This companion removes both caps.  The underlying fact is the **exact** one:

> a non-vertical line meets the graph `y = Poly.eval x` where the polynomial
> `q = C(Δx)·Poly − C(Δy)·X − C(const)` vanishes, and (since `deg Poly ≥ 2` keeps the linear
> correction from touching the top term) `deg q = deg Poly`, so the line carries **at most
> `deg Poly`** graph points.

Hence *any* collinear subset of a degree-`d` polynomial-graph point set has cardinality `≤ d`
— for every `d ≥ 2`, with no ceiling.  The `noFiveCollinear` result is exactly the `d ≤ 4`
reading (`d ≤ 4 < 5`); a quintic graph is no-six-collinear, a degree-`d` graph is
no-`(d+1)`-collinear, etc.  This is the honest structural content behind the quartic
construction, in the form that scales with the degree — directly relevant to the
higher-degree / higher-dimensional line-count question of Erdős #101.

Self-contained beyond the mother module (`onPolyGraph`, `onPolyGraph_fst_ne`, `collinear`,
`PlanarPointSet`, `NoFiveCollinear` are reused as-is).  Axiom-free (no `decide`, no new axiom).
-/

namespace Erdos101OQ04

open Classical

/-- **Exact collinearity bound for a polynomial graph.**  Let `Poly` have `deg Poly ≥ 2`, let
`a, b` span a non-vertical line (`a.1 ≠ b.1`), and let `S` be a finite set of points that all
lie on the graph `y = Poly.eval x` and are all collinear with `a, b`.  Then `S.card ≤ deg Poly`.

The line `a–b` meets the graph exactly at the roots of
`q = C(b.1−a.1)·Poly − C(b.2−a.2)·X − C((b.1−a.1)·a.2 − (b.2−a.2)·a.1)`, whose degree equals
`deg Poly` (the `deg ≥ 2` hypothesis keeps the degree-`≤1` correction from cancelling the top
coefficient `(b.1−a.1)·leadingCoeff ≠ 0`).  Mapping `S` into `q.roots` by first coordinate is
injective (distinct graph points have distinct abscissae), so `S.card ≤ #q.roots ≤ deg q =
deg Poly`. -/
theorem card_collinear_on_polyGraph_le (Poly : Polynomial ℝ) (hd : 2 ≤ Poly.natDegree)
    {a b : ℝ × ℝ} (hab : a.1 ≠ b.1) {S : Finset (ℝ × ℝ)}
    (hSg : ∀ p ∈ S, onPolyGraph Poly p) (hScol : ∀ p ∈ S, collinear a b p) :
    S.card ≤ Poly.natDegree := by
  have hA0 : b.1 - a.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set q : Polynomial ℝ :=
      Polynomial.C (b.1 - a.1) * Poly
        - Polynomial.C (b.2 - a.2) * Polynomial.X
        - Polynomial.C ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) with hq
  -- `deg q ≤ deg Poly`: the `C·Poly` term dominates; the correction has degree `≤ 1 ≤ deg Poly`.
  have hqdeg : q.natDegree ≤ Poly.natDegree := by
    rw [hq]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_C_mul_le _ _
      · calc (Polynomial.C (b.2 - a.2) * Polynomial.X).natDegree
              ≤ (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_C_mul_le _ _
            _ = 1 := Polynomial.natDegree_X
            _ ≤ Poly.natDegree := by omega
    · rw [Polynomial.natDegree_C]; omega
  -- `q ≠ 0`: its coefficient at index `deg Poly (≥ 2)` is `(b.1−a.1)·leadingCoeff ≠ 0`.
  have hpne : Poly ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hd; omega
  have hlead : Poly.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hne1 : ¬ (1 : ℕ) = Poly.natDegree := by omega
  have hne0 : ¬ Poly.natDegree = 0 := by omega
  have hcoeff : q.coeff Poly.natDegree = (b.1 - a.1) * Poly.leadingCoeff := by
    rw [hq]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, if_neg hne1, if_neg hne0, mul_zero, sub_zero]
    rw [Polynomial.leadingCoeff]
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact (mul_ne_zero hA0 hlead) hcoeff.symm
  have hqeval : ∀ x : ℝ, q.eval x
      = (b.1 - a.1) * Poly.eval x - (b.2 - a.2) * x
        - ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) := by
    intro x
    simp only [hq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  -- Every graph point collinear with `a, b` has its abscissa a root of `q`.
  have hisroot : ∀ p : ℝ × ℝ, onPolyGraph Poly p → collinear a b p → p.1 ∈ q.roots := by
    intro p hpg hcol
    rw [Polynomial.mem_roots hq0]
    show q.eval p.1 = 0
    rw [hqeval]
    have hcol' : (b.1 - a.1) * (p.2 - a.2) = (p.1 - a.1) * (b.2 - a.2) := hcol
    rw [hpg] at hcol'
    linear_combination hcol'
  -- The first-coordinate map is injective on `S` (a graph is a function of `x`).
  have hinj : Set.InjOn (fun p : ℝ × ℝ => p.1) S := by
    intro p hp p' hp' he
    by_contra hne
    exact onPolyGraph_fst_ne (hSg p hp) (hSg p' hp') hne he
  have hsub : S.image (fun p : ℝ × ℝ => p.1) ⊆ q.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [Multiset.mem_toFinset]
    exact hisroot p (hSg p hp) (hScol p hp)
  calc S.card = (S.image (fun p : ℝ × ℝ => p.1)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ Poly.natDegree := hqdeg

/-- **No `(d+1)` collinear on a degree-`d` graph** (the general count generalising
`noFiveCollinear_of_onPolyGraph`).  If a set of `k` distinct points all lie on the graph
`y = Poly.eval x` (`deg Poly ≥ 2`) and are mutually collinear along the non-vertical line
`a–b`, then `k ≤ deg Poly`.  Stated with the points supplied as a `Finset` this is exactly
`card_collinear_on_polyGraph_le`; the point of the name is that a **quartic** graph is
no-five-collinear, a **quintic** graph is no-six-collinear, and generally a degree-`d` graph
carries no `d+1` collinear points. -/
theorem not_succ_natDegree_collinear_on_polyGraph (Poly : Polynomial ℝ) (hd : 2 ≤ Poly.natDegree)
    {a b : ℝ × ℝ} (hab : a.1 ≠ b.1) {S : Finset (ℝ × ℝ)}
    (hSg : ∀ p ∈ S, onPolyGraph Poly p) (hScol : ∀ p ∈ S, collinear a b p)
    (hcard : Poly.natDegree < S.card) : False :=
  absurd (card_collinear_on_polyGraph_le Poly hd hab hSg hScol) (by omega)

/-- **`noFiveCollinear_of_onPolyGraph` as a corollary of the exact bound.**  For `2 ≤ deg ≤ 4`,
five collinear points would form a 5-element collinear subset, but the exact bound caps such a
subset at `deg ≤ 4 < 5`.  This re-derives the mother module's headline from the degree-general
`card_collinear_on_polyGraph_le`, confirming the two are the same fact read at `d ≤ 4`. -/
theorem noFiveCollinear_of_onPolyGraph_via_card (Poly : Polynomial ℝ)
    (h2 : 2 ≤ Poly.natDegree) (h4 : Poly.natDegree ≤ 4)
    (P : PlanarPointSet) (hP : ∀ p ∈ P.points, onPolyGraph Poly p) :
    NoFiveCollinear P := by
  intro a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  rintro ⟨hcol_c, hcol_d, hcol_e⟩
  have hab1 : a.1 ≠ b.1 := onPolyGraph_fst_ne (hP a ha) (hP b hb) hab
  have hSg : ∀ p ∈ ({a, b, c, d, e} : Finset (ℝ × ℝ)), onPolyGraph Poly p := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h | h | h | h <;> rw [h]
    exacts [hP a ha, hP b hb, hP c hc, hP d hd, hP e he]
  have hScol : ∀ p ∈ ({a, b, c, d, e} : Finset (ℝ × ℝ)), collinear a b p := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h | h | h | h <;> rw [h]
    · unfold collinear; ring
    · unfold collinear; ring
    · exact hcol_c
    · exact hcol_d
    · exact hcol_e
  have hcard : ({a, b, c, d, e} : Finset (ℝ × ℝ)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
        Finset.card_insert_of_notMem (by simp [hcd, hce]),
        Finset.card_insert_of_notMem (by simp [hde]),
        Finset.card_singleton]
  exact not_succ_natDegree_collinear_on_polyGraph Poly h2 hab1 hSg hScol (by omega)

end Erdos101OQ04
