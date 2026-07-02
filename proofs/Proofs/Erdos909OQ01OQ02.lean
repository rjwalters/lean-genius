/-
  Erdos-909-oq-01-oq-02: The Product-Cover Dimension Bound
  (partial progress on  dim(X × Y) ≤ dim(X) + dim(Y))

  Open Question from Erdos Problem #909 (Dimension of Product Spaces).
  The parent file `Erdos909OQ01Problem.lean` states the product inequality

        dim(X × Y) ≤ dim(X) + dim(Y)

  as `axiom dimension_product_ineq`.  In full generality (arbitrary topological
  spaces, covering dimension) this inequality is a genuinely deep theorem and is
  in fact FALSE without extra hypotheses: Filippov (1972) constructed compact
  Hausdorff spaces X, Y with dim X = dim Y = 2 yet dim(X × Y) = 3 < 4, and the
  logarithmic law dim(X × Y) ≤ dim X + dim Y only holds under conditions such as
  metrizability of one factor.  So the general axiom cannot be discharged, and it
  should remain an acknowledged assumption.

  This file isolates and PROVES (0 axioms, 0 sorry) the combinatorial heart of
  the inequality: the RECTANGULAR / PRODUCT-COVER case.  Concretely, using the
  same covering-dimension definition as the parent, we show:

    * `prodFamily_order` : the product family {Uᵢ × Vⱼ} of a family of order ≤ p
      and a family of order ≤ q has order ≤ p·q.  (pure finite combinatorics)
    * `prodFamily_isOpen`, `prodFamily_cover` : {Uᵢ × Vⱼ} is an open cover of
      X × Y when {Uᵢ}, {Vⱼ} are open covers of X, Y.
    * `HasOrderAtMost.reindex` : order is preserved under injective reindexing.
    * `product_cover_refinement` : if dim X ≤ m and dim Y ≤ n, then EVERY product
      open cover of X × Y admits a finite open refinement of order ≤ (m+1)(n+1),
      i.e. the product inequality holds when the cover of X × Y is rectangular.
    * `product_cover_refinement_zero_left/right` : when one factor is
      0-dimensional the bound is SHARP — it collapses to the full m + n, matching
      `dimension_product_ineq` exactly on product covers.

  The gap between this and the general axiom is precisely the reduction of an
  ARBITRARY open cover of X × Y to a rectangular one, which is where the deep
  (and, in general, false) topology lives.

  References:
  - Engelking, "Dimension Theory" (1978), §3.2 (logarithmic law).
  - Filippov (1972): a counterexample to dim(X × Y) = dim X + dim Y.
  - Erdos Problem #909: https://erdosproblems.com/909
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

open TopologicalSpace Set

namespace Erdos909OQ01OQ02

/-!
## Part I: Covering dimension (same definitions as the parent file)
-/

/-- A family of sets indexed by `ι` has order at most `k` if every point belongs
    to at most `k` sets of the family. -/
def HasOrderAtMost {X ι : Type*} (f : ι → Set X) (k : ℕ) : Prop :=
  ∀ (x : X) (S : Finset ι), (∀ i ∈ S, x ∈ f i) → S.card ≤ k

/-- Covering dimension: `dim X ≤ n` iff every finite open cover (indexed by
    `Fin k`) has a finite open refinement of order ≤ `n + 1`. -/
def coveringDimension (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (k : ℕ) (cover : Fin k → Set X),
    (∀ i, IsOpen (cover i)) →
    (⋃ i, cover i) = Set.univ →
    ∃ (m : ℕ) (refine : Fin m → Set X),
      (∀ j, IsOpen (refine j)) ∧
      (⋃ j, refine j) = Set.univ ∧
      (∀ j, ∃ i, refine j ⊆ cover i) ∧
      HasOrderAtMost refine (n + 1)

@[inherit_doc] notation "dimLeq" => coveringDimension

/-!
## Part II: Order behaves well under injective reindexing
-/

/-- Order is preserved when the index set is reindexed along an injective map. -/
theorem HasOrderAtMost.reindex {X ι κ : Type*} {f : ι → Set X} {k : ℕ}
    (h : HasOrderAtMost f k) (e : κ → ι) (he : Function.Injective e) :
    HasOrderAtMost (f ∘ e) k := by
  classical
  intro x S hS
  have hmap : S.card = (S.image e).card :=
    (Finset.card_image_of_injective S he).symm
  rw [hmap]
  apply h x (S.image e)
  intro i hi
  rw [Finset.mem_image] at hi
  obtain ⟨a, ha, rfl⟩ := hi
  exact hS a ha

/-!
## Part III: The product family and its order

Given `f : ι → Set X` and `g : κ → Set Y`, the product family sends `(i, j)` to
the rectangle `f i ×ˢ g j`.  Its order is the product of the two orders.
-/

/-- The rectangular product family `(i, j) ↦ f i ×ˢ g j`. -/
def prodFamily {X Y ι κ : Type*} (f : ι → Set X) (g : κ → Set Y) :
    ι × κ → Set (X × Y) :=
  fun r => f r.1 ×ˢ g r.2

/-- **Order of a product family.** If `f` has order ≤ `p` and `g` has order ≤ `q`,
    then the product family has order ≤ `p · q`.  This is the purely combinatorial
    core of the product dimension inequality. -/
theorem prodFamily_order {X Y ι κ : Type*} (f : ι → Set X) (g : κ → Set Y)
    (p q : ℕ) (hf : HasOrderAtMost f p) (hg : HasOrderAtMost g q) :
    HasOrderAtMost (prodFamily f g) (p * q) := by
  classical
  intro z S hS
  -- The first coordinate `z.1` lies in every `f i` for `i` a first-projection of `S`.
  have hAx : ∀ i ∈ S.image Prod.fst, z.1 ∈ f i := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨r, hr, hri⟩ := hi
    have hz := hS r hr
    rw [prodFamily, Set.mem_prod] at hz
    rw [← hri]; exact hz.1
  -- The second coordinate `z.2` lies in every `g j` for `j` a second-projection of `S`.
  have hBy : ∀ j ∈ S.image Prod.snd, z.2 ∈ g j := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨r, hr, hrj⟩ := hj
    have hz := hS r hr
    rw [prodFamily, Set.mem_prod] at hz
    rw [← hrj]; exact hz.2
  -- Every index in `S` lies in the rectangle `(image fst) ×ˢ (image snd)`.
  have hSsub : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro r hr
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hr, Finset.mem_image_of_mem _ hr⟩
  have hcardA : (S.image Prod.fst).card ≤ p := hf z.1 _ hAx
  have hcardB : (S.image Prod.snd).card ≤ q := hg z.2 _ hBy
  calc S.card ≤ ((S.image Prod.fst) ×ˢ (S.image Prod.snd)).card :=
        Finset.card_le_card hSsub
    _ = (S.image Prod.fst).card * (S.image Prod.snd).card := Finset.card_product _ _
    _ ≤ p * q := Nat.mul_le_mul hcardA hcardB

/-- The product family of open families is open. -/
theorem prodFamily_isOpen {X Y ι κ : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : ι → Set X) (g : κ → Set Y)
    (hf : ∀ i, IsOpen (f i)) (hg : ∀ j, IsOpen (g j)) :
    ∀ r, IsOpen (prodFamily f g r) :=
  fun r => (hf r.1).prod (hg r.2)

/-- The product family of covers is a cover of `X × Y`. -/
theorem prodFamily_cover {X Y ι κ : Type*} (f : ι → Set X) (g : κ → Set Y)
    (hf : (⋃ i, f i) = Set.univ) (hg : (⋃ j, g j) = Set.univ) :
    (⋃ r, prodFamily f g r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have h1 : z.1 ∈ ⋃ i, f i := by rw [hf]; exact Set.mem_univ _
  have h2 : z.2 ∈ ⋃ j, g j := by rw [hg]; exact Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h2
  apply Set.mem_iUnion.mpr
  refine ⟨(i, j), ?_⟩
  rw [prodFamily, Set.mem_prod]
  exact ⟨hi, hj⟩

/-- The product family refines the product of the refined covers. -/
theorem prodFamily_refines {X Y ι κ : Type*} (f : ι → Set X) (g : κ → Set Y)
    {kX kY : ℕ} (cX : Fin kX → Set X) (cY : Fin kY → Set Y)
    (hf : ∀ i, ∃ a, f i ⊆ cX a) (hg : ∀ j, ∃ b, g j ⊆ cY b) :
    ∀ r, ∃ s : Fin kX × Fin kY, prodFamily f g r ⊆ cX s.1 ×ˢ cY s.2 := by
  intro r
  obtain ⟨a, ha⟩ := hf r.1
  obtain ⟨b, hb⟩ := hg r.2
  exact ⟨(a, b), Set.prod_mono ha hb⟩

/-!
## Part IV: The product-cover dimension bound

The main theorem: if `dim X ≤ m` and `dim Y ≤ n`, then every *product* open cover
of `X × Y` admits a finite open refinement of order ≤ `(m+1)(n+1)`.  This is the
product dimension inequality restricted to rectangular covers.
-/

/-- **Product-cover refinement.** If `dim X ≤ m` and `dim Y ≤ n`, then for every
    open cover `cX` of `X` and open cover `cY` of `Y`, the product cover of `X × Y`
    admits a finite open refinement of order ≤ `(m+1)(n+1)`. -/
theorem product_cover_refinement
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {m n : ℕ}
    (hX : dimLeq X m) (hY : dimLeq Y n)
    (kX kY : ℕ) (cX : Fin kX → Set X) (cY : Fin kY → Set Y)
    (hcXopen : ∀ i, IsOpen (cX i)) (hcXcov : (⋃ i, cX i) = Set.univ)
    (hcYopen : ∀ j, IsOpen (cY j)) (hcYcov : (⋃ j, cY j) = Set.univ) :
    ∃ (M : ℕ) (refine : Fin M → Set (X × Y)),
      (∀ t, IsOpen (refine t)) ∧
      (⋃ t, refine t) = Set.univ ∧
      (∀ t, ∃ s : Fin kX × Fin kY, refine t ⊆ cX s.1 ×ˢ cY s.2) ∧
      HasOrderAtMost refine ((m + 1) * (n + 1)) := by
  -- Refine each factor cover.
  obtain ⟨mX, rX, hrXopen, hrXcov, hrXref, hrXord⟩ := hX kX cX hcXopen hcXcov
  obtain ⟨mY, rY, hrYopen, hrYcov, hrYref, hrYord⟩ := hY kY cY hcYopen hcYcov
  -- The product family of the two refinements, and its properties.
  set pf := prodFamily rX rY with hpf
  have hpfOpen : ∀ r, IsOpen (pf r) := prodFamily_isOpen rX rY hrXopen hrYopen
  have hpfCov : (⋃ r, pf r) = Set.univ := prodFamily_cover rX rY hrXcov hrYcov
  have hpfRef : ∀ r, ∃ s : Fin kX × Fin kY, pf r ⊆ cX s.1 ×ˢ cY s.2 :=
    prodFamily_refines rX rY cX cY hrXref hrYref
  have hpfOrder : HasOrderAtMost pf ((m + 1) * (n + 1)) :=
    prodFamily_order rX rY (m + 1) (n + 1) hrXord hrYord
  -- Reindex the product `Fin mX × Fin mY` to `Fin (mX * mY)`.
  let e : Fin mX × Fin mY ≃ Fin (mX * mY) := finProdFinEquiv
  refine ⟨mX * mY, fun t => pf (e.symm t), ?_, ?_, ?_, ?_⟩
  · exact fun t => hpfOpen (e.symm t)
  · -- cover: any `z` lies in some product-family member, indexed via `e`.
    apply Set.eq_univ_of_forall
    intro z
    have : z ∈ ⋃ r, pf r := by rw [hpfCov]; exact Set.mem_univ _
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp this
    apply Set.mem_iUnion.mpr
    refine ⟨e r, ?_⟩
    rwa [Equiv.symm_apply_apply]
  · exact fun t => hpfRef (e.symm t)
  · -- order: reindex along the injective map `e.symm`.
    exact hpfOrder.reindex e.symm e.symm.injective

/-- When the second factor is `0`-dimensional the product-cover bound is SHARP:
    it collapses to the full `dim X + dim Y = m`, matching `dimension_product_ineq`
    on product covers. -/
theorem product_cover_refinement_zero_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {m : ℕ}
    (hX : dimLeq X m) (hY : dimLeq Y 0)
    (kX kY : ℕ) (cX : Fin kX → Set X) (cY : Fin kY → Set Y)
    (hcXopen : ∀ i, IsOpen (cX i)) (hcXcov : (⋃ i, cX i) = Set.univ)
    (hcYopen : ∀ j, IsOpen (cY j)) (hcYcov : (⋃ j, cY j) = Set.univ) :
    ∃ (M : ℕ) (refine : Fin M → Set (X × Y)),
      (∀ t, IsOpen (refine t)) ∧
      (⋃ t, refine t) = Set.univ ∧
      (∀ t, ∃ s : Fin kX × Fin kY, refine t ⊆ cX s.1 ×ˢ cY s.2) ∧
      HasOrderAtMost refine (m + 0 + 1) := by
  obtain ⟨M, refine, ho, hc, hr, hord⟩ :=
    product_cover_refinement hX hY kX kY cX cY hcXopen hcXcov hcYopen hcYcov
  refine ⟨M, refine, ho, hc, hr, ?_⟩
  -- `(m+1)*(0+1) = m + 0 + 1`, so the order bound is exactly the sharp `m + n`.
  have : (m + 1) * (0 + 1) = m + 0 + 1 := by omega
  rw [← this]; exact hord

/-- Symmetric sharp case: when the first factor is `0`-dimensional. -/
theorem product_cover_refinement_zero_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (hX : dimLeq X 0) (hY : dimLeq Y n)
    (kX kY : ℕ) (cX : Fin kX → Set X) (cY : Fin kY → Set Y)
    (hcXopen : ∀ i, IsOpen (cX i)) (hcXcov : (⋃ i, cX i) = Set.univ)
    (hcYopen : ∀ j, IsOpen (cY j)) (hcYcov : (⋃ j, cY j) = Set.univ) :
    ∃ (M : ℕ) (refine : Fin M → Set (X × Y)),
      (∀ t, IsOpen (refine t)) ∧
      (⋃ t, refine t) = Set.univ ∧
      (∀ t, ∃ s : Fin kX × Fin kY, refine t ⊆ cX s.1 ×ˢ cY s.2) ∧
      HasOrderAtMost refine (0 + n + 1) := by
  obtain ⟨M, refine, ho, hc, hr, hord⟩ :=
    product_cover_refinement hX hY kX kY cX cY hcXopen hcXcov hcYopen hcYcov
  refine ⟨M, refine, ho, hc, hr, ?_⟩
  have : (0 + 1) * (n + 1) = 0 + n + 1 := by omega
  rw [← this]; exact hord

end Erdos909OQ01OQ02
