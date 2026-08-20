import Proofs.Erdos85AbelianCayleyC4Obstruction
import Proofs.Erdos85DifferenceArray

/-!
# The noncommutative Cayley product-collision obstruction

Node: B.2 / `GAP B-EXIST`.  The abelian parallelogram obstruction is the
commutative shadow of a more general Sidon law.  In any inverse-closed Cayley
graph, a collision between two non-backtracking length-two words with
different first letters produces the four-cycle
`1 -- a -- a*b = c*d -- c -- 1`.

Thus every viable nonabelian odd-order Cayley construction must make the
ordered product map injective after the unavoidable inverse/backtracking
identifications.
-/

namespace Erdos85

/-- A finite inverse-closed Cayley graph is regular of degree equal to the
cardinality of its connection set. -/
theorem invClosedCayleyGraph_degree
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    [DecidableRel (invClosedCayleyGraph (· ∈ A) hinv hone).Adj]
    (x : Γ) :
    (invClosedCayleyGraph (· ∈ A) hinv hone).degree x = A.card := by
  classical
  let f : Γ ↪ Γ :=
    ⟨fun a => x * a, by
      intro a b hab
      exact mul_left_cancel hab⟩
  have hneighbors :
      (invClosedCayleyGraph (· ∈ A) hinv hone).neighborFinset x =
        A.map f := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map]
    change (x⁻¹ * y ∈ A) ↔ ∃ a, a ∈ A ∧ f a = y
    constructor
    · intro hy
      refine ⟨x⁻¹ * y, hy, ?_⟩
      simp [f, mul_assoc]
    · rintro ⟨a, ha, hay⟩
      have hxy : x * a = y := by simpa [f] using hay
      simpa [← hxy] using ha
  rw [SimpleGraph.degree, hneighbors, Finset.card_map]

/-- A collision `a * b = c * d` between two non-backtracking connection
words with different first letters gives a four-cycle.  No commutativity is
used. -/
theorem invClosedCayley_containsC4_of_product_collision
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    {a b c d : Γ}
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hac : a ≠ c) (hprod : a * b ≠ 1)
    (hcollision : a * b = c * d) :
    containsC4 Γ (invClosedCayleyGraph S hinv hone) := by
  let G := invClosedCayleyGraph S hinv hone
  have h1a : G.Adj 1 a := by
    change S (1⁻¹ * a)
    simpa using ha
  have hap : G.Adj a (a * b) := by
    change S (a⁻¹ * (a * b))
    simpa using hb
  have hpc : G.Adj (a * b) c := by
    change S ((a * b)⁻¹ * c)
    have hdi : S d⁻¹ := (hinv d).mp hd
    rw [hcollision]
    simpa using hdi
  have hc1 : G.Adj c 1 := by
    change S (c⁻¹ * 1)
    simpa using (hinv c).mp hc
  exact containsC4_of_rim h1a hap hpc hc1
    (Ne.symm hprod) hac
    (G.ne_of_adj h1a).symm (G.ne_of_adj hap)
    (G.ne_of_adj hc1) (G.ne_of_adj hpc).symm

/-- **Noncommutative Sidon law.**  In a C4-free inverse-closed Cayley graph,
two non-backtracking length-two connection words with different first letters
have different products. -/
theorem connection_product_ne_of_invClosedCayley_not_containsC4
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    (hfree : ¬ containsC4 Γ (invClosedCayleyGraph S hinv hone))
    {a b c d : Γ}
    (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hac : a ≠ c) (hprod : a * b ≠ 1) :
    a * b ≠ c * d := by
  intro hcollision
  exact hfree (invClosedCayley_containsC4_of_product_collision
    S hinv hone ha hb hc hd hac hprod hcollision)

/-- The non-backtracking ordered-word product map of a C4-free Cayley graph
is injective.  This is the Cayley-coordinate form of the Moore two-ball
packing constraint. -/
theorem nonbacktracking_connectionProduct_injective
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    (hfree : ¬ containsC4 Γ (invClosedCayleyGraph S hinv hone)) :
    Function.Injective (fun p : {p : Γ × Γ //
      S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} => p.1.1 * p.1.2) := by
  intro p q hpq
  have hfirst : p.1.1 = q.1.1 := by
    by_contra hac
    exact (connection_product_ne_of_invClosedCayley_not_containsC4
      S hinv hone hfree p.2.1 p.2.2.1 q.2.1 q.2.2.1 hac p.2.2.2) hpq
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · change p.1.1 * p.1.2 = q.1.1 * q.1.2 at hpq
    rw [← hfirst] at hpq
    exact mul_left_cancel hpq

/-- Ordered pairs of connection elements which do not immediately
backtrack. -/
def nonbacktrackingConnectionPairs
    {Γ : Type*} [Group Γ] [DecidableEq Γ] (A : Finset Γ) : Finset (Γ × Γ) :=
  (A.product A).filter fun p => p.1 * p.2 ≠ 1

/-- An inverse-closed connection set has exactly `d(d-1)` non-backtracking
ordered words of length two. -/
theorem card_nonbacktrackingConnectionPairs
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A) :
    (nonbacktrackingConnectionPairs A).card = A.card * (A.card - 1) := by
  classical
  let P := A.product A
  let B := P.filter fun p => p.1 * p.2 = 1
  have hBcard : B.card = A.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq hpq
      apply Prod.ext hpq
      have hpProd := (Finset.mem_filter.mp hp).2
      have hqProd := (Finset.mem_filter.mp hq).2
      have hpInv : p.2 = p.1⁻¹ := eq_inv_of_mul_eq_one_right hpProd
      have hqInv : q.2 = q.1⁻¹ := eq_inv_of_mul_eq_one_right hqProd
      simpa [hpInv, hqInv, hpq]
    · intro a ha
      refine ⟨(a, a⁻¹), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨ha, (hinv a).mp ha⟩, mul_inv_cancel a⟩
  have hsplit := P.card_filter_add_card_filter_not
    (fun p : Γ × Γ => p.1 * p.2 = 1)
  have hPcard : P.card = A.card * A.card := Finset.card_product A A
  change B.card + (nonbacktrackingConnectionPairs A).card = P.card at hsplit
  rw [hBcard, hPcard] at hsplit
  by_cases hzero : A.card = 0
  · simp [hzero] at hsplit ⊢
    exact hsplit
  · have hdecomp : A.card = (A.card - 1) + 1 := by omega
    have hmul : A.card * A.card =
        A.card * (A.card - 1) + A.card := by
      calc
        A.card * A.card = A.card * ((A.card - 1) + 1) :=
          congrArg (A.card * ·) hdecomp
        _ = A.card * (A.card - 1) + A.card := by
          rw [Nat.mul_add]
          simp
    omega

/-- In a finite C4-free inverse-closed Cayley graph, the set of group
elements reached by non-backtracking connection words has cardinal exactly
`d(d-1)`. -/
theorem card_nonbacktracking_connectionProducts
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    ((nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2).card =
      A.card * (A.card - 1) := by
  rw [Finset.card_image_iff.mpr]
  · exact card_nonbacktrackingConnectionPairs A hinv
  · intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hqA := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    apply Prod.ext
    · by_contra hac
      exact (connection_product_ne_of_invClosedCayley_not_containsC4
        (· ∈ A) hinv hone hfree hpA.1 hpA.2 hqA.1 hqA.2 hac hp') hpq
    · have hfirst : p.1 = q.1 := by
        by_contra hac
        exact (connection_product_ne_of_invClosedCayley_not_containsC4
          (· ∈ A) hinv hone hfree hpA.1 hpA.2 hqA.1 hqA.2 hac hp') hpq
      change p.1 * p.2 = q.1 * q.2 at hpq
      rw [← hfirst] at hpq
      exact mul_left_cancel hpq

/-- **Exact plane-minus-two Cayley slack.**  At the target order `q²-1`, a
size-`q` inverse-closed C4-free connection set has exactly `q-2` nonidentity
group elements which are not represented by a non-backtracking word of
length two. -/
theorem card_unused_nonidentity_of_planeMinusTwo_Cayley
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (q : ℕ) (hq : 2 ≤ q)
    (hcardΓ : Fintype.card Γ = q * q - 1)
    (hcardA : A.card = q) :
    (((Finset.univ.erase (1 : Γ)) \
      ((nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2)).card) =
        q - 2 := by
  classical
  let W := (nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2
  have hWcard : W.card = q * (q - 1) := by
    simpa [W, hcardA] using
      card_nonbacktracking_connectionProducts A hinv hone hfree
  have hWsub : W ⊆ Finset.univ.erase (1 : Γ) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    have hpne := (Finset.mem_filter.mp hp).2
    exact Finset.mem_erase.mpr ⟨hpne, Finset.mem_univ _⟩
  have hcardErase : (Finset.univ.erase (1 : Γ)).card = q * q - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : Γ)), Finset.card_univ,
      hcardΓ]
    omega
  change ((Finset.univ.erase (1 : Γ)) \ W).card = q - 2
  have hinter : W ∩ Finset.univ.erase (1 : Γ) = W :=
    Finset.inter_eq_left.mpr hWsub
  rw [Finset.card_sdiff, hinter, hcardErase, hWcard]
  have hdecomp : q = (q - 1) + 1 := by omega
  have hmul : q * q = q * (q - 1) + q := by
    calc
      q * q = q * ((q - 1) + 1) := congrArg (q * ·) hdecomp
      _ = q * (q - 1) + q := by rw [Nat.mul_add]; simp
  omega

/-- The nonidentity elements missed by the non-backtracking product map. -/
def unusedNonidentityConnectionProducts
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ) : Finset Γ :=
  (Finset.univ.erase 1) \
    ((nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2)

/-- The unused product slack of an inverse-closed connection set is itself
closed under inversion. -/
theorem unusedNonidentityConnectionProducts_inv_mem
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    {g : Γ} (hg : g ∈ unusedNonidentityConnectionProducts A) :
    g⁻¹ ∈ unusedNonidentityConnectionProducts A := by
  classical
  have hgne : g ≠ 1 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hg).1).1
  apply Finset.mem_sdiff.mpr
  constructor
  · exact Finset.mem_erase.mpr ⟨inv_ne_one.mpr hgne, Finset.mem_univ _⟩
  · intro hginv
    obtain ⟨p, hp, hprod⟩ := Finset.mem_image.mp hginv
    have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hpne := (Finset.mem_filter.mp hp).2
    let q : Γ × Γ := (p.2⁻¹, p.1⁻¹)
    have hq : q ∈ nonbacktrackingConnectionPairs A := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨(hinv p.2).mp hpA.2, (hinv p.1).mp hpA.1⟩
      · change p.2⁻¹ * p.1⁻¹ ≠ 1
        simpa only [mul_inv_rev] using inv_ne_one.mpr hpne
    have hgImage : g ∈
        (nonbacktrackingConnectionPairs A).image fun r => r.1 * r.2 := by
      apply Finset.mem_image.mpr
      refine ⟨q, hq, ?_⟩
      change p.2⁻¹ * p.1⁻¹ = g
      have hprod' : p.1 * p.2 = g⁻¹ := hprod
      have := congrArg Inv.inv hprod'
      simpa only [mul_inv_rev, inv_inv] using this
    exact (Finset.mem_sdiff.mp hg).2 hgImage

/-- If the unused product slack has odd cardinality, inversion fixes one of
its elements.  Since the slack omits the identity, this is a nontrivial
involution in the ambient group. -/
theorem exists_unused_nontrivial_involution_of_odd_card
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hodd : Odd (unusedNonidentityConnectionProducts A).card) :
    ∃ g, g ∈ unusedNonidentityConnectionProducts A ∧ g⁻¹ = g := by
  classical
  let U := unusedNonidentityConnectionProducts A
  let I := {g : Γ // g ∈ U}
  let f : I → I := fun g =>
    ⟨g.1⁻¹, unusedNonidentityConnectionProducts_inv_mem A hinv g.2⟩
  have hf : Function.Involutive f := by
    intro g
    apply Subtype.ext
    simp [f]
  have hIodd : Odd (Fintype.card I) := by
    simpa [I, U] using hodd
  obtain ⟨g, hg⟩ := everyInvolutionHasFixedPoint_of_odd hIodd f hf
  refine ⟨g.1, g.2, ?_⟩
  exact congrArg Subtype.val hg

/-- For odd `q`, every C4-free Cayley witness at the plane-minus-two target
has a nonidentity involution among its `q-2` unused products. -/
theorem exists_unused_involution_of_odd_planeMinusTwo_Cayley
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (q : ℕ) (hq : 3 ≤ q) (hqodd : Odd q)
    (hcardΓ : Fintype.card Γ = q * q - 1)
    (hcardA : A.card = q) :
    ∃ g, g ≠ 1 ∧ g * g = 1 ∧
      g ∈ unusedNonidentityConnectionProducts A := by
  have hcardUnused : (unusedNonidentityConnectionProducts A).card = q - 2 := by
    simpa [unusedNonidentityConnectionProducts] using
      card_unused_nonidentity_of_planeMinusTwo_Cayley
        A hinv hone hfree q (by omega) hcardΓ hcardA
  have hoddUnused : Odd (unusedNonidentityConnectionProducts A).card := by
    rw [hcardUnused]
    rcases hqodd with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨g, hg, hginv⟩ :=
    exists_unused_nontrivial_involution_of_odd_card A hinv hoddUnused
  have hgne : g ≠ 1 :=
    (Finset.mem_erase.mp (Finset.mem_sdiff.mp hg).1).1
  have hgsq : g * g = 1 := by
    calc
      g * g = g * g⁻¹ := congrArg (g * ·) hginv.symm
      _ = 1 := mul_inv_cancel g
  exact ⟨g, hgne, hgsq, hg⟩

/-- Every odd-cardinality inverse-closed connection set which omits the
identity contains a nontrivial involution. -/
theorem exists_connection_involution_of_odd_card
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hodd : Odd A.card) :
    ∃ t, t ∈ A ∧ t ≠ 1 ∧ t * t = 1 := by
  classical
  let I := {g : Γ // g ∈ A}
  let f : I → I := fun g => ⟨g.1⁻¹, (hinv g.1).mp g.2⟩
  have hf : Function.Involutive f := by
    intro g
    apply Subtype.ext
    simp [f]
  have hIodd : Odd (Fintype.card I) := by
    simpa [I] using hodd
  obtain ⟨t, ht⟩ := everyInvolutionHasFixedPoint_of_odd hIodd f hf
  have htinv : t.1⁻¹ = t.1 := congrArg Subtype.val ht
  have htne : t.1 ≠ 1 := by
    intro htone
    exact hone (htone ▸ t.2)
  have htsq : t.1 * t.1 = 1 := by
    calc
      t.1 * t.1 = t.1 * t.1⁻¹ := congrArg (t.1 * ·) htinv.symm
      _ = 1 := mul_inv_cancel t.1
  exact ⟨t.1, t.2, htne, htsq⟩

/-- Consequently every odd-degree undirected Cayley graph contains a
canonical fixed-point-free involutory matching layer, given by right
multiplication by an involutory connection element. -/
theorem exists_connection_perfectMatchingLayer_of_odd_card
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hodd : Odd A.card) :
    ∃ t, t ∈ A ∧ t ≠ 1 ∧ t * t = 1 ∧
      Function.Involutive (fun x : Γ => x * t) ∧
      ∀ x, x * t ≠ x ∧
        (invClosedCayleyGraph (· ∈ A) hinv hone).Adj x (x * t) := by
  obtain ⟨t, htA, htne, htsq⟩ :=
    exists_connection_involution_of_odd_card A hinv hone hodd
  refine ⟨t, htA, htne, htsq, ?_, ?_⟩
  · intro x
    change (x * t) * t = x
    rw [mul_assoc, htsq, mul_one]
  · intro x
    constructor
    · intro hfix
      apply htne
      change x * t = x at hfix
      have hfix' : x * t = x * 1 := by simpa using hfix
      exact mul_left_cancel hfix'
    · change (x⁻¹ * (x * t)) ∈ A
      simpa using htA

/-- Removing an involutory connection element preserves inverse-closure. -/
theorem mem_erase_involution_iff_inv_mem_erase
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    {t : Γ} (htsq : t * t = 1) (g : Γ) :
    g ∈ A.erase t ↔ g⁻¹ ∈ A.erase t := by
  have htinv : t⁻¹ = t := by
    exact (eq_inv_of_mul_eq_one_right htsq).symm
  constructor
  · intro hg
    have hg' := Finset.mem_erase.mp hg
    apply Finset.mem_erase.mpr
    constructor
    · intro hgit
      apply hg'.1
      calc
        g = (g⁻¹)⁻¹ := by simp
        _ = t⁻¹ := congrArg Inv.inv hgit
        _ = t := htinv
    · exact (hinv g).mp hg'.2
  · intro hg
    have hg' := Finset.mem_erase.mp hg
    apply Finset.mem_erase.mpr
    constructor
    · intro hgt
      apply hg'.1
      calc
        g⁻¹ = t⁻¹ := congrArg Inv.inv hgt
        _ = t := htinv
    · exact (hinv g).mpr hg'.2

/-- Erasing an involutory generator splits the Cayley adjacency relation
exactly into the residual Cayley graph and the matching `y = x*t`. -/
theorem invClosedCayley_erase_involution_adj_iff
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (x y : Γ) :
    (invClosedCayleyGraph (· ∈ A) hinv hone).Adj x y ↔
      (invClosedCayleyGraph (· ∈ A.erase t)
        (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
        (by exact fun h => hone (Finset.mem_of_mem_erase h))).Adj x y ∨
      y = x * t := by
  have hyiff : y = x * t ↔ x⁻¹ * y = t := by
    constructor
    · intro hy
      simp [hy]
    · intro hy
      have h := congrArg (x * ·) hy
      simpa [mul_assoc] using h
  change (x⁻¹ * y ∈ A) ↔
    (x⁻¹ * y ∈ A.erase t) ∨ y = x * t
  rw [hyiff]
  by_cases hxy : x⁻¹ * y = t
  · simp [Finset.mem_erase, hxy, htA]
  · simp [Finset.mem_erase, hxy]

/-- The residual Cayley layer obtained by erasing an involutory generator is
a subgraph, so C4-freeness is preserved. -/
theorem invClosedCayley_erase_involution_not_containsC4
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t : Γ} (htsq : t * t = 1) :
    ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A.erase t)
        (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
        (by exact fun h => hone (Finset.mem_of_mem_erase h))) := by
  intro hc4
  apply hfree
  apply containsC4_mono (G := invClosedCayleyGraph (· ∈ A.erase t)
    (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
    (by exact fun h => hone (Finset.mem_of_mem_erase h)))
  · intro x y hxy
    change x⁻¹ * y ∈ A.erase t at hxy
    change x⁻¹ * y ∈ A
    exact Finset.mem_of_mem_erase hxy
  · exact hc4

/-- If the erased involution belongs to the connection set, the residual
Cayley graph is regular of degree exactly one less. -/
theorem invClosedCayley_erase_involution_degree
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    [DecidableRel (invClosedCayleyGraph (· ∈ A.erase t)
      (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
      (by exact fun h => hone (Finset.mem_of_mem_erase h))).Adj]
    (x : Γ) :
    (invClosedCayleyGraph (· ∈ A.erase t)
      (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
      (by exact fun h => hone (Finset.mem_of_mem_erase h))).degree x =
        A.card - 1 := by
  classical
  have honeErase : (1 : Γ) ∉ A.erase t :=
    fun h => hone (Finset.mem_of_mem_erase h)
  rw [invClosedCayleyGraph_degree (A.erase t)
    (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
    honeErase x,
    Finset.card_erase_of_mem htA]

/-- **Odd Cayley peel capstone.**  Every odd-cardinality inverse-closed
connection set in a C4-free Cayley graph admits an involutory generator whose
removal leaves a C4-free connection set of cardinality one smaller, and the
erased graph reconstructs by adding exactly its matching layer. -/
theorem exists_c4Free_evenResidual_matchingDecomposition_of_odd_Cayley
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hodd : Odd A.card)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    ∃ t, ∃ htsq : t * t = 1, t ∈ A ∧ t ≠ 1 ∧
      (A.erase t).card = A.card - 1 ∧
      ¬ containsC4 Γ
        (invClosedCayleyGraph (· ∈ A.erase t)
          (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
          (by exact fun h => hone (Finset.mem_of_mem_erase h))) ∧
      ∀ x y,
        (invClosedCayleyGraph (· ∈ A) hinv hone).Adj x y ↔
          (invClosedCayleyGraph (· ∈ A.erase t)
            (mem_erase_involution_iff_inv_mem_erase A hinv htsq)
            (by exact fun h => hone (Finset.mem_of_mem_erase h))).Adj x y ∨
          y = x * t := by
  obtain ⟨t, htA, htne, htsq⟩ :=
    exists_connection_involution_of_odd_card A hinv hone hodd
  refine ⟨t, htsq, htA, htne, ?_, ?_, ?_⟩
  · exact Finset.card_erase_of_mem htA
  · exact invClosedCayley_erase_involution_not_containsC4
      A hinv hone hfree htsq
  · intro x y
    exact invClosedCayley_erase_involution_adj_iff
      A hinv hone htA htsq x y

end Erdos85

#print axioms Erdos85.invClosedCayley_containsC4_of_product_collision
#print axioms Erdos85.invClosedCayleyGraph_degree
#print axioms Erdos85.connection_product_ne_of_invClosedCayley_not_containsC4
#print axioms Erdos85.nonbacktracking_connectionProduct_injective
#print axioms Erdos85.card_nonbacktrackingConnectionPairs
#print axioms Erdos85.card_nonbacktracking_connectionProducts
#print axioms Erdos85.card_unused_nonidentity_of_planeMinusTwo_Cayley
#print axioms Erdos85.unusedNonidentityConnectionProducts_inv_mem
#print axioms Erdos85.exists_unused_nontrivial_involution_of_odd_card
#print axioms Erdos85.exists_unused_involution_of_odd_planeMinusTwo_Cayley
#print axioms Erdos85.exists_connection_involution_of_odd_card
#print axioms Erdos85.exists_connection_perfectMatchingLayer_of_odd_card
#print axioms Erdos85.mem_erase_involution_iff_inv_mem_erase
#print axioms Erdos85.invClosedCayley_erase_involution_adj_iff
#print axioms Erdos85.invClosedCayley_erase_involution_not_containsC4
#print axioms Erdos85.invClosedCayley_erase_involution_degree
#print axioms Erdos85.exists_c4Free_evenResidual_matchingDecomposition_of_odd_Cayley
