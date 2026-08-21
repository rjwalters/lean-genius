import Proofs.Erdos85AbelianCayleyC4Obstruction
import Proofs.Erdos85DifferenceArray
import Proofs.SpernerTuckerAntipodalParityEngine

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

/-- Conjugation by an involutory connection element sends every other
connection element outside the connection set.  Otherwise the two words
`s*t` and `t*(t*s*t)` collide and create a four-cycle. -/
theorem involution_conjugate_not_mem_connection
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t s : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (hsA : s ∈ A) (hst : s ≠ t) :
    t * s * t ∉ A := by
  intro hconjA
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right htsq).symm
  have hprod : s * t ≠ 1 := by
    intro hstOne
    apply hst
    calc
      s = t⁻¹ := eq_inv_of_mul_eq_one_left hstOne
      _ = t := htinv
  have hcollision : s * t = t * (t * s * t) := by
    calc
      s * t = 1 * (s * t) := by simp
      _ = (t * t) * (s * t) := by rw [htsq]
      _ = t * (t * s * t) := by simp [mul_assoc]
  exact hfree (invClosedCayley_containsC4_of_product_collision
    (· ∈ A) hinv hone hsA htA htA hconjA hst hprod hcollision)

/-- Hence an involutory generator in a C4-free Cayley graph commutes with no
other generator.  The forced odd-degree matching layer must be genuinely
noncentral. -/
theorem involution_generator_not_commute
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t s : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (hsA : s ∈ A) (hst : s ≠ t) :
    t * s ≠ s * t := by
  intro hcomm
  have hconj : t * s * t = s := by
    calc
      t * s * t = (s * t) * t := congrArg (· * t) hcomm
      _ = s * (t * t) := by rw [mul_assoc]
      _ = s := by rw [htsq, mul_one]
  have hconjA : t * s * t ∈ A := by
    rw [hconj]
    exact hsA
  exact (involution_conjugate_not_mem_connection
    A hinv hone hfree htA htsq hsA hst) hconjA

/-- Conjugation by an involution, packaged as an embedding. -/
def involutionConjugateEmbedding
    {Γ : Type*} [Group Γ]
    (t : Γ) (htsq : t * t = 1) : Γ ↪ Γ where
  toFun s := t * s * t
  inj' := by
    intro a b hab
    have h := congrArg (fun s => t * s * t) hab
    simpa [mul_assoc, htsq] using h

/-- The conjugate shore of a finite set under an involution. -/
def involutionConjugateFinset
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (B : Finset Γ) (t : Γ) (htsq : t * t = 1) : Finset Γ :=
  B.map (involutionConjugateEmbedding t htsq)

/-- The residual connection shore and its involution-conjugate shore are
disjoint in every C4-free Cayley graph. -/
theorem erase_involution_disjoint_conjugate_shore
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1) :
    Disjoint (A.erase t)
      (involutionConjugateFinset (A.erase t) t htsq) := by
  rw [Finset.disjoint_left]
  intro g hgA hgConj
  obtain ⟨s, hsA, hsg⟩ := Finset.mem_map.mp hgConj
  have hsA' : s ∈ A := Finset.mem_of_mem_erase hsA
  have hst : s ≠ t := (Finset.mem_erase.mp hsA).1
  have hgA' : g ∈ A := Finset.mem_of_mem_erase hgA
  have hconjA : t * s * t ∈ A := by
    change involutionConjugateEmbedding t htsq s ∈ A
    rw [hsg]
    exact hgA'
  exact (involution_conjugate_not_mem_connection
    A hinv hone hfree htA htsq hsA' hst) hconjA

/-- Consequently the residual and conjugate shores form a `2(d-1)`-element
set. -/
theorem card_erase_involution_union_conjugate_shore
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1) :
    ((A.erase t) ∪ involutionConjugateFinset (A.erase t) t htsq).card =
      2 * (A.card - 1) := by
  have hdisj := erase_involution_disjoint_conjugate_shore
    A hinv hone hfree htA htsq
  rw [Finset.card_union_of_disjoint hdisj,
    involutionConjugateFinset, Finset.card_map,
    Finset.card_erase_of_mem htA]
  omega

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

/-- **Exact noncommutative Sidon characterization.**  An inverse-closed
Cayley graph is C4-free exactly when multiplication is injective on its
non-backtracking ordered connection pairs. -/
theorem not_containsC4_iff_nonbacktracking_connectionProduct_injective
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1) :
    (¬ containsC4 Γ (invClosedCayleyGraph S hinv hone)) ↔
      Function.Injective (fun p : {p : Γ × Γ //
        S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} => p.1.1 * p.1.2) := by
  constructor
  · exact nonbacktracking_connectionProduct_injective S hinv hone
  · intro hInjective hc4
    obtain ⟨f, hf, hadj⟩ := hc4
    let G := invClosedCayleyGraph S hinv hone
    have h01 : G.Adj (f 0) (f 1) := hadj 0 1 C4_adj_zero_one
    have h12 : G.Adj (f 1) (f 2) := hadj 1 2 C4_adj_one_two
    have h03 : G.Adj (f 0) (f 3) :=
      (hadj 3 0 C4_adj_three_zero).symm
    have h32 : G.Adj (f 3) (f 2) :=
      (hadj 2 3 C4_adj_two_three).symm
    have h02 : f 0 ≠ f 2 := by
      intro h
      exact (by decide : (0 : Fin 4) ≠ 2) (hf h)
    let p : {p : Γ × Γ // S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} :=
      ⟨((f 0)⁻¹ * f 1, (f 1)⁻¹ * f 2), h01, h12, by
        intro hp
        have hp' := congrArg (fun z => f 0 * z) hp
        apply h02
        have hpEq : f 2 = f 0 := by simpa [mul_assoc] using hp'
        exact hpEq.symm⟩
    let q : {p : Γ × Γ // S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} :=
      ⟨((f 0)⁻¹ * f 3, (f 3)⁻¹ * f 2), h03, h32, by
        intro hq
        have hq' := congrArg (fun z => f 0 * z) hq
        apply h02
        have hqEq : f 2 = f 0 := by simpa [mul_assoc] using hq'
        exact hqEq.symm⟩
    have hpqProduct : p.1.1 * p.1.2 = q.1.1 * q.1.2 := by
      simp [p, q, mul_assoc]
    have hpq : p = q := hInjective hpqProduct
    have hfirst : (f 0)⁻¹ * f 1 = (f 0)⁻¹ * f 3 := by
      exact congrArg (fun z => z.1.1) hpq
    have h13 : f 1 = f 3 := by
      exact mul_left_cancel hfirst
    exact (by decide : (1 : Fin 4) ≠ 3) (hf h13)

/-- An involutory connection element is never represented by a
non-backtracking word of length two.  Otherwise inversion supplies the second
representation `(b⁻¹,a⁻¹)`. -/
theorem involution_connection_ne_nonbacktracking_product
    {Γ : Type*} [Group Γ]
    (S : Γ → Prop)
    (hinv : ∀ g, S g ↔ S g⁻¹)
    (hone : ¬ S 1)
    (hfree : ¬ containsC4 Γ (invClosedCayleyGraph S hinv hone))
    {t a b : Γ} (htsq : t * t = 1)
    (ha : S a) (hb : S b) (hab : a * b ≠ 1) :
    a * b ≠ t := by
  intro habt
  have hInjective := nonbacktracking_connectionProduct_injective
    S hinv hone hfree
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right htsq).symm
  let p : {p : Γ × Γ // S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} :=
    ⟨(a, b), ha, hb, hab⟩
  let q : {p : Γ × Γ // S p.1 ∧ S p.2 ∧ p.1 * p.2 ≠ 1} :=
    ⟨(b⁻¹, a⁻¹), (hinv b).mp hb, (hinv a).mp ha, by
      change b⁻¹ * a⁻¹ ≠ 1
      rw [← mul_inv_rev]
      exact inv_ne_one.mpr hab⟩
  have hpqProduct : p.1.1 * p.1.2 = q.1.1 * q.1.2 := by
    change a * b = b⁻¹ * a⁻¹
    calc
      a * b = t := habt
      _ = t⁻¹ := htinv.symm
      _ = (a * b)⁻¹ := congrArg Inv.inv habt.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
  have hpq : p = q := hInjective hpqProduct
  have hfirst : a = b⁻¹ := congrArg (fun z => z.1.1) hpq
  apply hab
  calc
    a * b = b⁻¹ * b := congrArg (· * b) hfirst
    _ = 1 := inv_mul_cancel b

/-- Ordered pairs of connection elements which do not immediately
backtrack. -/
def nonbacktrackingConnectionPairs
    {Γ : Type*} [Group Γ] [DecidableEq Γ] (A : Finset Γ) : Finset (Γ × Γ) :=
  (A.product A).filter fun p => p.1 * p.2 ≠ 1

/-- The immediately backtracking ordered pairs are in bijection with their
first connection element. -/
theorem card_backtrackingConnectionPairs
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A) :
    ((A.product A).filter fun p => p.1 * p.2 = 1).card = A.card := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext hpq
    have hpInv : p.2 = p.1⁻¹ :=
      eq_inv_of_mul_eq_one_right (Finset.mem_filter.mp hp).2
    have hqInv : q.2 = q.1⁻¹ :=
      eq_inv_of_mul_eq_one_right (Finset.mem_filter.mp hq).2
    simpa [hpInv, hqInv, hpq]
  · intro a ha
    refine ⟨(a, a⁻¹), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨ha, (hinv a).mp ha⟩, mul_inv_cancel a⟩

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

/-- The integral group-ring indicator of a finite subset.  This packages the
exact (multiplicity-sensitive) product ledger of a Cayley connection set. -/
noncomputable def finsetGroupRingIndicator
    {Γ : Type*} [Group Γ] (S : Finset Γ) : MonoidAlgebra ℤ Γ :=
  ∑ g ∈ S, MonoidAlgebra.single g 1

/-- A finite-set indicator has coefficient one precisely on the set. -/
@[simp] theorem finsetGroupRingIndicator_coeff_apply
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (S : Finset Γ) (x : Γ) :
    MonoidAlgebra.coeff (finsetGroupRingIndicator S) x =
      if x ∈ S then 1 else 0 := by
  classical
  simp only [finsetGroupRingIndicator, MonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  have hsingle (c : Γ) :
      MonoidAlgebra.coeff (MonoidAlgebra.single c (1 : ℤ)) x =
        if c = x then 1 else 0 := by
    exact MonoidAlgebra.single_apply
  simp_rw [hsingle]
  by_cases hx : x ∈ S <;> simp [hx]

/-- Ordered representations of `x` as a product from `S × T`. -/
def finsetProductRepresentations
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (S T : Finset Γ) (x : Γ) : Finset (Γ × Γ) :=
  (S.product T).filter fun p => p.1 * p.2 = x

/-- Indicators turn a disjoint union into a sum. -/
theorem finsetGroupRingIndicator_union_of_disjoint
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    {S T : Finset Γ} (hdisj : Disjoint S T) :
    finsetGroupRingIndicator (S ∪ T) =
      finsetGroupRingIndicator S + finsetGroupRingIndicator T := by
  classical
  simpa [finsetGroupRingIndicator] using
    (Finset.sum_union hdisj :
      ∑ g ∈ S ∪ T, MonoidAlgebra.single g (1 : ℤ) =
        (∑ g ∈ S, MonoidAlgebra.single g 1) +
          ∑ g ∈ T, MonoidAlgebra.single g 1)

@[simp] theorem finsetGroupRingIndicator_singleton_one
    {Γ : Type*} [Group Γ] [DecidableEq Γ] :
    finsetGroupRingIndicator ({1} : Finset Γ) =
      (1 : MonoidAlgebra ℤ Γ) := by
  classical
  simp [finsetGroupRingIndicator, MonoidAlgebra.one_def]

/-- Multiplication of finite-set indicators enumerates all ordered products,
with their natural representation multiplicities. -/
theorem finsetGroupRingIndicator_mul
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (S T : Finset Γ) :
    finsetGroupRingIndicator S * finsetGroupRingIndicator T =
      ∑ p ∈ S.product T, MonoidAlgebra.single (p.1 * p.2) 1 := by
  classical
  simp only [finsetGroupRingIndicator, Finset.sum_mul, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, one_mul]
  rw [Finset.sum_comm]
  exact (Finset.sum_product' S T
    (fun s t => MonoidAlgebra.single (s * t) 1)).symm

/-- A coefficient of an indicator product is the corresponding ordered
representation count. -/
theorem finsetGroupRingIndicator_mul_coeff_eq_card_representations
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (S T : Finset Γ) (x : Γ) :
    MonoidAlgebra.coeff
        (finsetGroupRingIndicator S * finsetGroupRingIndicator T) x =
      (finsetProductRepresentations S T x).card := by
  classical
  rw [finsetGroupRingIndicator_mul]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hsingle (p : Γ × Γ) :
      MonoidAlgebra.coeff
          (MonoidAlgebra.single (p.1 * p.2) (1 : ℤ)) x =
        if p.1 * p.2 = x then 1 else 0 := by
    exact MonoidAlgebra.single_apply
  simp_rw [hsingle]
  simp [finsetProductRepresentations]

/-- Right translation permutes the full finite-group indicator. -/
theorem finsetGroupRingIndicator_univ_mul_single
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] (s : Γ) :
    finsetGroupRingIndicator (Finset.univ : Finset Γ) *
        MonoidAlgebra.single s 1 =
      finsetGroupRingIndicator (Finset.univ : Finset Γ) := by
  classical
  simp only [finsetGroupRingIndicator, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul]
  apply Finset.sum_bij (fun g _ => g * s)
  · intro g _
    exact Finset.mem_univ _
  · intro g₁ _ g₂ _ h
    exact mul_right_cancel h
  · intro h _
    refine ⟨h * s⁻¹, Finset.mem_univ _, ?_⟩
    simp [mul_assoc]
  · intro g _
    rfl

/-- Left translation also permutes the full finite-group indicator. -/
theorem finsetGroupRingIndicator_single_mul_univ
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] (s : Γ) :
    MonoidAlgebra.single s 1 *
        finsetGroupRingIndicator (Finset.univ : Finset Γ) =
      finsetGroupRingIndicator (Finset.univ : Finset Γ) := by
  classical
  simp only [finsetGroupRingIndicator, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, one_mul]
  apply Finset.sum_bij (fun g _ => s * g)
  · intro g _
    exact Finset.mem_univ _
  · intro g₁ _ g₂ _ h
    exact mul_left_cancel h
  · intro h _
    refine ⟨s⁻¹ * h, Finset.mem_univ _, ?_⟩
    simp [mul_assoc]
  · intro g _
    rfl

/-- The full finite-group indicator commutes with every finite-set
indicator; both products are the cardinality of the set times the full
indicator. -/
theorem finsetGroupRingIndicator_univ_commute
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] (S : Finset Γ) :
    finsetGroupRingIndicator (Finset.univ : Finset Γ) *
        finsetGroupRingIndicator S =
      finsetGroupRingIndicator S *
        finsetGroupRingIndicator (Finset.univ : Finset Γ) := by
  classical
  let F := finsetGroupRingIndicator (Finset.univ : Finset Γ)
  change F * (∑ s ∈ S, MonoidAlgebra.single s 1) =
    (∑ s ∈ S, MonoidAlgebra.single s 1) * F
  rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [F, finsetGroupRingIndicator_univ_mul_single,
    finsetGroupRingIndicator_single_mul_univ]

/-- The identity, a subset of the nonidentity elements, and its unused
complement form an exact indicator partition of a finite group. -/
theorem finsetGroupRingIndicator_identity_used_unused_partition
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (used : Finset Γ) (hused : used ⊆ Finset.univ.erase (1 : Γ)) :
    finsetGroupRingIndicator ({1} : Finset Γ) +
        finsetGroupRingIndicator used +
        finsetGroupRingIndicator ((Finset.univ.erase 1) \ used) =
      finsetGroupRingIndicator (Finset.univ : Finset Γ) := by
  classical
  let E := Finset.univ.erase (1 : Γ)
  have husedDisj : Disjoint used (E \ used) := Finset.disjoint_sdiff
  have honeDisj : Disjoint ({1} : Finset Γ) E := by
    simp [E, Finset.disjoint_left]
  have husedUnion : used ∪ (E \ used) = E :=
    Finset.union_sdiff_of_subset hused
  have honeUnion : ({1} : Finset Γ) ∪ E = Finset.univ := by
    ext g
    by_cases hg : g = 1 <;> simp [E, hg]
  rw [add_assoc,
    ← finsetGroupRingIndicator_union_of_disjoint husedDisj,
    husedUnion,
    ← finsetGroupRingIndicator_union_of_disjoint honeDisj,
    honeUnion]

/-- **Exact group-ring Sidon square.**  In a C4-free inverse-closed Cayley
graph, the square of the connection indicator has coefficient `#A` at the
identity and coefficient one at every represented non-backtracking product. -/
theorem connectionIndicator_sq_eq_backtracking_add_used
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    finsetGroupRingIndicator A * finsetGroupRingIndicator A =
      A.card • (1 : MonoidAlgebra ℤ Γ) +
        finsetGroupRingIndicator
          ((nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2) := by
  classical
  let P := A.product A
  let B := P.filter fun p => p.1 * p.2 = 1
  let N := nonbacktrackingConnectionPairs A
  let f : Γ × Γ → Γ := fun p => p.1 * p.2
  have hsplit :
      (∑ p ∈ P, MonoidAlgebra.single (f p) (1 : ℤ)) =
        (∑ p ∈ B, MonoidAlgebra.single (f p) 1) +
          ∑ p ∈ N, MonoidAlgebra.single (f p) 1 := by
    have h := Finset.sum_filter_add_sum_filter_not P
      (fun p => p.1 * p.2 = 1)
      (fun p => MonoidAlgebra.single (f p) (1 : ℤ))
    simpa [B, N, P, nonbacktrackingConnectionPairs, f] using h.symm
  have hback :
      (∑ p ∈ B, MonoidAlgebra.single (f p) (1 : ℤ)) =
        A.card • (1 : MonoidAlgebra ℤ Γ) := by
    calc
      (∑ p ∈ B, MonoidAlgebra.single (f p) (1 : ℤ)) =
          ∑ _p ∈ B, MonoidAlgebra.single 1 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpone := (Finset.mem_filter.mp hp).2
            simpa [B, P, f] using congrArg
              (fun g => MonoidAlgebra.single g (1 : ℤ)) hpone
      _ = B.card • MonoidAlgebra.single 1 (1 : ℤ) := by
            rw [Finset.sum_const]
      _ = A.card • (1 : MonoidAlgebra ℤ Γ) := by
            rw [show B.card = A.card by
              simpa [B, P] using card_backtrackingConnectionPairs A hinv]
            simp [MonoidAlgebra.one_def]
  have hinj : Set.InjOn f N := by
    intro p hp q hq hpq
    have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hqA := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    have hpne := (Finset.mem_filter.mp hp).2
    apply Prod.ext
    · by_contra hpqFirst
      exact (connection_product_ne_of_invClosedCayley_not_containsC4
        (· ∈ A) hinv hone hfree hpA.1 hpA.2 hqA.1 hqA.2
        hpqFirst hpne) hpq
    · have hfirst : p.1 = q.1 := by
        by_contra hpqFirst
        exact (connection_product_ne_of_invClosedCayley_not_containsC4
          (· ∈ A) hinv hone hfree hpA.1 hpA.2 hqA.1 hqA.2
          hpqFirst hpne) hpq
      change p.1 * p.2 = q.1 * q.2 at hpq
      rw [← hfirst] at hpq
      exact mul_left_cancel hpq
  have hused :
      (∑ p ∈ N, MonoidAlgebra.single (f p) (1 : ℤ)) =
        finsetGroupRingIndicator (N.image f) := by
    unfold finsetGroupRingIndicator
    exact (Finset.sum_image
      (f := fun g : Γ => MonoidAlgebra.single g (1 : ℤ)) hinj).symm
  rw [finsetGroupRingIndicator_mul, hsplit, hback, hused]

/-- **Slack-centralizer algebra.**  If a packed square consists of a scalar
identity contribution plus the used products, and the used and unused
products partition the full ambient indicator, then the unused indicator
commutes with the connection indicator.  The only group-specific input is
that the full indicator commutes with the connection indicator. -/
theorem unusedIndicator_commutes_of_square_pack_and_partition
    {R : Type*} [Ring R]
    (a used unused full : R) (n : ℕ)
    (hpack : a * a = n • (1 : R) + used)
    (hpartition : 1 + used + unused = full)
    (hfull : a * full = full * a) :
    a * unused = unused * a := by
  have hused : used = a * a - n • (1 : R) := by
    calc
      used = (n • (1 : R) + used) - n • (1 : R) := by abel
      _ = a * a - n • (1 : R) := by rw [← hpack]
  have hunused : unused = full - 1 - used := by
    calc
      unused = (1 + used + unused) - 1 - used := by abel
      _ = full - 1 - used := by rw [hpartition]
  have hncomm : a * (n • (1 : R)) = (n • (1 : R)) * a := by
    simpa using (Nat.cast_commute n a).eq.symm
  rw [hunused, hused]
  noncomm_ring [hfull, hncomm]

/-- **Cayley slack centralizer.**  The unused nonidentity product indicator
commutes in the integral group ring with the connection-set indicator.  This
is a multiplicity-sensitive constraint on every unused inverse pair, strictly
stronger than inversion closure or the cardinality/parity ledger alone. -/
theorem connectionIndicator_commutes_unusedProducts
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    finsetGroupRingIndicator A *
        finsetGroupRingIndicator (unusedNonidentityConnectionProducts A) =
      finsetGroupRingIndicator (unusedNonidentityConnectionProducts A) *
        finsetGroupRingIndicator A := by
  classical
  let W := (nonbacktrackingConnectionPairs A).image fun p => p.1 * p.2
  have hWsub : W ⊆ Finset.univ.erase (1 : Γ) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_filter.mp hp).2, Finset.mem_univ _⟩
  apply unusedIndicator_commutes_of_square_pack_and_partition
    (a := finsetGroupRingIndicator A)
    (used := finsetGroupRingIndicator W)
    (unused := finsetGroupRingIndicator (unusedNonidentityConnectionProducts A))
    (full := finsetGroupRingIndicator (Finset.univ : Finset Γ))
    (n := A.card)
  · simpa [W] using
      connectionIndicator_sq_eq_backtracking_add_used A hinv hone hfree
  · simpa [W, unusedNonidentityConnectionProducts] using
      finsetGroupRingIndicator_identity_used_unused_partition W hWsub
  · exact (finsetGroupRingIndicator_univ_commute A).symm

/-- **Pointwise slack balance.**  For every target group element `x`, the
number of factorizations `x = a*u` with `a` a connection and `u` unused is
exactly the number of factorizations `x = u*a`.  This is the coefficientwise
form of `connectionIndicator_commutes_unusedProducts`. -/
theorem card_connection_unused_representations_eq_unused_connection
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (x : Γ) :
    (finsetProductRepresentations A
      (unusedNonidentityConnectionProducts A) x).card =
    (finsetProductRepresentations
      (unusedNonidentityConnectionProducts A) A x).card := by
  have hcoeff := congrArg
    (fun z : MonoidAlgebra ℤ Γ => MonoidAlgebra.coeff z x)
    (connectionIndicator_commutes_unusedProducts A hinv hone hfree)
  rw [finsetGroupRingIndicator_mul_coeff_eq_card_representations,
    finsetGroupRingIndicator_mul_coeff_eq_card_representations] at hcoeff
  exact_mod_cast hcoeff

/-- **Slack routing forced by the matching involution.**  Fix an involutory
connection `t`.  Every other connection `s` forces an unused element `u ≠ t`
whose left translate routes `s*t` back into the connection set.  The obvious
candidate `u=t` is forbidden precisely by conjugation separation
`t*s*t ∉ A`. -/
theorem exists_unused_ne_involution_inv_mul_connection_mul_involution_mem
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t s : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (hsA : s ∈ A) (hst : s ≠ t) :
    ∃ u, u ∈ unusedNonidentityConnectionProducts A ∧ u ≠ t ∧
      u⁻¹ * s * t ∈ A := by
  classical
  let U := unusedNonidentityConnectionProducts A
  let x := s * t
  have htU : t ∈ U := by
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_erase.mpr
        ⟨fun ht => hone (ht ▸ htA), Finset.mem_univ _⟩
    · intro htImage
      obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp htImage
      have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hpne := (Finset.mem_filter.mp hp).2
      exact (involution_connection_ne_nonbacktracking_product
        (· ∈ A) hinv hone hfree htsq hpA.1 hpA.2 hpne) hpt
  have hleft : (s, t) ∈ finsetProductRepresentations A U x := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hsA, htU⟩, rfl⟩
  have hbalance :=
    card_connection_unused_representations_eq_unused_connection
      A hinv hone hfree x
  have hrightPos :
      0 < (finsetProductRepresentations U A x).card := by
    rw [← hbalance]
    exact Finset.card_pos.mpr ⟨(s, t), hleft⟩
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hrightPos
  have hpData := Finset.mem_filter.mp hp
  have hpMem := Finset.mem_product.mp hpData.1
  have hprod : p.1 * p.2 = s * t := hpData.2
  have hpNe : p.1 ≠ t := by
    intro hpt
    have hpSecond : p.2 = t * s * t := by
      calc
        p.2 = 1 * p.2 := by simp
        _ = (t * t) * p.2 := by rw [htsq]
        _ = t * (t * p.2) := by simp [mul_assoc]
        _ = t * (s * t) := by rw [← hprod, hpt]
        _ = t * s * t := by simp [mul_assoc]
    exact (involution_conjugate_not_mem_connection
      A hinv hone hfree htA htsq hsA hst)
      (hpSecond ▸ hpMem.2)
  refine ⟨p.1, hpMem.1, hpNe, ?_⟩
  have hpSecond : p.1⁻¹ * s * t = p.2 := by
    calc
      p.1⁻¹ * s * t = p.1⁻¹ * (s * t) := by simp [mul_assoc]
      _ = p.1⁻¹ * (p.1 * p.2) := by rw [hprod]
      _ = p.2 := by simp [mul_assoc]
  exact hpSecond ▸ hpMem.2

/-- A slack route can re-enter the connection set only through its source
generator.  This is a direct application of nonbacktracking Sidon
injectivity to the two connection words `s*t` and
`u*(u⁻¹*s*t)`. -/
theorem unused_route_mem_connection_eq_source
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t s u : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (hsA : s ∈ A) (hst : s ≠ t)
    (huA : u ∈ A) (hroute : u⁻¹ * s * t ∈ A) :
    u = s := by
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right htsq).symm
  have hstProd : s * t ≠ 1 := by
    intro h
    apply hst
    calc
      s = t⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = t := htinv
  by_contra hus
  have hcollision : s * t = u * (u⁻¹ * s * t) := by
    simp [mul_assoc]
  exact (connection_product_ne_of_invClosedCayley_not_containsC4
    (· ∈ A) hinv hone hfree hsA htA huA hroute (Ne.symm hus) hstProd)
    hcollision

/-- Consequently, a connection generator which is not itself unused must
route through a genuinely external unused element. -/
theorem exists_external_unused_route_of_connection_not_unused
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t s : Γ} (htA : t ∈ A) (htsq : t * t = 1)
    (hsA : s ∈ A) (hst : s ≠ t)
    (hsUsed : s ∉ unusedNonidentityConnectionProducts A) :
    ∃ u, u ∈ unusedNonidentityConnectionProducts A ∧ u ∉ A ∧
      u⁻¹ * s * t ∈ A := by
  obtain ⟨u, huUnused, _hut, hroute⟩ :=
    exists_unused_ne_involution_inv_mul_connection_mul_involution_mem
      A hinv hone hfree htA htsq hsA hst
  refine ⟨u, huUnused, ?_, hroute⟩
  intro huA
  have hus : u = s := unused_route_mem_connection_eq_source
    A hinv hone hfree htA htsq hsA hst huA hroute
  exact hsUsed (hus ▸ huUnused)

/-- **Plane-minus-two external slack.**  Since `#A=q` while the unused slack
has only `q-2` elements, at least one generator is represented rather than
unused.  Relative to any involutory generator `t`, its forced route therefore
produces an unused element lying genuinely outside the connection set. -/
theorem exists_unused_not_mem_connection_of_planeMinusTwo_Cayley
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (q : ℕ) (hq : 3 ≤ q)
    (hcardΓ : Fintype.card Γ = q * q - 1)
    (hcardA : A.card = q)
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1) :
    ∃ u, u ∈ unusedNonidentityConnectionProducts A ∧ u ∉ A := by
  let U := unusedNonidentityConnectionProducts A
  have hcardU : U.card = q - 2 := by
    simpa [U, unusedNonidentityConnectionProducts] using
      card_unused_nonidentity_of_planeMinusTwo_Cayley
        A hinv hone hfree q (by omega) hcardΓ hcardA
  have hnotSubset : ¬ A ⊆ U := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hcardA, hcardU] at hle
    omega
  obtain ⟨s, hsA, hsNotU⟩ := Finset.not_subset.mp hnotSubset
  have hst : s ≠ t := by
    intro hst
    subst s
    exact hsNotU (by
      apply Finset.mem_sdiff.mpr
      constructor
      · exact Finset.mem_erase.mpr
          ⟨fun ht => hone (ht ▸ htA), Finset.mem_univ _⟩
      · intro htImage
        obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp htImage
        have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
        have hpne := (Finset.mem_filter.mp hp).2
        exact (involution_connection_ne_nonbacktracking_product
          (· ∈ A) hinv hone hfree htsq hpA.1 hpA.2 hpne) hpt)
  obtain ⟨u, huU, huA, _hroute⟩ :=
    exists_external_unused_route_of_connection_not_unused
      A hinv hone hfree htA htsq hsA hst hsNotU
  exact ⟨u, huU, huA⟩

/-- In finite-set language, every nonidentity involution in the ambient group
belongs to the unused product slack, whether or not it is a generator. -/
theorem nontrivial_involution_mem_unusedProducts
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t : Γ} (htne : t ≠ 1) (htsq : t * t = 1) :
    t ∈ unusedNonidentityConnectionProducts A := by
  classical
  apply Finset.mem_sdiff.mpr
  constructor
  · exact Finset.mem_erase.mpr ⟨htne, Finset.mem_univ _⟩
  · intro htImage
    obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp htImage
    have hpA := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hpne := (Finset.mem_filter.mp hp).2
    exact (involution_connection_ne_nonbacktracking_product
      (· ∈ A) hinv hone hfree htsq hpA.1 hpA.2 hpne) hpt

/-- In particular, every involutory connection generator lies in the unused
product slack. -/
theorem involution_connection_mem_unusedProducts
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    {t : Γ} (htA : t ∈ A) (htsq : t * t = 1) :
    t ∈ unusedNonidentityConnectionProducts A :=
  nontrivial_involution_mem_unusedProducts A hinv hone hfree
    (fun ht => hone (ht ▸ htA)) htsq

/-- The ambient group's nonidentity involutions. -/
def nontrivialInvolutionFinset
    (Γ : Type*) [Group Γ] [Fintype Γ] [DecidableEq Γ] : Finset Γ :=
  Finset.univ.filter fun t => t ≠ 1 ∧ t * t = 1

/-- Every ambient nontrivial involution is absorbed by the unused slack. -/
theorem nontrivialInvolutionFinset_subset_unusedProducts
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    nontrivialInvolutionFinset Γ ⊆ unusedNonidentityConnectionProducts A := by
  intro t ht
  have ht' := (Finset.mem_filter.mp ht).2
  exact nontrivial_involution_mem_unusedProducts
    A hinv hone hfree ht'.1 ht'.2

/-- At plane-minus-two order, the ambient group has at most `q-2`
nonidentity involutions. -/
theorem card_nontrivialInvolutionFinset_le_of_planeMinusTwo_Cayley
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (q : ℕ) (hq : 2 ≤ q)
    (hcardΓ : Fintype.card Γ = q * q - 1)
    (hcardA : A.card = q) :
    (nontrivialInvolutionFinset Γ).card ≤ q - 2 := by
  calc
    (nontrivialInvolutionFinset Γ).card ≤
        (unusedNonidentityConnectionProducts A).card :=
      Finset.card_le_card
        (nontrivialInvolutionFinset_subset_unusedProducts
          A hinv hone hfree)
    _ = q - 2 := by
      simpa [unusedNonidentityConnectionProducts] using
        card_unused_nonidentity_of_planeMinusTwo_Cayley
          A hinv hone hfree q hq hcardΓ hcardA

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

/-- **Exact parity content of the Cayley slack.**  Inversion pairs every
unused non-involutory product with a distinct unused inverse.  Consequently
the parity of the whole unused slack is exactly the parity of the ambient
nonidentity involutions.  This is the unconditional conclusion available
from inversion symmetry; equality of the two finsets would require ruling
out all of those inverse pairs. -/
theorem card_unusedProducts_modEq_card_nontrivialInvolutions
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone)) :
    (unusedNonidentityConnectionProducts A).card ≡
      (nontrivialInvolutionFinset Γ).card [MOD 2] := by
  classical
  let U := unusedNonidentityConnectionProducts A
  have hmaps : ∀ g ∈ U, g⁻¹ ∈ U := by
    intro g hg
    exact unusedNonidentityConnectionProducts_inv_mem A hinv hg
  have hparity :=
    SpernerTuckerAntipodalParityEngine.card_modEq_card_fixed_of_involution
      U Inv.inv hmaps (by intro g _; exact inv_inv g)
  have hfixed :
      U.filter (fun g => g⁻¹ = g) = nontrivialInvolutionFinset Γ := by
    ext g
    constructor
    · intro hg
      have hgU := (Finset.mem_filter.mp hg).1
      have hginv := (Finset.mem_filter.mp hg).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ g, ?_⟩
      constructor
      · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hgU).1).1
      · calc
          g * g = g * g⁻¹ := congrArg (g * ·) hginv.symm
          _ = 1 := mul_inv_cancel g
    · intro hg
      have hg' := (Finset.mem_filter.mp hg).2
      apply Finset.mem_filter.mpr
      refine ⟨nontrivial_involution_mem_unusedProducts
        A hinv hone hfree hg'.1 hg'.2, ?_⟩
      exact (eq_inv_of_mul_eq_one_right hg'.2).symm
  simpa [U, hfixed] using hparity

/-- At plane-minus-two order, the `q-2` slack and the ambient nonidentity
involution count have the same parity.  Together with the cardinal upper
bound, this says that any failure of tight slack occurs in increments of two. -/
theorem planeMinusTwo_sub_two_modEq_card_nontrivialInvolutions
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (q : ℕ) (hq : 2 ≤ q)
    (hcardΓ : Fintype.card Γ = q * q - 1)
    (hcardA : A.card = q) :
    q - 2 ≡ (nontrivialInvolutionFinset Γ).card [MOD 2] := by
  have hcard : (unusedNonidentityConnectionProducts A).card = q - 2 := by
    simpa [unusedNonidentityConnectionProducts] using
      card_unused_nonidentity_of_planeMinusTwo_Cayley
        A hinv hone hfree q hq hcardΓ hcardA
  rw [← hcard]
  exact card_unusedProducts_modEq_card_nontrivialInvolutions
    A hinv hone hfree

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

/-- Every C4-free odd-degree Cayley graph of degree greater than one exhibits
a noncentral involution already inside its connection set. -/
theorem exists_noncentral_involution_generator_of_odd_card
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hfree : ¬ containsC4 Γ
      (invClosedCayleyGraph (· ∈ A) hinv hone))
    (hodd : Odd A.card) (hcard : 1 < A.card) :
    ∃ t s, t ∈ A ∧ s ∈ A ∧ t * t = 1 ∧ t * s ≠ s * t := by
  obtain ⟨t, htA, _htne, htsq⟩ :=
    exists_connection_involution_of_odd_card A hinv hone hodd
  have hEraseCard : (A.erase t).card = A.card - 1 :=
    Finset.card_erase_of_mem htA
  have hErasePos : 0 < (A.erase t).card := by
    rw [hEraseCard]
    omega
  obtain ⟨s, hsErase⟩ := Finset.card_pos.mp hErasePos
  have hsA : s ∈ A := Finset.mem_of_mem_erase hsErase
  have hst : s ≠ t := (Finset.mem_erase.mp hsErase).1
  exact ⟨t, s, htA, hsA, htsq,
    involution_generator_not_commute
      A hinv hone hfree htA htsq hsA hst⟩

/-- Therefore any group in which every involution is central admits no
C4-free inverse-closed Cayley graph of odd degree greater than one. -/
theorem containsC4_of_odd_connection_card_of_all_involutions_central
    {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (A : Finset Γ)
    (hinv : ∀ g, g ∈ A ↔ g⁻¹ ∈ A)
    (hone : (1 : Γ) ∉ A)
    (hodd : Odd A.card) (hcard : 1 < A.card)
    (hcentral : ∀ t : Γ, t * t = 1 → ∀ s : Γ, t * s = s * t) :
    containsC4 Γ (invClosedCayleyGraph (· ∈ A) hinv hone) := by
  by_contra hfree
  obtain ⟨t, s, _htA, _hsA, htsq, hnoncomm⟩ :=
    exists_noncentral_involution_generator_of_odd_card
      A hinv hone hfree hodd hcard
  exact hnoncomm (hcentral t htsq s)

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
#print axioms Erdos85.involution_conjugate_not_mem_connection
#print axioms Erdos85.involution_generator_not_commute
#print axioms Erdos85.erase_involution_disjoint_conjugate_shore
#print axioms Erdos85.card_erase_involution_union_conjugate_shore
#print axioms Erdos85.exists_noncentral_involution_generator_of_odd_card
#print axioms Erdos85.containsC4_of_odd_connection_card_of_all_involutions_central
#print axioms Erdos85.nonbacktracking_connectionProduct_injective
#print axioms Erdos85.not_containsC4_iff_nonbacktracking_connectionProduct_injective
#print axioms Erdos85.involution_connection_ne_nonbacktracking_product
#print axioms Erdos85.card_nonbacktrackingConnectionPairs
#print axioms Erdos85.card_nonbacktracking_connectionProducts
#print axioms Erdos85.card_unused_nonidentity_of_planeMinusTwo_Cayley
#print axioms Erdos85.finsetGroupRingIndicator_univ_commute
#print axioms Erdos85.connectionIndicator_sq_eq_backtracking_add_used
#print axioms Erdos85.connectionIndicator_commutes_unusedProducts
#print axioms Erdos85.finsetGroupRingIndicator_mul_coeff_eq_card_representations
#print axioms Erdos85.card_connection_unused_representations_eq_unused_connection
#print axioms Erdos85.exists_unused_ne_involution_inv_mul_connection_mul_involution_mem
#print axioms Erdos85.unused_route_mem_connection_eq_source
#print axioms Erdos85.exists_external_unused_route_of_connection_not_unused
#print axioms Erdos85.exists_unused_not_mem_connection_of_planeMinusTwo_Cayley
#print axioms Erdos85.nontrivial_involution_mem_unusedProducts
#print axioms Erdos85.involution_connection_mem_unusedProducts
#print axioms Erdos85.nontrivialInvolutionFinset_subset_unusedProducts
#print axioms Erdos85.card_nontrivialInvolutionFinset_le_of_planeMinusTwo_Cayley
#print axioms Erdos85.unusedNonidentityConnectionProducts_inv_mem
#print axioms Erdos85.card_unusedProducts_modEq_card_nontrivialInvolutions
#print axioms Erdos85.planeMinusTwo_sub_two_modEq_card_nontrivialInvolutions
#print axioms Erdos85.exists_unused_nontrivial_involution_of_odd_card
#print axioms Erdos85.exists_unused_involution_of_odd_planeMinusTwo_Cayley
#print axioms Erdos85.exists_connection_involution_of_odd_card
#print axioms Erdos85.exists_connection_perfectMatchingLayer_of_odd_card
#print axioms Erdos85.mem_erase_involution_iff_inv_mem_erase
#print axioms Erdos85.invClosedCayley_erase_involution_adj_iff
#print axioms Erdos85.invClosedCayley_erase_involution_not_containsC4
#print axioms Erdos85.invClosedCayley_erase_involution_degree
#print axioms Erdos85.exists_c4Free_evenResidual_matchingDecomposition_of_odd_Cayley
