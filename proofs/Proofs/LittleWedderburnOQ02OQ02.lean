import Mathlib

/-
# Gauss's necklace formula: counting monic irreducible polynomials over a finite field

The parent entry (`LittleWedderburnOQ02`) classified finite fields: for every prime power
`q = p ^ n` there is, up to isomorphism, a unique field `GF(q)` of that order.  This entry
answers the second open question raised there:

> Count the monic irreducible polynomials of each degree over `𝔽_p` by Möbius inversion of
> the classification.

Write `N(d)` for the number of monic irreducible polynomials of degree `d` over `𝔽_p`.
Every element `x` of `GF(p ^ n)` has a monic irreducible minimal polynomial whose degree
divides `n`, and conversely every monic irreducible of degree `d ∣ n` is the minimal
polynomial of exactly `d` elements of `GF(p ^ n)` (its distinct conjugates).  Partitioning
`GF(p ^ n)` by minimal polynomial therefore gives **Gauss's degree identity**

  `p ^ n = ∑_{d ∣ n} d · N(d)`,

and Möbius inversion turns this into the **necklace / Gauss formula**

  `n · N(n) = ∑_{d ∣ n} μ(n / d) · p ^ d`.

The only nontrivial inputs are standard finite-field facts already in Mathlib: a finite field
is a separable normal (Galois) extension of its prime subfield, so a minimal polynomial splits
there with exactly `deg` distinct roots; and `GF(p ^ d)` embeds in `GF(p ^ n)` whenever `d ∣ n`,
so every monic irreducible of degree `d ∣ n` acquires a root.  We realise `N(d)` concretely as
the number of distinct degree-`d` minimal polynomials occurring in `GF(p ^ d)` and prove this
count is the same whichever field `GF(p ^ n)` (`d ∣ n`) we read it off — the ambient
independence that makes the Möbius inversion meaningful.

Everything is fully machine-checked with no axioms or sorries.
-/

open Polynomial Finset

namespace LittleWedderburnOQ0202

variable (p : ℕ) [Fact p.Prime]

noncomputable local instance instDecEqPoly : DecidableEq ((ZMod p)[X]) := Classical.decEq _
noncomputable local instance instFintypeGF (m : ℕ) : Fintype (GaloisField p m) := Fintype.ofFinite _
noncomputable local instance instDecEqGF (m : ℕ) : DecidableEq (GaloisField p m) := Classical.decEq _

/-- `Nfield p m d` is the number of distinct degree-`d` minimal polynomials realised by
elements of `GF(p ^ m)`. -/
noncomputable def Nfield (m d : ℕ) : ℕ :=
  (((univ : Finset (GaloisField p m)).image (minpoly (ZMod p))).filter
    (fun g => g.natDegree = d)).card

/-! ## The per-field degree partition -/

/-- A monic irreducible polynomial occurring as a minimal polynomial of `GF(p ^ m)` has exactly
`deg` distinct roots there: the elements sharing a given minimal polynomial number `deg`. -/
lemma card_minpoly_fiber {m : ℕ} (x : GaloisField p m) :
    ((univ : Finset (GaloisField p m)).filter
      (fun y => minpoly (ZMod p) y = minpoly (ZMod p) x)).card
      = (minpoly (ZMod p) x).natDegree := by
  have hxI : IsIntegral (ZMod p) x := Algebra.IsIntegral.isIntegral x
  set g := minpoly (ZMod p) x with hg
  have hgmonic : g.Monic := minpoly.monic hxI
  have hgirr : Irreducible g := minpoly.irreducible hxI
  have hgsep : g.Separable := Algebra.IsSeparable.isSeparable (ZMod p) x
  set φ := algebraMap (ZMod p) (GaloisField p m) with hφ
  have hsplit : (g.map φ).Splits := Normal.splits inferInstance x
  have hmapne : g.map φ ≠ 0 := by simpa [hφ] using (hgmonic.map φ).ne_zero
  have hset : ((univ : Finset (GaloisField p m)).filter
      (fun y => minpoly (ZMod p) y = g)) = (g.map φ).roots.toFinset := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset, mem_roots hmapne,
      IsRoot.def, eval_map]
    constructor
    · intro hy
      have h0 : aeval y (minpoly (ZMod p) y) = 0 := minpoly.aeval _ _
      rw [hy] at h0
      rwa [← aeval_def]
    · intro hy
      rw [← aeval_def] at hy
      exact (minpoly.eq_of_irreducible_of_monic hgirr hy hgmonic).symm
  rw [hset, Multiset.toFinset_card_of_nodup (nodup_roots (hgsep.map)),
    ← hsplit.natDegree_eq_card_roots, hgmonic.natDegree_map φ]

/-- The degree of every minimal polynomial of `GF(p ^ m)` divides `m`. -/
lemma mdeg_dvd {m : ℕ} (hm : m ≠ 0) (x : GaloisField p m) :
    (minpoly (ZMod p) x).natDegree ∣ m := by
  have hxI : IsIntegral (ZMod p) x := Algebra.IsIntegral.isIntegral x
  have key : (minpoly (ZMod p) x).natDegree ∣ Module.finrank (ZMod p) (GaloisField p m) := by
    rw [← IntermediateField.adjoin.finrank hxI]
    exact ⟨_, (Module.finrank_mul_finrank (ZMod p) _ (GaloisField p m)).symm⟩
  rwa [GaloisField.finrank p hm] at key

/-- **Gauss's degree identity (per field).** `p ^ m = ∑_{d ∣ m} d · N(m, d)`. -/
theorem degree_identity_field (m : ℕ) (hm : m ≠ 0) :
    p ^ m = ∑ d ∈ m.divisors, d * Nfield p m d := by
  have hcard : Fintype.card (GaloisField p m) = p ^ m := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p m hm
  have hmaps : ∀ x ∈ (univ : Finset (GaloisField p m)),
      minpoly (ZMod p) x ∈ (univ : Finset (GaloisField p m)).image (minpoly (ZMod p)) :=
    fun x _ => mem_image_of_mem _ (mem_univ x)
  have hstep : Fintype.card (GaloisField p m)
      = ∑ g ∈ (univ : Finset (GaloisField p m)).image (minpoly (ZMod p)), g.natDegree := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl ?_
    intro g hg
    rw [mem_image] at hg
    obtain ⟨x, _, rfl⟩ := hg
    exact card_minpoly_fiber p x
  have hdvd : ∀ g ∈ (univ : Finset (GaloisField p m)).image (minpoly (ZMod p)),
      g.natDegree ∈ m.divisors := by
    intro g hg
    rw [mem_image] at hg
    obtain ⟨x, _, rfl⟩ := hg
    exact Nat.mem_divisors.mpr ⟨mdeg_dvd p hm x, hm⟩
  rw [← hcard, hstep, ← Finset.sum_fiberwise_of_maps_to hdvd]
  refine Finset.sum_congr rfl ?_
  intro d _
  have h1 : ∑ g ∈ ((univ : Finset (GaloisField p m)).image (minpoly (ZMod p))).filter
        (fun g => g.natDegree = d), g.natDegree
      = ∑ _g ∈ ((univ : Finset (GaloisField p m)).image (minpoly (ZMod p))).filter
        (fun g => g.natDegree = d), d :=
    Finset.sum_congr rfl (fun g hg => (mem_filter.mp hg).2)
  rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ## Ambient independence of the count -/

/-- If `d ∣ k` then every monic irreducible of degree `d` has a root in `GF(p ^ k)`:
`𝔽_p[X]/(g) ≅ GF(p ^ d)` embeds into `GF(p ^ k)`. -/
lemma exists_root_of_dvd (k d : ℕ) (hk : k ≠ 0) (hd : d ∣ k) {g : (ZMod p)[X]}
    (hmonic : g.Monic) (hirr : Irreducible g) (hdeg : g.natDegree = d) :
    ∃ y : GaloisField p k, aeval y g = 0 := by
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hfr : Module.finrank (ZMod p) (AdjoinRoot g) = d := by
    rw [(AdjoinRoot.powerBasis hmonic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hdvd : Module.finrank (ZMod p) (AdjoinRoot g) ∣
      Module.finrank (ZMod p) (GaloisField p k) := by
    rw [hfr, GaloisField.finrank p hk]; exact hd
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  have hroot : aeval (AdjoinRoot.root g) g = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.eval₂_root g
  exact ⟨φ (AdjoinRoot.root g), by rw [aeval_algHom_apply, hroot, map_zero]⟩

/-- Membership in the degree-`d` minimal-polynomial image of `GF(p ^ k)` (when `d ∣ k`,
`d ≠ 0`) is exactly being a monic irreducible of degree `d`. -/
lemma mem_image_filter_iff (k d : ℕ) (hk : k ≠ 0) (hd : d ∣ k)
    (g : (ZMod p)[X]) :
    g ∈ ((univ : Finset (GaloisField p k)).image (minpoly (ZMod p))).filter
      (fun g => g.natDegree = d) ↔ (g.Monic ∧ Irreducible g ∧ g.natDegree = d) := by
  rw [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨x, _, rfl⟩, hdeg⟩
    exact ⟨minpoly.monic (Algebra.IsIntegral.isIntegral x),
      minpoly.irreducible (Algebra.IsIntegral.isIntegral x), hdeg⟩
  · rintro ⟨hmonic, hirr, hdeg⟩
    obtain ⟨y, hy⟩ := exists_root_of_dvd p k d hk hd hmonic hirr hdeg
    exact ⟨⟨y, mem_univ y, (minpoly.eq_of_irreducible_of_monic hirr hy hmonic).symm⟩, hdeg⟩

/-- **Ambient independence.** For `d ∣ m` the degree-`d` count read off `GF(p ^ m)` agrees with
the one read off `GF(p ^ d)`. -/
lemma Nfield_eq (m d : ℕ) (hm : m ≠ 0) (hd : d ∣ m) (hd0 : d ≠ 0) :
    Nfield p m d = Nfield p d d := by
  have e : ((univ : Finset (GaloisField p m)).image (minpoly (ZMod p))).filter
        (fun g => g.natDegree = d)
      = ((univ : Finset (GaloisField p d)).image (minpoly (ZMod p))).filter
        (fun g => g.natDegree = d) := by
    ext g
    rw [mem_image_filter_iff p m d hm hd g, mem_image_filter_iff p d d hd0 (dvd_refl d) g]
  simp only [Nfield, e]

/-- The intrinsic count: the number of monic irreducible polynomials of degree `n` over `𝔽_p`. -/
noncomputable def Nirr (n : ℕ) : ℕ := Nfield p n n

/-- **Gauss's degree identity.** `p ^ m = ∑_{d ∣ m} d · N(d)` with the intrinsic count `N`. -/
theorem degree_identity (m : ℕ) (hm : m ≠ 0) :
    p ^ m = ∑ d ∈ m.divisors, d * Nirr p d := by
  rw [degree_identity_field p m hm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [Nirr, Nfield_eq p m d hm hdvd hd0]

/-! ## Möbius inversion: the necklace formula -/

/-- **Gauss's necklace formula.** `n · N(n) = ∑_{d ∣ n} μ(n / d) · p ^ d`, expressed via the
divisor antidiagonal `(a, b)` with `a * b = n` (so `a = n / d`, `b = d`). -/
theorem necklace_formula (n : ℕ) (hn : n ≠ 0) :
    (n : ℤ) * Nirr p n
      = ∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ) * (p : ℤ) ^ x.2 := by
  have hfwd : ∀ k > 0, ∑ d ∈ k.divisors, ((d * Nirr p d : ℕ) : ℤ) = (p : ℤ) ^ k := by
    intro k hk
    rw [← Nat.cast_sum, ← degree_identity p k hk.ne', Nat.cast_pow]
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun d => ((d * Nirr p d : ℕ) : ℤ)) (g := fun n => (p : ℤ) ^ n)).mp hfwd n
      (Nat.pos_of_ne_zero hn)
  rw [Nat.cast_mul] at key
  exact key.symm

end LittleWedderburnOQ0202
