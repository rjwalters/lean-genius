/-
# Inverse Galois Problem: Generalizing X⁴-2 to Xⁿ-p (open question inverse-galois-d4-oq-02)

The base entry `Proofs.InverseGaloisD4` computes `|Gal(X⁴-2/ℚ)| = 8`, identifying the
Galois group with the dihedral group `D₄`.  The open question asks for the general
picture: for a prime `p`, the Galois group of `Xⁿ - p` over `ℚ` is *metacyclic* of order
`n·φ(n)` under genericity — it sits in a split exact sequence

      1 → Cₙ → Gal(Xⁿ-p/ℚ) → (ℤ/nℤ)ˣ → 1,

the kernel `Cₙ` permuting the roots `α·ζⁱ` by translating `i`, and the quotient
`(ℤ/nℤ)ˣ ≅ Gal(ℚ(ζₙ)/ℚ)` acting on the roots of unity.

This file establishes the two-sided divisibility bracket that pins the order of this group:

      n  ∣  |Gal(Xⁿ-p/ℚ)|  ∣  n!         (`n_dvd_gal_card`, `gal_card_dvd_factorial`)

and, on the metacyclic side, the cyclotomic lower factor

      φ(n)  ∣  |Gal(Xⁿ-p/ℚ)|             (`totient_dvd_gal_card`)

obtained from the cyclotomic subfield `ℚ(ζₙ) ⊆ ℚ(roots)`, of degree `φ(n)`.  These three
divisibilities directly generalize the base entry's `four_dvd_x4_sub_2_gal_card`
(`n = 4`: `4 ∣ |Gal|`) and `x4_sub_2_gal_card_dvd_24` (`|Gal| ∣ 24 = 4!`), and add the
new `(ℤ/nℤ)ˣ`-quotient witness `φ(n) ∣ |Gal|`.  For `n = 4` they read
`4 ∣ |Gal|`, `|Gal| ∣ 24`, `φ(4)=2 ∣ |Gal|`, consistent with the known `|Gal| = 8`.

Because the kernel order `n` and quotient order `φ(n)` divide `|Gal|` *simultaneously*,
their least common multiple does too (`lcm_dvd_gal_card`):

      lcm(n, φ(n))  ∣  |Gal(Xⁿ-p/ℚ)|.

When the two are coprime (`gcd(n, φ(n)) = 1`) this sharpens to the *full* generic
metacyclic order `n·φ(n) ∣ |Gal|` (`mul_totient_dvd_gal_card_of_coprime`), which is the
exact group order for the smallest such cases: `n = 3` gives `6 = |S₃|` and `n = 5` gives
`20 = |F₂₀|`.  (The base `n = 4` is excluded since `gcd(4, 2) = 2`, matching `lcm = 4 < 8`.)

Irreducibility of `Xⁿ - p` over `ℚ` is Eisenstein at `p` (valid for every `n ≥ 1`,
prime `p`), reusing `NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime`.  The two outer
bounds reuse the base entry's `irred_monic_degree_dvd_splitting_finrank` and the
`galActionHom` embedding into `Sₙ`; the cyclotomic factor uses that `ℚ(ζₙ)` is a
subfield of the splitting field with `[ℚ(ζₙ):ℚ] = φ(n)`.

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- Part I: Basic facts about Xⁿ - p for prime p
-- ============================================================================

/-- `Xⁿ - p` is irreducible over `ℚ` for prime `p` and `n ≥ 2`, via Eisenstein at `p`. -/
theorem x_pow_sub_prime_irreducible (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime n p hn hp

/-- `Xⁿ - p` has degree `n`. -/
theorem x_pow_sub_prime_natDegree (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) :
    (X ^ n - C (p : ℚ) : ℚ[X]).natDegree = n :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq hn (by exact_mod_cast hp.ne_zero)

/-- `Xⁿ - p` is monic. -/
theorem x_pow_sub_prime_monic (n p : ℕ) (hn : 1 ≤ n) :
    (X ^ n - C (p : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C _ (by omega)

/-- `Xⁿ - p` is separable (irreducible in characteristic 0). -/
theorem x_pow_sub_prime_separable (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    (X ^ n - C (p : ℚ) : ℚ[X]).Separable :=
  (x_pow_sub_prime_irreducible n p hn hp).separable

-- ============================================================================
-- Part II: The lower factor n ∣ |Gal| (irreducible degree divides the order)
-- ============================================================================

/-- **`n ∣ |Gal(Xⁿ-p/ℚ)|`.** The degree of the irreducible polynomial `Xⁿ - p`
divides the order of its Galois group: adjoining a single root gives an intermediate
field of degree `n`, which divides the full splitting-field degree `= |Gal|`.

Generalizes the base entry's `four_dvd_x4_sub_2_gal_card` (`n = 4`). -/
theorem n_dvd_gal_card (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    n ∣ Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal := by
  have hcard := Polynomial.Gal.card_of_separable (x_pow_sub_prime_separable n p hn hp)
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  have hdvd := irred_monic_degree_dvd_splitting_finrank
    (x_pow_sub_prime_irreducible n p hn hp) (x_pow_sub_prime_monic n p (by omega))
  rwa [x_pow_sub_prime_natDegree n p (by omega) hp] at hdvd

-- ============================================================================
-- Part III: The upper bound |Gal| ∣ n! (embedding into Sₙ via the root action)
-- ============================================================================

/-- **`|Gal(Xⁿ-p/ℚ)| ∣ n!`.** The Galois group embeds into the symmetric group `Sₙ`
on the `n` roots, so its order divides `n!`.

Generalizes the base entry's `x4_sub_2_gal_card_dvd_24` (`n = 4`, `24 = 4!`). -/
theorem gal_card_dvd_factorial (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal ∣ n.factorial := by
  set q := (X ^ n - C (p : ℚ) : ℚ[X]) with hq
  haveI : Fact (map (algebraMap ℚ q.SplittingField) q).Splits :=
    ⟨Polynomial.SplittingField.splits q⟩
  haveI : DecidableEq (↥(q.rootSet q.SplittingField)) := Classical.typeDecidableEq _
  have hinj := Polynomial.Gal.galActionHom_injective q q.SplittingField
  have hdvd : Nat.card q.Gal ∣ Nat.card (Equiv.Perm (q.rootSet q.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hdvd
  have hcard : Fintype.card (q.rootSet q.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree (x_pow_sub_prime_separable n p hn hp)
        (Polynomial.SplittingField.splits q)]
    exact x_pow_sub_prime_natDegree n p (by omega) hp
  rwa [hcard] at hdvd

-- ============================================================================
-- Part IV: The cyclotomic factor φ(n) ∣ |Gal|  (the metacyclic quotient witness)
-- ============================================================================

/-- **`φ(n) ∣ |Gal(Xⁿ-p/ℚ)|`.** The splitting field `L` of `Xⁿ - p` contains a
primitive `n`-th root of unity: the `n` distinct roots `β` all satisfy `βⁿ = p`, so
their ratios `β/α` (for a fixed root `α`) give `n` distinct `n`-th roots of unity in
`L`.  Hence `ℚ(ζₙ) ⊆ L` with `[ℚ(ζₙ):ℚ] = φ(n)`, and the tower law forces
`φ(n) ∣ [L:ℚ] = |Gal|`.

This is the cyclotomic lower factor of the metacyclic order `n·φ(n)`: it witnesses the
quotient `Gal(Xⁿ-p/ℚ) ↠ Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)ˣ`.  Together with `n_dvd_gal_card` it
pins both factors of `n·φ(n)` from below.  For `n = 4`: `φ(4) = 2 ∣ 8 = |Gal(X⁴-2)|`. -/
theorem totient_dvd_gal_card (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    n.totient ∣ Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  set q := (X ^ n - C (p : ℚ) : ℚ[X]) with hq
  have hsep := x_pow_sub_prime_separable n p hn hp
  have hsplit := Polynomial.SplittingField.splits q
  -- |Gal| = [L:ℚ]
  have hgal : Fintype.card q.Gal = Module.finrank ℚ q.SplittingField := by
    have h := Polynomial.Gal.card_of_separable hsep
    rwa [Nat.card_eq_fintype_card] at h
  rw [hgal]
  haveI : CharZero q.SplittingField := inferInstance
  have hp_ne : (p : q.SplittingField) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  -- the n roots of q in L
  have hcardroot : Fintype.card (q.rootSet q.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep hsplit,
      x_pow_sub_prime_natDegree n p (by omega) hp]
  -- every root β has βⁿ = p
  have root_pow : ∀ β ∈ q.rootSet q.SplittingField, β ^ n = (p : q.SplittingField) := by
    intro β hβ
    have h0 := (Polynomial.mem_rootSet.mp hβ).2
    simp only [hq, map_sub, map_pow, aeval_X, aeval_C] at h0
    rw [map_natCast] at h0
    exact sub_eq_zero.mp h0
  -- fix a root α; it is nonzero since αⁿ = p ≠ 0
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcardroot]; omega)
  have hαpow : α ^ n = (p : q.SplittingField) := root_pow α hα_mem
  have hα0 : α ≠ 0 := by
    intro h; apply hp_ne; rw [← hαpow, h, zero_pow (by omega : n ≠ 0)]
  -- the map β ↦ β/α injects the n roots into the n-th roots of unity in L
  have hge : n ≤ Fintype.card (rootsOfUnity n q.SplittingField) := by
    have hle : Fintype.card (q.rootSet q.SplittingField)
        ≤ Fintype.card (rootsOfUnity n q.SplittingField) := by
      refine Fintype.card_le_of_injective
        (fun β : q.rootSet q.SplittingField =>
          rootsOfUnity.mkOfPowEq (β.1 / α) (by
            rw [div_pow, root_pow β.1 β.2, hαpow, div_self hp_ne])) ?_
      intro β₁ β₂ h
      have hcoe := congrArg
        (fun u : rootsOfUnity n q.SplittingField =>
          ((u : (q.SplittingField)ˣ) : q.SplittingField)) h
      simp only [rootsOfUnity.coe_mkOfPowEq] at hcoe
      rw [div_eq_div_iff hα0 hα0] at hcoe
      exact Subtype.ext (mul_right_cancel₀ hα0 hcoe)
    rwa [hcardroot] at hle
  -- so L has enough roots of unity: a primitive n-th root ζ exists
  haveI : HasEnoughRootsOfUnity q.SplittingField n := HasEnoughRootsOfUnity.of_card_le hge
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot q.SplittingField n
  -- ℚ(ζ) has degree φ(n) and sits inside L; tower law gives φ(n) ∣ [L:ℚ]
  have hζ_int : IsIntegral ℚ ζ := .of_finite ℚ ζ
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have hmin : cyclotomic n ℚ = minpoly ℚ ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (by omega))
  set F := IntermediateField.adjoin ℚ ({ζ} : Set q.SplittingField) with hF
  have hF_finrank : Module.finrank ℚ F = n.totient := by
    rw [IntermediateField.adjoin.finrank hζ_int, ← hmin, natDegree_cyclotomic]
  have htower := Module.finrank_mul_finrank ℚ F q.SplittingField
  rw [hF_finrank] at htower
  exact ⟨_, htower.symm⟩

-- ============================================================================
-- Part V: Combining the two lower factors — lcm(n, φ(n)) ∣ |Gal|
-- ============================================================================

/-- **`lcm(n, φ(n)) ∣ |Gal(Xⁿ-p/ℚ)|`.** The two lower factors `n` (kernel `Cₙ`) and
`φ(n)` (quotient `(ℤ/nℤ)ˣ`) divide `|Gal|` *simultaneously*, so their least common
multiple does too.  This is the sharpest lower bound on `|Gal|` obtainable from the
metacyclic kernel/quotient pair alone, strictly improving on each factor separately
whenever `gcd(n, φ(n)) > 1`.

For `n = 4`: `lcm(4, φ(4)) = lcm(4, 2) = 4 ∣ 8 = |Gal(X⁴-2)|` (here the two factors
share the prime `2`, so the lcm `4` is below the true order `8 = 4·φ(4)`). -/
theorem lcm_dvd_gal_card (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    Nat.lcm n n.totient ∣ Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal :=
  Nat.lcm_dvd (n_dvd_gal_card n p hn hp) (totient_dvd_gal_card n p hn hp)

/-- **`n·φ(n) ∣ |Gal(Xⁿ-p/ℚ)|` when `gcd(n, φ(n)) = 1`.** If the kernel order `n` and
the quotient order `φ(n)` are coprime, the two divisibilities combine into the *full*
generic metacyclic order `n·φ(n)` as a lower bound — pinning `|Gal|` from below by the
conjectured exact value.  Combined with the embedding `|Gal| ∣ n!` this squeezes the
order tightly for all such `n`.

This is exact for the smallest coprime cases:
* `n = 3`: `gcd(3, 2) = 1`, lower bound `6 = |S₃| = |Gal(X³-p)|`;
* `n = 5`: `gcd(5, 4) = 1`, lower bound `20 = |F₂₀| = |Gal(X⁵-p)|` (the Frobenius group).
(The base entry `n = 4` is *excluded*: `gcd(4, 2) = 2 ≠ 1`, consistent with `lcm = 4 < 8`.) -/
theorem mul_totient_dvd_gal_card_of_coprime (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hcop : Nat.Coprime n n.totient) :
    n * n.totient ∣ Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal :=
  hcop.mul_dvd_of_dvd_of_dvd (n_dvd_gal_card n p hn hp) (totient_dvd_gal_card n p hn hp)

/-- `6 ∣ |Gal(X³-p/ℚ)|` for every prime `p`, matching the known `Gal(X³-p) ≅ S₃`. -/
example (p : ℕ) (hp : p.Prime) :
    (6 : ℕ) ∣ Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal := by
  have ht : (3 : ℕ).totient = 2 := by decide
  have h := mul_totient_dvd_gal_card_of_coprime 3 p (by norm_num) hp (by decide)
  simpa [ht] using h

/-- `20 ∣ |Gal(X⁵-p/ℚ)|` for every prime `p`, matching the known `Gal(X⁵-p) ≅ F₂₀`. -/
example (p : ℕ) (hp : p.Prime) :
    (20 : ℕ) ∣ Fintype.card (X ^ 5 - C (p : ℚ) : ℚ[X]).Gal := by
  have ht : (5 : ℕ).totient = 4 := by decide
  have h := mul_totient_dvd_gal_card_of_coprime 5 p (by norm_num) hp (by decide)
  simpa [ht] using h

-- ============================================================================
-- Part VI: Exact order in the smallest fully determined case (n = 3)
-- ============================================================================

/-- **Exact order `|Gal(X³-p/ℚ)| = 6` for every prime `p`.**  The two outer bounds of
this file close to an *equality* in the case `n = 3`: the factorial embedding gives the
upper bound `|Gal| ∣ 3! = 6`, while the coprime metacyclic lower bound gives
`6 = 3·φ(3) ∣ |Gal|` (here `gcd(3, φ(3)) = gcd(3, 2) = 1`).  Divisibility antisymmetry
forces `|Gal| = 6`, matching the known `Gal(X³-p/ℚ) ≅ S₃`.

This is the first `n` for which the divisibility bracket of this file pins the order
exactly with no extra hypotheses: `n·φ(n) = 6 = n!`, so the metacyclic lower bound and the
`Sₙ`-embedding upper bound coincide.  (For `n = 5` the lower bound `20` and upper bound
`120 = 5!` leave a gap, so equality there needs the genericity upper bound `|Gal| ≤ n·φ(n)`
— the remaining open question; for `n = 4` the factors are not coprime.) -/
theorem gal_card_X3_sub_prime (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal = 6 := by
  -- Upper bound: |Gal| ∣ 3! = 6 from the symmetric-group embedding.
  have hupper : Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal ∣ 6 := by
    have h := gal_card_dvd_factorial 3 p (by norm_num) hp
    rwa [show (3 : ℕ).factorial = 6 from rfl] at h
  -- Lower bound: 6 = 3·φ(3) ∣ |Gal| from the coprime metacyclic bracket.
  have hlower : (6 : ℕ) ∣ Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal := by
    have ht : (3 : ℕ).totient = 2 := by decide
    have h := mul_totient_dvd_gal_card_of_coprime 3 p (by norm_num) hp (by decide)
    simpa [ht] using h
  exact Nat.dvd_antisymm hupper hlower

end InverseGaloisExtensions
