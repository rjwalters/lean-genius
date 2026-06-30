/-
# Inverse Galois: the metacyclic upper bound `|Gal(Xⁿ-p)| ≤ n·φ(n)`
  (inverse-galois-d4-oq-02-oq-03-oq-01-oq-01)

The parent chain establishes, for a prime `p` and `n ≥ 2`, the lower divisibilities of the
order of `Gal(Xⁿ - p / ℚ)`

      n ∣ |Gal|        (`n_dvd_gal_card`,       the radical/kernel factor `Cₙ`)
      φ(n) ∣ |Gal|     (`totient_dvd_gal_card`,  the cyclotomic/quotient factor `(ℤ/n)ˣ`)
      lcm(n, φ(n)) ∣ |Gal|, and when `gcd(n, φ(n)) = 1` the product `n·φ(n) ∣ |Gal|`
                       (`lcm_dvd_gal_card`, `mul_totient_dvd_gal_card_of_coprime`),

together with the *symmetric-group* upper bound `|Gal| ∣ n!` (`gal_card_dvd_factorial`).
The conjectured metacyclic order under genericity is `n·φ(n)`, the order of the holomorph
`ℤ/n ⋊ (ℤ/n)ˣ`.  The deepest parent entry (`...OQ02OQ03OQ01`) pins the order *exactly* only
at `n = 2, 3`, precisely because there the elementary bracket closes — `n·φ(n) = n!`.  For
`n ≥ 4` the factorial bound has genuine slack (`n·φ(n) < n!`), so the order was left open;
its first listed open question asks for the *matching upper bound* `|Gal| ≤ n·φ(n)` via the
tower `SF = ℚ(ζₙ)(ⁿ√p)`, sharp where the `Sₙ` bound is not (e.g. `n = 5`).

This file supplies that upper bound, **unconditionally** — no genericity / linear-disjointness
hypothesis is needed.

  * `gal_card_le_n_mul_totient`        : `|Gal(Xⁿ-p/ℚ)| ≤ n·φ(n)` for every `n ≥ 2`, prime `p`.
        The splitting field `L` is generated over `ℚ` by a single root `α` and a primitive
        `n`-th root of unity `ζ` (every root is `ζⁱ·α`), so it sits in the tower
        `ℚ ⊆ ℚ(ζ) ⊆ ℚ(ζ)(α) = L` with `[ℚ(ζ):ℚ] = φ(n)` and `[L:ℚ(ζ)] ≤ n` (because `α` is a
        root of the degree-`n` polynomial `Xⁿ - p` over `ℚ(ζ)`).  Multiplying the tower
        degrees gives `[L:ℚ] = |Gal| ≤ n·φ(n)`.  This replaces the weak `n!` bound with the
        metacyclic bound — the missing ceiling of the bracket.

  * `gal_card_eq_n_mul_totient_of_coprime`
                                       : when `gcd(n, φ(n)) = 1` the coprime lower bound
        `n·φ(n) ∣ |Gal|` meets this ceiling, pinning `|Gal(Xⁿ-p/ℚ)| = n·φ(n)` exactly — for
        *every* prime `p`, with no genericity hypothesis.  Unlike the parent's `n = 2, 3`
        squeeze (which used the factorial bound), this works at every coprime degree,
        including those where `n·φ(n) < n!`.

  * `gal_card_quintic_eq_twenty`       : the first genuinely-new pin beyond the factorial
        squeeze — `|Gal(X⁵-p/ℚ)| = 20 = |F₂₀|` for every prime `p`.  Here `gcd(5, φ(5)) =
        gcd(5,4) = 1` so `5·φ(5) = 20 ∣ |Gal|`, while the meta-bound gives `|Gal| ≤ 20`; the
        factorial bound `|Gal| ∣ 120` alone could *not* close this (`20 < 120`).  This resolves
        the parent entry's first open question, exhibiting the affine group `F₂₀ = AGL(1,5)`
        as the uniform Galois group of `X⁵ - p`.

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` on the headline theorems
reports only `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02OQ03

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- The metacyclic upper bound  |Gal(Xⁿ-p/ℚ)| ≤ n·φ(n)
-- ============================================================================

/-- **`|Gal(Xⁿ-p/ℚ)| ≤ n·φ(n)`.** The splitting field `L` of `Xⁿ - p` is generated over `ℚ`
by a single root `α` together with a primitive `n`-th root of unity `ζ`: every root `β`
satisfies `(β/α)ⁿ = 1`, hence `β/α = ζⁱ`, so `β = ζⁱ·α ∈ ℚ(ζ, α)`.  Therefore `L = ℚ(ζ)(α)`,
giving the tower

      ℚ  ⊆  ℚ(ζ)  ⊆  ℚ(ζ)(α) = L,     [ℚ(ζ):ℚ] = φ(n),   [L:ℚ(ζ)] ≤ n,

since `α` is a root of the degree-`n` polynomial `Xⁿ - p` already over `ℚ(ζ)`.  Multiplying
the tower degrees, `|Gal| = [L:ℚ] ≤ φ(n)·n = n·φ(n)`.

This is the metacyclic ceiling of the divisibility bracket — strictly better than the
symmetric-group bound `|Gal| ∣ n!` whenever `n·φ(n) < n!` (i.e. `n ≥ 4`), and unconditional
(no genericity hypothesis). -/
theorem gal_card_le_n_mul_totient (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) :
    Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal ≤ n * n.totient := by
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
  set L := q.SplittingField with hLdef
  haveI : CharZero L := inferInstance
  have hp_ne : (p : L) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- the n roots of q in L
  have hcardroot : Fintype.card (q.rootSet L) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep hsplit,
      x_pow_sub_prime_natDegree n p (by omega) hp]
  -- every root β has βⁿ = p
  have root_pow : ∀ β ∈ q.rootSet L, β ^ n = (p : L) := by
    intro β hβ
    have h0 := (Polynomial.mem_rootSet.mp hβ).2
    simp only [hq, map_sub, map_pow, aeval_X, aeval_C] at h0
    rw [map_natCast] at h0
    exact sub_eq_zero.mp h0
  -- fix a root α; it is nonzero since αⁿ = p ≠ 0
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcardroot]; omega)
  have hαpow : α ^ n = (p : L) := root_pow α hα_mem
  have hα0 : α ≠ 0 := by
    intro h; apply hp_ne; rw [← hαpow, h, zero_pow (by omega : n ≠ 0)]
  -- L contains a primitive n-th root of unity ζ
  have hge : n ≤ Fintype.card (rootsOfUnity n L) := by
    have hle : Fintype.card (q.rootSet L) ≤ Fintype.card (rootsOfUnity n L) := by
      refine Fintype.card_le_of_injective
        (fun β : q.rootSet L =>
          rootsOfUnity.mkOfPowEq (β.1 / α) (by
            rw [div_pow, root_pow β.1 β.2, hαpow, div_self hp_ne])) ?_
      intro β₁ β₂ h
      have hcoe := congrArg
        (fun u : rootsOfUnity n L => ((u : Lˣ) : L)) h
      simp only [rootsOfUnity.coe_mkOfPowEq] at hcoe
      rw [div_eq_div_iff hα0 hα0] at hcoe
      exact Subtype.ext (mul_right_cancel₀ hα0 hcoe)
    rwa [hcardroot] at hle
  haveI : HasEnoughRootsOfUnity L n := HasEnoughRootsOfUnity.of_card_le hge
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L n
  -- F = ℚ(ζ) has degree φ(n)
  have hζ_int : IsIntegral ℚ ζ := .of_finite ℚ ζ
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have hmin : cyclotomic n ℚ = minpoly ℚ ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (by omega))
  set F := IntermediateField.adjoin ℚ ({ζ} : Set L) with hF
  have hF_finrank : Module.finrank ℚ F = n.totient := by
    rw [IntermediateField.adjoin.finrank hζ_int, ← hmin, natDegree_cyclotomic]
  -- L = F(α): every root lies in ℚ(ζ, α)
  have htop : IntermediateField.adjoin F ({α} : Set L) = ⊤ := by
    apply IntermediateField.restrictScalars_injective ℚ
    rw [IntermediateField.restrictScalars_top, hF, IntermediateField.adjoin_adjoin_left]
    -- goal: adjoin ℚ ({ζ} ∪ {α}) = ⊤
    refine le_antisymm le_top ?_
    intro x _
    -- x lies in the splitting field, generated by the roots
    have hx_alg : x ∈ Algebra.adjoin ℚ (q.rootSet L) := by
      rw [IsSplittingField.adjoin_rootSet]; trivial
    refine Algebra.adjoin_le ?_ hx_alg
    -- every root β is in adjoin ℚ ({ζ} ∪ {α})
    intro β hβ
    have hζmem : ζ ∈ IntermediateField.adjoin ℚ ({ζ} ∪ {α} : Set L) :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_union_left _ rfl)
    have hαmem : α ∈ IntermediateField.adjoin ℚ ({ζ} ∪ {α} : Set L) :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_union_right _ rfl)
    -- β/α is an n-th root of unity, hence a power of ζ
    have hβpow : β ^ n = (p : L) := root_pow β hβ
    have hξ : (β / α) ^ n = 1 := by
      rw [div_pow, hβpow, hαpow, div_self hp_ne]
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
    -- β = ζ^i · α
    have hβeq : β = ζ ^ i * α := by
      rw [hi, div_mul_cancel₀ β hα0]
    rw [SetLike.mem_coe, hβeq]
    exact mul_mem (pow_mem hζmem i) hαmem
  -- [L : F] = [F(α) : F] ≤ n
  have hFL_le : Module.finrank F L ≤ n := by
    have hαL : IsIntegral F α := IsIntegral.of_finite F α
    -- α is a root of Xⁿ - p over F, a degree-n polynomial
    have hgaeval : aeval α (X ^ n - C ((p : ℕ) : F) : F[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, map_natCast, hαpow, sub_self]
    have hdvd : minpoly F α ∣ (X ^ n - C ((p : ℕ) : F)) := minpoly.dvd F α hgaeval
    have hgne : (X ^ n - C ((p : ℕ) : F) : F[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) _
    have hdeg : (minpoly F α).natDegree ≤ n := by
      have hle := Polynomial.natDegree_le_of_dvd hdvd hgne
      rwa [natDegree_X_pow_sub_C] at hle
    have key : Module.finrank F L = (minpoly F α).natDegree := by
      rw [← IntermediateField.finrank_top' (F := F) (E := L), ← htop,
        IntermediateField.adjoin.finrank hαL]
    rw [key]; exact hdeg
  -- multiply the tower degrees
  calc Module.finrank ℚ L
      = Module.finrank ℚ F * Module.finrank F L := (Module.finrank_mul_finrank ℚ F L).symm
    _ ≤ n.totient * n := by rw [hF_finrank]; exact Nat.mul_le_mul_left _ hFL_le
    _ = n * n.totient := Nat.mul_comm _ _

-- ============================================================================
-- The exact metacyclic order when gcd(n, φ(n)) = 1
-- ============================================================================

/-- **`|Gal(Xⁿ-p/ℚ)| = n·φ(n)` when `gcd(n, φ(n)) = 1`.** The coprime lower bound
`n·φ(n) ∣ |Gal|` (`mul_totient_dvd_gal_card_of_coprime`) meets the metacyclic ceiling
`|Gal| ≤ n·φ(n)` (`gal_card_le_n_mul_totient`), pinning the order exactly — for every prime
`p`, with no genericity hypothesis.  Unlike the parent's `n = 2, 3` factorial squeeze, this
holds at every coprime degree, including `n ≥ 4` where `n·φ(n) < n!`. -/
theorem gal_card_eq_n_mul_totient_of_coprime (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hcop : Nat.Coprime n n.totient) :
    Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal = n * n.totient := by
  have hle := gal_card_le_n_mul_totient n p hn hp
  have hdvd := mul_totient_dvd_gal_card_of_coprime n p hn hp hcop
  have hpos : 0 < Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal := Fintype.card_pos
  exact Nat.le_antisymm hle (Nat.le_of_dvd hpos hdvd)

/-- **`|Gal(X⁵-p/ℚ)| = 20`** for every prime `p` — the affine group `F₂₀ = AGL(1,5)`.
Since `gcd(5, φ(5)) = gcd(5, 4) = 1`, the coprime bracket pins the order: `5·φ(5) = 20 ∣
|Gal|` while the metacyclic ceiling gives `|Gal| ≤ 20`.  The factorial bound `|Gal| ∣ 5! =
120` alone cannot close this (`20 < 120`); the cyclotomic ceiling is essential.  This is the
first genuinely-new exact pin beyond the parent's `n = 2, 3` factorial squeeze. -/
theorem gal_card_quintic_eq_twenty (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 5 - C (p : ℚ) : ℚ[X]).Gal = 20 := by
  have h := gal_card_eq_n_mul_totient_of_coprime 5 p (by norm_num) hp (by decide)
  rw [h]; decide

end InverseGaloisExtensions
