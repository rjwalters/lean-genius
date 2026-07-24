/-
# The odd-prime quadratic Gauss sum engine: `g_q² = χ_q(−1)·q`

**Satellite of `elementary-quadratic-reciprocity-oq-03-oq-02-wip-01`.**

The node's Gauss-sum programme has so far treated the prime `2` end-to-end:
`ElementaryQuadraticReciprocityOQ03OQ02WIP01.lean` builds the conductor-8 sum
`τ(χ₈)`, proves `τ² = 8` ring-generically, and derives the second supplement
`(2/p) = (p/2)` via Frobenius covariance in `GaloisField p 2` — all without
invoking Mathlib's quadratic reciprocity.

This file supplies the **odd-prime half of the engine**: for an arbitrary odd
prime `q`, an arbitrary field `K`, and any primitive `q`-th root of unity
`ζ ∈ K` (packaged as `ζ^q = 1`, `ζ ≠ 1` — primitivity is automatic for prime
`q`), the quadratic Gauss sum

    gaussSumOdd ζ = ∑ a : ZMod q, χ_q(a) · ζ^a,   χ_q = quadraticChar (ZMod q)

satisfies the classical **Gauss square formula**

    (gaussSumOdd ζ)² = χ_q(−1) · q            (`gaussSumOdd_sq`)

This is the identified hard half of the remaining open question on this node
(full quadratic reciprocity via Gauss sums, independent of Mathlib's
`jacobiSym.quadratic_reciprocity`): the formula holds in ANY field containing a
primitive `q`-th root — in particular in `GaloisField p k` of characteristic
`p`, where the follow-up Frobenius-covariance step `g^p = χ_q(p)·g` (the exact
analogue of the prime-2 recipe already on the node) will yield reciprocity.

The proof is the classical substitution argument, kept fully elementary:

1. `zetapow ζ a := ζ^a.val` is additive-to-multiplicative
   (`zetapow_add`, via `ζ^q = 1` and exponent folding mod `q`);
2. orthogonality `∑_a ζ^{ad} = 0` for `d ≠ 0` (`sum_zetapow_mul_eq_zero`) by
   the shift trick `a ↦ a + 1` — no geometric-series machinery needed;
3. in `S²`, each row `a ≠ 0` reindexes by `b = a·c` (`mulLeft_bijective₀`),
   `χ(a)² = 1` collapses the character, and the double sum reduces to
   `∑_c χ(c)·(∑_{a≠0} ζ^{a(1+c)})`, which the orthogonality relations and
   `∑_c χ(c) = 0` (`quadraticChar_sum_zero`) evaluate to `χ(−1)·q`.

Mathlib's abstract `GaussSum` library proves an analogous square formula for
`MulChar`/`AddChar` pairs; this file deliberately keeps the node's
self-contained concrete development (mirroring the explicit `ζ₈` treatment of
the prime-2 case) so that the eventual reciprocity proof remains independent
of that infrastructure and composes directly with the node's established
`GaloisField` descent recipe.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace KroneckerSymbol

open Finset

variable {K : Type*} [Field K] {q : ℕ} [hq : Fact q.Prime]

instance : NeZero q := ⟨hq.out.pos.ne'⟩

/-! ## Powers of a root of unity indexed by `ZMod q` -/

/-- `ζ` raised to a residue class: `zetapow ζ a = ζ ^ a.val`.  When `ζ^q = 1`
this is a well-defined additive-to-multiplicative map on `ZMod q`. -/
def zetapow (ζ : K) (a : ZMod q) : K := ζ ^ a.val

@[simp] theorem zetapow_zero (ζ : K) : zetapow ζ (0 : ZMod q) = 1 := by
  simp [zetapow, ZMod.val_zero]

/-- `zetapow` turns addition of residues into multiplication: the exponent
`(a+b).val = (a.val + b.val) % q` folds back to `a.val + b.val` because
`ζ^q = 1`. -/
theorem zetapow_add (ζ : K) (hζq : ζ ^ q = 1) (a b : ZMod q) :
    zetapow ζ (a + b) = zetapow ζ a * zetapow ζ b := by
  unfold zetapow
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζq, pow_add]

/-- For prime `q`, the hypotheses `ζ^q = 1`, `ζ ≠ 1` force `ζ` to have order
exactly `q` (the order divides the prime `q` and is not `1`). -/
theorem orderOf_of_pow_prime_eq_one (ζ : K) (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1) :
    orderOf ζ = q := by
  have hdvd : orderOf ζ ∣ q := orderOf_dvd_of_pow_eq_one hζq
  rcases hq.out.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hζ1
  · exact h

/-- Primitivity for free at prime level: `zetapow ζ d ≠ 1` for every nonzero
residue `d`.  If `ζ^{d.val} = 1` then `q = orderOf ζ` divides `d.val`, which is
impossible for `0 < d.val < q`. -/
theorem zetapow_ne_one (ζ : K) (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    {d : ZMod q} (hd : d ≠ 0) : zetapow ζ d ≠ 1 := by
  intro h
  have horder : orderOf ζ = q := orderOf_of_pow_prime_eq_one ζ hζq hζ1
  have hdvd : orderOf ζ ∣ d.val := orderOf_dvd_of_pow_eq_one h
  rw [horder] at hdvd
  have hlt : d.val < q := ZMod.val_lt d
  have hne : d.val ≠ 0 := fun h0 => hd ((ZMod.val_eq_zero d).mp h0)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  omega

/-! ## Orthogonality relations -/

/-- **Root-of-unity orthogonality, nonzero frequency.**  For `d ≠ 0`,
`∑_{a : ZMod q} ζ^{ad} = 0`.  Shift trick: reindexing `a ↦ a + 1` multiplies
the sum by `ζ^d ≠ 1`, so the sum is fixed by multiplication by `ζ^d` and must
vanish.  No geometric-series machinery is needed. -/
theorem sum_zetapow_mul_eq_zero (ζ : K) (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    {d : ZMod q} (hd : d ≠ 0) :
    ∑ a : ZMod q, zetapow ζ (a * d) = 0 := by
  have hshift : ∑ a : ZMod q, zetapow ζ ((a + 1) * d) = ∑ a : ZMod q, zetapow ζ (a * d) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod q)) _ _ (fun a => rfl)
  have hkey : zetapow ζ d * ∑ a : ZMod q, zetapow ζ (a * d)
      = ∑ a : ZMod q, zetapow ζ (a * d) := by
    rw [Finset.mul_sum]
    calc ∑ a : ZMod q, zetapow ζ d * zetapow ζ (a * d)
        = ∑ a : ZMod q, zetapow ζ ((a + 1) * d) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [add_mul, one_mul, zetapow_add ζ hζq]
          ring
      _ = ∑ a : ZMod q, zetapow ζ (a * d) := hshift
  have hne : zetapow ζ d - 1 ≠ 0 := sub_ne_zero.mpr (zetapow_ne_one ζ hζq hζ1 hd)
  have hzero : (zetapow ζ d - 1) * ∑ a : ZMod q, zetapow ζ (a * d) = 0 := by
    rw [sub_mul, one_mul, hkey, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- **Zero frequency:** `∑_{a : ZMod q} ζ^{a·0} = q` (each term is `1`). -/
theorem sum_zetapow_mul_zero (ζ : K) :
    ∑ a : ZMod q, zetapow ζ (a * 0) = (q : K) := by
  simp only [mul_zero, zetapow_zero]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-! ## The quadratic character, cast into `K` -/

/-- The quadratic character `χ_q = quadraticChar (ZMod q)` (values in
`{-1, 0, 1} ⊆ ℤ`), cast into the field `K`. -/
def chiK (a : ZMod q) : K := ((quadraticChar (ZMod q) a : ℤ) : K)

@[simp] theorem chiK_zero : chiK (K := K) (0 : ZMod q) = 0 := by
  simp [chiK]

theorem chiK_mul (a b : ZMod q) :
    chiK (K := K) (a * b) = chiK a * chiK b := by
  unfold chiK
  rw [map_mul]
  push_cast
  ring

/-- `χ(a)² = 1` for `a ≠ 0`, cast into `K`. -/
theorem chiK_sq_eq_one {a : ZMod q} (ha : a ≠ 0) :
    chiK (K := K) a * chiK a = 1 := by
  unfold chiK
  rw [← Int.cast_mul, ← sq, quadraticChar_sq_one ha, Int.cast_one]

/-- **Mean-zero:** `∑_a χ(a) = 0` for odd `q` (as many nonzero squares as
non-squares), cast into `K`. -/
theorem sum_chiK (hq2 : q ≠ 2) : ∑ a : ZMod q, chiK (K := K) a = 0 := by
  have hF : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  have h := quadraticChar_sum_zero hF
  unfold chiK
  exact_mod_cast congrArg (fun z : ℤ => (z : K)) h

/-! ## The quadratic Gauss sum and the square formula -/

/-- **The odd-prime quadratic Gauss sum** `g_q = ∑_{a : ZMod q} χ_q(a)·ζ^a`,
valued in an arbitrary field `K` containing a `q`-th root of unity `ζ`. -/
noncomputable def gaussSumOdd (ζ : K) : K :=
  ∑ a : ZMod q, chiK a * zetapow ζ a

/-- **Row collapse.**  For `a ≠ 0`, multiplying the Gauss sum by its `a`-th
term reindexes (`b = a·c`) into `∑_c χ(c)·ζ^{a(1+c)}`: the substitution uses
`χ(ac) = χ(a)χ(c)` and `χ(a)² = 1`, and merges the exponents via
`zetapow_add`. -/
theorem term_mul_gaussSumOdd (ζ : K) (hζq : ζ ^ q = 1)
    {a : ZMod q} (ha : a ≠ 0) :
    chiK a * zetapow ζ a * gaussSumOdd (q := q) ζ
      = ∑ c : ZMod q, chiK c * zetapow ζ (a * (1 + c)) := by
  have hreindex : gaussSumOdd (q := q) ζ
      = ∑ c : ZMod q, chiK (a * c) * zetapow ζ (a * c) :=
    (Fintype.sum_bijective _ (mulLeft_bijective₀ a ha) _ _ (fun c => rfl)).symm
  rw [hreindex, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : a * (1 + c) = a + a * c := by ring
  rw [chiK_mul, h1, zetapow_add ζ hζq]
  have h2 : chiK (K := K) a * chiK a = 1 := chiK_sq_eq_one ha
  linear_combination zetapow ζ a * zetapow ζ (a * c) * chiK (K := K) c * h2

/-- **Gauss's square formula** (1801): for an odd prime `q` and any field `K`
with a primitive `q`-th root of unity `ζ`,

    `(∑_a χ_q(a) ζ^a)² = χ_q(−1) · q`.

The classical substitution proof: expand `S² = ∑_{a≠0} (χ(a)ζ^a)·S` (the `a=0`
row vanishes), collapse each row to `∑_c χ(c) ζ^{a(1+c)}`
(`term_mul_gaussSumOdd`), swap the sums, and evaluate the inner geometric sums:
frequency `1+c = 0` contributes `χ(−1)(q−1)`, every other frequency
contributes `−χ(c)`, and `∑ χ = 0` turns the tail into `+χ(−1)`. -/
theorem gaussSumOdd_sq (hq2 : q ≠ 2) (ζ : K) (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1) :
    gaussSumOdd (q := q) ζ ^ 2 = chiK (K := K) (-1 : ZMod q) * q := by
  -- Step 1: S² as a sum of rows over a ≠ 0
  have hrow0 : chiK (K := K) (0 : ZMod q) * zetapow ζ (0 : ZMod q) * gaussSumOdd (q := q) ζ
      = 0 := by
    rw [chiK_zero, zero_mul, zero_mul]
  have hsq : gaussSumOdd (q := q) ζ ^ 2
      = ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
          chiK a * zetapow ζ a * gaussSumOdd (q := q) ζ := by
    rw [sq]
    conv_lhs => rw [gaussSumOdd, Finset.sum_mul]
    exact (Finset.sum_erase
      (f := fun b : ZMod q => chiK b * zetapow ζ b * gaussSumOdd (q := q) ζ)
      (a := (0 : ZMod q)) univ hrow0).symm
  -- Step 2: collapse the rows and swap the summation order
  have hswap : gaussSumOdd (q := q) ζ ^ 2
      = ∑ c : ZMod q, chiK c *
          ∑ a ∈ (univ : Finset (ZMod q)).erase 0, zetapow ζ (a * (1 + c)) := by
    rw [hsq]
    rw [Finset.sum_congr rfl fun a ha =>
      term_mul_gaussSumOdd ζ hζq (Finset.mem_erase.mp ha).1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
  -- Step 3: evaluate the inner sums over a ≠ 0
  have hinner_zero : ∑ a ∈ (univ : Finset (ZMod q)).erase 0, zetapow ζ (a * 0)
      = (q : K) - 1 := by
    rw [Finset.sum_erase_eq_sub (mem_univ 0), sum_zetapow_mul_zero, zero_mul,
      zetapow_zero]
  have hinner_ne : ∀ d : ZMod q, d ≠ 0 →
      ∑ a ∈ (univ : Finset (ZMod q)).erase 0, zetapow ζ (a * d) = -1 := by
    intro d hd
    rw [Finset.sum_erase_eq_sub (mem_univ 0), sum_zetapow_mul_eq_zero ζ hζq hζ1 hd,
      zero_mul, zetapow_zero, zero_sub]
  -- Step 4: split the outer sum at c = −1
  rw [hswap, ← Finset.add_sum_erase _ _ (mem_univ (-1 : ZMod q))]
  have hc1 : (1 : ZMod q) + -1 = 0 := by ring
  rw [hc1, hinner_zero]
  have htail : ∑ c ∈ (univ : Finset (ZMod q)).erase (-1),
      chiK c * ∑ a ∈ (univ : Finset (ZMod q)).erase 0, zetapow ζ (a * (1 + c))
      = ∑ c ∈ (univ : Finset (ZMod q)).erase (-1), -chiK (K := K) c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : (1 : ZMod q) + c ≠ 0 := by
      intro h0
      exact (Finset.mem_erase.mp hc).1 (by linear_combination h0)
    rw [hinner_ne _ hc']
    ring
  rw [htail, Finset.sum_neg_distrib,
    Finset.sum_erase_eq_sub (mem_univ (-1 : ZMod q)), sum_chiK hq2]
  ring

/-! ## Corollaries -/

/-- The square formula in Legendre-symbol form:
`g_q² = (−1 | q) · q` where `(· | q)` is `legendreSym q`. -/
theorem gaussSumOdd_sq_legendre (hq2 : q ≠ 2) (ζ : K) (hζq : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) :
    gaussSumOdd (q := q) ζ ^ 2 = ((legendreSym q (-1) : ℤ) : K) * q := by
  rw [gaussSumOdd_sq hq2 ζ hζq hζ1]
  congr 1
  unfold chiK legendreSym
  push_cast
  rfl

/-- **Nonvanishing:** if additionally `q ≠ 0` in `K` (i.e. `char K ≠ q`), the
Gauss sum is nonzero — the key cancellation input for the forthcoming
Frobenius-covariance step. -/
theorem gaussSumOdd_ne_zero (hq2 : q ≠ 2) (ζ : K) (hζq : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) (hqK : (q : K) ≠ 0) :
    gaussSumOdd (q := q) ζ ≠ 0 := by
  intro h
  have hsq := gaussSumOdd_sq hq2 ζ hζq hζ1
  rw [h, zero_pow two_ne_zero] at hsq
  have hneg1 : (-1 : ZMod q) ≠ 0 := by
    intro h0
    have : (1 : ZMod q) = 0 := by linear_combination -h0
    exact one_ne_zero this
  have hone : chiK (K := K) (-1 : ZMod q) * chiK (-1) = 1 := chiK_sq_eq_one hneg1
  have hchi : chiK (K := K) (-1 : ZMod q) = 0 := by
    rcases mul_eq_zero.mp hsq.symm with h' | h'
    · exact h'
    · exact absurd h' hqK
  rw [hchi, mul_zero] at hone
  exact zero_ne_one hone

end KroneckerSymbol
