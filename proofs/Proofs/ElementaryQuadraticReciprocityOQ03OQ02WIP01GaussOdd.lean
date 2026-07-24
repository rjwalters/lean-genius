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
import Mathlib.FieldTheory.Finite.GaloisField
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

/-! ## Frobenius covariance in characteristic `p`

With the square formula in hand, the reciprocity mechanism is the Frobenius
endomorphism: in a field of odd characteristic `p` (with `p` invertible mod
`q`), raising the Gauss sum to the `p`-th power distributes over the sum
(`sum_pow_char`), fixes the character values (`χ(a)^p = χ(a)` since
`χ(a) ∈ {0, ±1}` and `p` is odd), and dilates the frequency (`(ζ^a)^p =
ζ^{ap}`); undoing the dilation with the substitution `a ↦ a·p̄` costs exactly
one factor `χ(p̄)`.  Cancelling `g ≠ 0` in `g^p = g·(g²)^{(p−1)/2}` then
converts the covariance into the *Euler-criterion identity*
`(χ(−1)·q)^{(p−1)/2} = χ(p̄)` — the algebraic heart of quadratic
reciprocity. -/

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- Character values are fixed by odd powers: `χ(a)^p = χ(a)` in `K`, because
`χ(a) ∈ {0, 1, −1}` and `p` is odd. -/
theorem chiK_pow_char (hodd : Odd p) (a : ZMod q) :
    chiK (K := K) a ^ p = chiK a := by
  rcases quadraticChar_isQuadratic (ZMod q) a with h | h | h <;>
    · unfold chiK
      rw [h]
      push_cast
      first
        | exact zero_pow hp.out.ne_zero
        | exact one_pow p
        | exact hodd.neg_one_pow

/-- Power law for `zetapow`: `(ζ^a)^n = ζ^{a·n̄}` where `n̄ = (n : ZMod q)`.
The exponents agree modulo `q`, and `ζ^q = 1` folds them. -/
theorem zetapow_pow (ζ : K) (hζq : ζ ^ q = 1) (a : ZMod q) (n : ℕ) :
    zetapow ζ a ^ n = zetapow ζ (a * (n : ZMod q)) := by
  unfold zetapow
  rw [← pow_mul]
  conv_lhs => rw [pow_eq_pow_mod _ hζq]
  conv_rhs => rw [pow_eq_pow_mod _ hζq]
  congr 1
  rw [ZMod.val_mul, Nat.mod_mod_of_dvd _ (dvd_refl q), ZMod.val_natCast]
  exact Nat.ModEq.mul_left a.val (Nat.mod_modEq n q).symm

/-- **Frobenius covariance of the Gauss sum:** in characteristic `p` (odd,
invertible mod `q`), `g^p = χ(p̄)·g`.  The Frobenius distributes over the sum,
fixes `χ`, and dilates frequencies by `p̄`; the substitution `a ↦ a·p̄`
(`mulRight_bijective₀`) restores `g` at the cost of `χ(p̄)`. -/
theorem gaussSumOdd_pow_char (hodd : Odd p) (ζ : K) (hζq : ζ ^ q = 1)
    (hpq : (p : ZMod q) ≠ 0) :
    gaussSumOdd (q := q) ζ ^ p = chiK (K := K) ((p : ZMod q)) * gaussSumOdd (q := q) ζ := by
  haveI : ExpChar K p := ExpChar.prime hp.out
  have hstep : gaussSumOdd (q := q) ζ ^ p
      = ∑ a : ZMod q, chiK a * zetapow ζ (a * (p : ZMod q)) := by
    rw [gaussSumOdd, sum_pow_char]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, chiK_pow_char hodd, zetapow_pow ζ hζq]
  have hrw : ∀ a : ZMod q, chiK (K := K) a * zetapow ζ (a * (p : ZMod q))
      = chiK (K := K) ((p : ZMod q))
          * (chiK (a * (p : ZMod q)) * zetapow ζ (a * (p : ZMod q))) := by
    intro a
    have h2 : chiK (K := K) ((p : ZMod q)) * chiK ((p : ZMod q)) = 1 :=
      chiK_sq_eq_one hpq
    rw [chiK_mul]
    linear_combination (-(chiK (K := K) a * zetapow ζ (a * (p : ZMod q)))) * h2
  rw [hstep, Finset.sum_congr rfl fun a _ => hrw a, ← Finset.mul_sum]
  congr 1
  rw [gaussSumOdd]
  exact Fintype.sum_bijective _ (mulRight_bijective₀ _ hpq) _ _ (fun a => rfl)

/-- **The Euler-criterion identity:** cancelling `g ≠ 0` between
`g^p = χ(p̄)·g` (Frobenius) and `g^p = g·(g²)^{(p−1)/2}` with `g² = χ(−1)·q`
gives

    `(χ(−1)·q)^{(p−1)/2} = χ(p̄)`   in `K`.

Instantiated in `GaloisField p k` and descended to `ZMod p`, this becomes full
quadratic reciprocity. -/
theorem chi_neg_one_mul_q_pow_eq_chi (hq2 : q ≠ 2) (hodd : Odd p) (ζ : K)
    (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1) (hqK : (q : K) ≠ 0)
    (hpq : (p : ZMod q) ≠ 0) :
    (chiK (K := K) (-1 : ZMod q) * q) ^ ((p - 1) / 2) = chiK ((p : ZMod q)) := by
  have hS := gaussSumOdd_ne_zero hq2 ζ hζq hζ1 hqK
  have hfrob := gaussSumOdd_pow_char (p := p) hodd ζ hζq hpq
  have hsq := gaussSumOdd_sq hq2 ζ hζq hζ1
  have hp1 : p = 2 * ((p - 1) / 2) + 1 := by
    rcases hodd with ⟨m, hm⟩; omega
  have hpow : gaussSumOdd (q := q) ζ ^ p
      = gaussSumOdd (q := q) ζ * (gaussSumOdd (q := q) ζ ^ 2) ^ ((p - 1) / 2) := by
    conv_lhs => rw [hp1]
    rw [pow_succ, pow_mul]
    ring
  rw [hsq] at hpow
  have hcancel : gaussSumOdd (q := q) ζ * (chiK (K := K) (-1 : ZMod q) * q) ^ ((p - 1) / 2)
      = gaussSumOdd (q := q) ζ * chiK ((p : ZMod q)) := by
    rw [← hpow, hfrob]
    ring
  exact mul_left_cancel₀ hS hcancel

end Frobenius

/-! ## Full quadratic reciprocity, independent of Mathlib's QR

Instantiating the engine in `GaloisField p k` — where `k` is the
multiplicative order of `p` mod `q`, so that `q ∣ p^k − 1` and the cyclic unit
group contains an element of order exactly `q` — and descending the
Euler-criterion identity along the prime subfield `ZMod p` yields **quadratic
reciprocity in Euler's `q*` form**:

    `(q* | p) = (p | q)`  where  `q* = χ_q(−1)·q`,

for distinct odd primes `p, q`.  Nothing below invokes
`jacobiSym.quadratic_reciprocity` or Mathlib's Gauss-sum library; the inputs
are the self-contained engine above, Euler's criterion (`legendreSym.eq_pow`),
and finite-field generalities. -/

section Reciprocity

/-- **Existence of a `q`-th root of unity in a Galois field of characteristic
`p`.**  Take `k` to be the multiplicative order of `p` mod `q`; then
`q ∣ p^k − 1`, and a generator `g` of the cyclic group
`(GaloisField p k)ˣ` (order `p^k − 1`) yields `ζ = g^{(p^k−1)/q}` of order
exactly `q`. -/
private theorem exists_qth_root (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) :
    ∃ (k : ℕ) (ζ : GaloisField p k), ζ ^ q = 1 ∧ ζ ≠ 1 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.out hq.out).mpr hpq
  -- k := order of p mod q gives q ∣ p^k − 1
  have hkey : ∃ k, k ≠ 0 ∧ q ∣ p ^ k - 1 := by
    refine ⟨orderOf (ZMod.unitOfCoprime p hcop), (orderOf_pos _).ne', ?_⟩
    have h2 : ((p : ZMod q)) ^ orderOf (ZMod.unitOfCoprime p hcop) = 1 := by
      have h1 := congrArg (Units.val) (pow_orderOf_eq_one (ZMod.unitOfCoprime p hcop))
      rwa [Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime] at h1
    have hple : 1 ≤ p ^ orderOf (ZMod.unitOfCoprime p hcop) :=
      Nat.one_le_pow _ _ hp.out.pos
    have h3 : ((p ^ orderOf (ZMod.unitOfCoprime p hcop) - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub hple, Nat.cast_pow, h2, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h3
  obtain ⟨k, hk0, hdvd⟩ := hkey
  obtain ⟨m, hm⟩ := hdvd
  have hpk1 : 1 < p ^ k := Nat.one_lt_pow hk0 hp.out.one_lt
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    omega
  -- a generator of the cyclic unit group
  haveI : Fintype (GaloisField p k)ˣ := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p k)ˣ)
  have horder : orderOf g = p ^ k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      GaloisField.card p k hk0]
  have hζorder : orderOf (g ^ m) = q := by
    rw [orderOf_pow, horder, hm, Nat.gcd_eq_right (dvd_mul_left m q),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  refine ⟨k, ((g ^ m : (GaloisField p k)ˣ) : GaloisField p k), ?_, ?_⟩
  · have h1 : (g ^ m) ^ q = 1 := by rw [← hζorder]; exact pow_orderOf_eq_one _
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  · intro h1
    have h2 : (g ^ m) = (1 : (GaloisField p k)ˣ) :=
      Units.ext (by rw [Units.val_one]; exact h1)
    have h3 : orderOf (g ^ m) = 1 := by rw [h2, orderOf_one]
    rw [hζorder] at h3
    exact hq.out.one_lt.ne' h3

/-- Casts of `±1` into `ZMod p` are injective for `p > 2`. -/
private theorem int_pm_one_cast_inj {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  haveI : Fact (2 < p) := ⟨by have := hp.out.two_le; omega⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso; push_cast at h; exact ZMod.neg_one_ne_one h.symm
  · exfalso; push_cast at h; exact ZMod.neg_one_ne_one h
  · rfl

/-- **Quadratic reciprocity (Euler's `q*` form), independent of Mathlib's
QR.**  For distinct odd primes `p ≠ q`,

    `(χ_q(−1)·q | p) = (p | q)`,

i.e. `legendreSym p (legendreSym q (−1) * q) = legendreSym q p`.  Proof: the
Euler-criterion identity `(χ(−1)q)^{(p−1)/2} = χ(p̄)` holds in
`GaloisField p k` (Gauss square formula + Frobenius covariance + cancellation
of `g ≠ 0`); both sides are integer casts, so the identity descends along the
injective `algebraMap (ZMod p) → GaloisField p k` to `ZMod p`, where the left
side is `legendreSym p (χ(−1)q)` by Euler's criterion; finally `±1` values are
distinguished mod `p > 2`. -/
theorem quadratic_reciprocity_qstar (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p (legendreSym q (-1) * q) = legendreSym q p := by
  obtain ⟨k, ζ, hζq, hζ1⟩ := exists_qth_root p q hpq
  have hoddp : Odd p := hp.out.odd_of_ne_two hp2
  have hqK : ((q : GaloisField p k)) ≠ 0 := by
    intro h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp
      ((Nat.coprime_primes hp.out hq.out).mpr hpq)
      ((CharP.cast_eq_zero_iff (GaloisField p k) p q).mp h0)
  have hpZ : ((p : ZMod q)) ≠ 0 := by
    intro h0
    exact (Nat.Prime.coprime_iff_not_dvd hq.out).mp
      ((Nat.coprime_primes hq.out hp.out).mpr hpq.symm)
      ((ZMod.natCast_eq_zero_iff p q).mp h0)
  -- the K-identity from the engine
  have hK := chi_neg_one_mul_q_pow_eq_chi (p := p) hq2 hoddp ζ hζq hζ1 hqK hpZ
  unfold chiK at hK
  -- both sides as integer casts
  set A : ℤ := (quadraticChar (ZMod q) (-1) * q) ^ ((p - 1) / 2) with hA
  set B : ℤ := quadraticChar (ZMod q) ((p : ZMod q)) with hB
  have hKAB : ((A : GaloisField p k)) = (B : GaloisField p k) := by
    rw [hA, hB]
    push_cast
    push_cast at hK
    exact hK
  -- descend to the prime subfield
  have hZp : ((A : ZMod p)) = (B : ZMod p) := by
    apply (algebraMap (ZMod p) (GaloisField p k)).injective
    rw [map_intCast, map_intCast]
    exact hKAB
  -- Euler's criterion on the left
  have hdiv : p / 2 = (p - 1) / 2 := by rcases hoddp with ⟨t, ht⟩; omega
  have hlhs : ((legendreSym p ((quadraticChar (ZMod q) (-1)) * q) : ℤ) : ZMod p)
      = (A : ZMod p) := by
    rw [legendreSym.eq_pow, hdiv, hA]
    push_cast
    ring
  have hB' : B = legendreSym q p := by
    rw [hB]
    unfold legendreSym
    norm_num
  have hcong : ((legendreSym p ((quadraticChar (ZMod q) (-1)) * q) : ℤ) : ZMod p)
      = ((legendreSym q p : ℤ) : ZMod p) := by
    rw [hlhs, hZp, hB']
  -- the ±1 values are distinguished mod p
  have hchi_pm : quadraticChar (ZMod q) (-1) = 1 ∨ quadraticChar (ZMod q) (-1) = -1 := by
    rcases quadraticChar_isQuadratic (ZMod q) (-1) with h | h | h
    · exfalso
      rw [quadraticChar_eq_zero_iff] at h
      exact (neg_ne_zero.mpr one_ne_zero) h
    · exact Or.inl h
    · exact Or.inr h
  have hXne : (((quadraticChar (ZMod q) (-1)) * (q : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    apply mul_ne_zero
    · rcases hchi_pm with h | h <;> rw [h] <;> push_cast
      · exact one_ne_zero
      · exact neg_ne_zero.mpr one_ne_zero
    · intro h0
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp
        ((Nat.coprime_primes hp.out hq.out).mpr hpq)
        ((ZMod.natCast_eq_zero_iff q p).mp (by exact_mod_cast h0))
  have hL1 := legendreSym.eq_one_or_neg_one (p := p) hXne
  have hL2 : legendreSym q p = 1 ∨ legendreSym q p = -1 :=
    legendreSym.eq_one_or_neg_one (p := q) (by exact_mod_cast hpZ)
  have hmain : legendreSym p ((quadraticChar (ZMod q) (-1)) * q) = legendreSym q p :=
    int_pm_one_cast_inj hp2 hL1 hL2 hcong
  have hbridge : legendreSym q (-1) = quadraticChar (ZMod q) (-1) := by
    unfold legendreSym
    norm_num
  rw [hbridge]
  exact hmain

/-! ### The classical product form

`quadratic_reciprocity_qstar` packages reciprocity in Euler's `q*` form.
This subsection derives the textbook product form

    `(q | p) · (p | q) = (−1)^{((p−1)/2)·((q−1)/2)}`

by parity bookkeeping only: the first supplement in exponent form
(`legendreSym_neg_one_eq_pow`, via Euler's criterion — not Mathlib's QR
file), multiplicativity of the Legendre symbol, and `sq_one`. Mathlib's
`legendreSym.quadratic_reciprocity` is **not** used anywhere in this
chain, preserving the independence claim of the Gauss-sum engine. -/

/-- **First supplement, exponent form** (via Euler's criterion only):
`(−1 | q) = (−1)^((q−1)/2)` for an odd prime `q`. Both sides are `±1`
integers agreeing mod `q > 2`, hence equal. -/
theorem legendreSym_neg_one_eq_pow (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    legendreSym q (-1) = (-1) ^ ((q - 1) / 2) := by
  have hoddq : Odd q := hq.out.odd_of_ne_two hq2
  have hdiv : q / 2 = (q - 1) / 2 := by rcases hoddq with ⟨t, ht⟩; omega
  have hne : ((-1 : ℤ) : ZMod q) ≠ 0 := by
    push_cast
    exact neg_ne_zero.mpr one_ne_zero
  have hcast : ((legendreSym q (-1) : ℤ) : ZMod q)
      = (((-1 : ℤ) ^ ((q - 1) / 2) : ℤ) : ZMod q) := by
    rw [legendreSym.eq_pow, hdiv]
    push_cast
    ring
  have hpow : ((-1 : ℤ) ^ ((q - 1) / 2) = 1) ∨ ((-1 : ℤ) ^ ((q - 1) / 2) = -1) := by
    rcases Nat.even_or_odd ((q - 1) / 2) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  exact int_pm_one_cast_inj hq2 (legendreSym.eq_one_or_neg_one (p := q) hne) hpow hcast

/-- **Quadratic reciprocity, classical product form** — derived from the
`q*` form by parity bookkeeping, independent of Mathlib's
`legendreSym.quadratic_reciprocity`:

    `(q | p) · (p | q) = (−1)^{((p−1)/2)·((q−1)/2)}`

for distinct odd primes `p ≠ q`. If `(q−1)/2` is even, `q* = q` and the
two symbols coincide, so the product is `1`; if odd, `q* = −q` and the
extra factor `(−1 | p) = (−1)^((p−1)/2)` is exactly the right-hand side. -/
theorem quadratic_reciprocity_product (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hqstar := quadratic_reciprocity_qstar p q hp2 hq2 hpq
  have hqp : ((q : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp
      ((Nat.coprime_primes hp.out hq.out).mpr hpq)
      ((ZMod.natCast_eq_zero_iff q p).mp (by exact_mod_cast h0))
  have hsq : legendreSym p q * legendreSym p q = 1 := by
    have h := legendreSym.sq_one (p := p) hqp
    rwa [sq] at h
  rcases Nat.even_or_odd ((q - 1) / 2) with hn | hn
  · -- `(q−1)/2` even: `q* = q`, both sides collapse to `1`.
    have hε : legendreSym q (-1) = 1 := by
      rw [legendreSym_neg_one_eq_pow q hq2, hn.neg_one_pow]
    rw [hε, one_mul] at hqstar
    have hrhs : ((-1 : ℤ)) ^ ((p - 1) / 2 * ((q - 1) / 2)) = 1 :=
      (Nat.even_mul.mpr (Or.inr hn)).neg_one_pow
    rw [hrhs, ← hqstar]
    exact hsq
  · -- `(q−1)/2` odd: `q* = −q`, the supplement supplies `(−1)^((p−1)/2)`.
    have hε : legendreSym q (-1) = -1 := by
      rw [legendreSym_neg_one_eq_pow q hq2, hn.neg_one_pow]
    rw [hε] at hqstar
    rw [legendreSym.mul] at hqstar
    have hpneg : legendreSym p (-1) = (-1) ^ ((p - 1) / 2) :=
      legendreSym_neg_one_eq_pow p hp2
    have hrhs : ((-1 : ℤ)) ^ ((p - 1) / 2 * ((q - 1) / 2)) = (-1) ^ ((p - 1) / 2) := by
      rw [pow_mul]
      rcases Nat.even_or_odd ((p - 1) / 2) with hm | hm
      · rw [hm.neg_one_pow, one_pow]
      · rw [hm.neg_one_pow, hn.neg_one_pow]
    rw [hrhs, ← hqstar, hpneg, mul_assoc, hsq, mul_one]

end Reciprocity

end KroneckerSymbol
