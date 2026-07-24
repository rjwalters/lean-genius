/-
Vahlen–Capelli criterion for binomial irreducibility — the sole remaining open sub-case.

Classical theorem (Capelli / Vahlen; Lang, *Algebra*, VI §9): for a field `K`, `a : K`,
and `n ≥ 1`, the binomial `X^n − a` is irreducible over `K` if and only if
  (1) `a` is not a `p`-th power in `K` for every prime `p ∣ n`, and
  (2) if `4 ∣ n`, then `a ∉ −4·K⁴`.

Mathlib formalizes the odd-prime-power case (`X_pow_sub_C_irreducible_of_prime_pow`,
restricted to `p ≠ 2`) but the even case `4 ∣ n` is an explicit open `TODO` in
`Mathlib/FieldTheory/KummerExtension.lean`. In the surrounding formalization
(`CubeRoot3IrrationalOQ02OQ03.lean`) the whole criterion is machine-checked EXCEPT this
one residual sub-case, which is isolated here as a self-contained (Mathlib-only) statement.

Residual sub-case (`8 ∣ n`, pure 2-power base `X^(2^k)` with `k ≥ 3`, in the branch where
`−a` is itself a square):
  Given a field `K` and `a : K` such that
    (h1) `a` is not a square in `K`  (condition (1) at `p = 2`),
    (h2) `a ∉ −4·K⁴`                 (condition (2)),
    (hna) `−a` is a square in `K`    (the residual branch `a = −c²`),
  prove `X^(2^k) − a` is irreducible over `K` for all `k ≥ 3`.

The companion branch `−a ∉ K²` is already discharged unconditionally by a field-norm
descent; the difficulty of THIS branch is exactly that when `−a` is a square the norm
argument is inconclusive, and condition (2) (`a ∉ −4·K⁴`, the Sophie–Germain
factorisation `x⁴ + 4y⁴ = (x²−2xy+2y²)(x²+2xy+2y²)`) is what forbids the obstructing
squares in the 2-power tower. This is precisely the content of Lang VI §9.
-/
import Mathlib

open Polynomial
open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

universe u

namespace CubeRoot3IrrationalOQ02OQ03Statement

open IntermediateField AdjoinRoot

/-
Every element of a quadratic extension is `c₀ + c₁·g` for scalars `c₀ c₁` in the base.
-/
lemma quad_repr {K F : Type u} [Field K] [Field F] [Algebra K F]
    (pb : PowerBasis K F) (hdim : pb.dim = 2) (b : F) :
    ∃ c0 c1 : K, b = algebraMap K F c0 + algebraMap K F c1 * pb.gen := by
  have := pb.basis.sum_repr b;
  rw [ ← this, Finset.sum_eq_add ( ⟨ 0, by linarith ⟩ : Fin pb.dim ) ( ⟨ 1, by linarith ⟩ : Fin pb.dim ) ] <;> simp +decide [ pow_succ, Algebra.smul_def ];
  · exact ⟨ _, _, rfl ⟩;
  · grind +qlia

/-
`1` and `g` are linearly independent over the base in a quadratic extension.
-/
lemma quad_indep {K F : Type u} [Field K] [Field F] [Algebra K F]
    (pb : PowerBasis K F) (hdim : pb.dim = 2) {c0 c1 : K}
    (h : algebraMap K F c0 + algebraMap K F c1 * pb.gen = 0) : c0 = 0 ∧ c1 = 0 := by
  -- By the linear independence of the basis vectors, if $c0 + c1 \cdot pb.gen = 0$, then $c0 = 0$ and $c1 = 0$.
  have h_lin_ind : LinearIndependent K (fun i : Fin 2 => pb.gen ^ (i : ℕ)) := by
    convert pb.basis.linearIndependent;
    · exact hdim.symm;
    · rw [ pb.basis_eq_pow ];
      grind +qlia;
  rw [ Fintype.linearIndependent_iff ] at h_lin_ind;
  exact ⟨ h_lin_ind ( fun i => if i = 0 then c0 else c1 ) ( by simpa [ Fin.sum_univ_two ] using by simpa [ Algebra.smul_def ] using h ) 0, h_lin_ind ( fun i => if i = 0 then c0 else c1 ) ( by simpa [ Fin.sum_univ_two ] using by simpa [ Algebra.smul_def ] using h ) 1 ⟩

/-
**Descent lemma across a quadratic extension.**
Let `F = K(g)` be a quadratic extension of `K` with `g ^ 2 = a` (`a : K`).
If `a` is not a square in `K` and `a ∉ -4·K⁴`, then `g` is neither a square in `F`
nor of the form `-4·b⁴` in `F`.  Both statements reduce, via the explicit description
of squares in a quadratic extension, to `a ∈ -4·K⁴`, contradicting `h2`.
-/
lemma descent {K F : Type u} [Field K] [Field F] [Algebra K F]
    (pb : PowerBasis K F) (hdim : pb.dim = 2) {a : K} (hchar : (2 : K) ≠ 0)
    (hg : pb.gen ^ 2 = algebraMap K F a)
    (h1 : ∀ b : K, b ^ 2 ≠ a) (h2 : ∀ b : K, a ≠ -(4 * b ^ 4)) :
    (∀ b : F, b ^ 2 ≠ pb.gen) ∧ (∀ b : F, pb.gen ≠ -(4 * b ^ 4)) := by
  constructor;
  · intro b hb
    obtain ⟨c0, c1, hc⟩ : ∃ c0 c1 : K, b = algebraMap K F c0 + algebraMap K F c1 * pb.gen :=
      quad_repr pb hdim b
    have h_eq : algebraMap K F (c0^2 + a * c1^2) + algebraMap K F (2 * c0 * c1 - 1) * pb.gen = 0 := by
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, add_mul, mul_add, sq ];
      rw [ ← hg ] ; ring_nf at *;
      erw [ map_ofNat ] ; linear_combination' hb;
    have h_coeff : c0^2 + a * c1^2 = 0 ∧ 2 * c0 * c1 - 1 = 0 :=
      quad_indep pb hdim h_eq
    have h_contra : a = -(4 * (1 / (2 * c1))^4) := by
      grind +qlia
    exact h2 (1 / (2 * c1)) h_contra;
  · intro b hb
    obtain ⟨c0, c1, hc⟩ : ∃ c0 c1 : K, b = algebraMap K F c0 + algebraMap K F c1 * pb.gen :=
      quad_repr pb hdim b
    set p := c0^2 + a * c1^2
    set q := 2 * c0 * c1
    have h_eq : algebraMap K F (-(4 * (p^2 + a * q^2))) + algebraMap K F (-(8 * p * q)) * pb.gen = pb.gen := by
      convert hb.symm using 1 ; rw [ hc ] ; ring;
      rw [ show pb.gen ^ 4 = ( pb.gen ^ 2 ) ^ 2 by ring, show pb.gen ^ 3 = pb.gen * pb.gen ^ 2 by ring, hg ] ; ring;
      simp +zetaDelta at *;
      erw [ map_ofNat, map_ofNat, map_ofNat ] ; ring;
    have h_coeff : -(4 * (p^2 + a * q^2)) = 0 ∧ -(8 * p * q) = 1 := by
      convert quad_indep pb hdim ( show algebraMap K F ( - ( 4 * ( p ^ 2 + a * q ^ 2 ) ) ) + algebraMap K F ( - ( 8 * p * q ) - 1 ) * pb.gen = 0 from ?_ ) using 1;
      · rw [ sub_eq_zero ];
      · convert sub_eq_zero.mpr h_eq using 1 ; simp +decide [ sub_mul ] ; ring!;
    have h_a : a = -(4 * (1 / (4 * q))^4) := by
      by_cases hq : q = 0 <;> simp +decide [ hq, mul_assoc, mul_left_comm ] at h_coeff ⊢
      generalize_proofs at *;
      by_cases h4 : ( 4 : K ) = 0 <;> simp +decide [ h4 ] at h_coeff ⊢
      generalize_proofs at *; (
      exact False.elim ( hchar ( by rw [ show ( 4 : K ) = 2 * 2 by norm_num, mul_eq_zero ] at h4; tauto ) ));
      grind +revert
    exact h2 (1 / (4 * q)) h_a

/-- The pure 2-power irreducibility, by induction on `k ≥ 1`, carrying the two
Vahlen–Capelli conditions (`a` not a square, `a ∉ -4·K⁴`) and `2 ≠ 0`.
The step uses `X_pow_mul_sub_C_irreducible` with `m = 2`, reducing to the descent
lemma on the quadratic extension `K(√a)`. -/
lemma two_power_irred : ∀ (k : ℕ), 1 ≤ k → ∀ {K : Type u} [Field K] {a : K},
    (2 : K) ≠ 0 → (∀ b : K, b ^ 2 ≠ a) → (∀ b : K, a ≠ -(4 * b ^ 4)) →
    Irreducible (X ^ 2 ^ k - C a : K[X]) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n IH =>
    intro _ K _ a hchar h1 h2
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- base case `k = 1`: `X ^ 2 - C a` irreducible since `a` is not a square
      subst hn
      simpa using X_pow_sub_C_irreducible_of_prime Nat.prime_two h1
    · -- step: `2 ^ (n+1) = 2 ^ n * 2`, apply `X_pow_mul_sub_C_irreducible`
      have hkey : Irreducible (X ^ (2 ^ n * 2) - C a : K[X]) := by
        apply X_pow_mul_sub_C_irreducible
            (X_pow_sub_C_irreducible_of_prime Nat.prime_two h1)
        intro E _ _ x hx
        -- `x` is integral with `minpoly = X ^ 2 - C a`
        have hxint : IsIntegral K x := by
          by_contra h
          simp only [minpoly.eq_zero h] at hx
          have := congrArg Polynomial.natDegree hx
          simp at this
        set pb := adjoin.powerBasis hxint with hpb
        have hdim : pb.dim = 2 := by
          rw [hpb, adjoin.powerBasis_dim, hx, natDegree_X_pow_sub_C]
        have hgen : pb.gen ^ 2 = algebraMap K K⟮x⟯ a := by
          have h0 := minpoly.aeval K pb.gen
          rw [hpb, adjoin.powerBasis_gen, minpoly_gen, hx] at h0
          simpa [sub_eq_zero] using h0
        have hchar' : (2 : K⟮x⟯) ≠ 0 := by
          rw [← map_ofNat (algebraMap K K⟮x⟯) 2]
          exact (_root_.map_ne_zero _).mpr hchar
        obtain ⟨hs1, hs2⟩ := descent pb hdim hchar hgen h1 h2
        have := IH hn hchar' hs1 hs2
        rwa [hpb, adjoin.powerBasis_gen] at this
      rw [pow_succ]; exact hkey

/-- **Pure 2-power Vahlen–Capelli base, residual `−a ∈ K²` branch.**
For a field `K` and `a : K` with `a` not a square, `a ∉ −4·K⁴`, and `−a` a square,
the binomial `X^(2^k) − a` is irreducible over `K` for every `k ≥ 3`.

This is the sole `sorry` of the full Vahlen–Capelli formalization and matches Mathlib's
open even-case `TODO` (`X_pow_sub_C_irreducible_of_prime_pow` is stated only for `p ≠ 2`). -/
theorem two_power_capelli_neg_square {K : Type*} [Field K] {k : ℕ} (hk : 3 ≤ k) {a : K}
    (h1 : ∀ b : K, b ^ 2 ≠ a) (h2 : ∀ b : K, a ≠ -(4 * b ^ 4))
    (hna : ∃ c : K, c ^ 2 = -a) :
    Irreducible (X ^ 2 ^ k - C a : K[X]) := by
  -- `2 ≠ 0`: otherwise `char K = 2`, so `-a = a` and `hna` would make `a` a square.
  have hchar : (2 : K) ≠ 0 := by
    intro h2z
    obtain ⟨c, hc⟩ := hna
    exact h1 c (by rw [hc]; linear_combination -a * h2z)
  exact two_power_irred k (by omega) hchar h1 h2

-- Proof attempt: a sketch of the classical Lang VI §9 Galois descent. Aristotle is free
-- to ignore this; it seeds the MCTS prior.
-- 1. Obtain `c` with `c² = −a`. Since `a` is not a square, `−1` is not a square in `K`
--    either: if `i² = −1` then `(i·c)² = i²·c² = (−1)(−a) = a`, contradicting `h1`. So
--    `X² + 1` is irreducible and `L := K(i)` is a genuine quadratic extension.
-- 2. Over `L`, `a = (i·c)²` becomes a square, so the pure 2-power tower splits:
--    `X^(2^k) − a = (X^(2^(k−1)) − (i·c))·(X^(2^(k−1)) + (i·c))` over `L`.
-- 3. Reduce, via `X_pow_mul_sub_C_irreducible` / the prime-power Kummer machinery
--    (`X^(2^k) = (X²)^(2^(k−1))`), to showing a root `x` with `x^(2^(k−1)) = a` is NOT a
--    square in `K(x)`. This is where condition (2) is indispensable.
-- 4. If `x = y²` for some `y ∈ K(x)`, tracing norms/traces down the tower produces a
--    factorisation of the `x⁴ + 4t⁴` (Sophie–Germain) shape, i.e. exhibits `a ∈ −4·K⁴`,
--    contradicting `h2`. Hence `x` is not a square, the extension degree is full `2^k`,
--    and `X^(2^k) − a` is irreducible.
-- Key Mathlib entry points likely useful: `X_pow_sub_C_irreducible_iff_of_prime`,
-- `X_pow_mul_sub_C_irreducible`, `irreducible_X_sq_add_one` / quadratic-extension lemmas,
-- `Algebra.norm`, `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`.

end CubeRoot3IrrationalOQ02OQ03Statement