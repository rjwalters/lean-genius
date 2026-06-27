import Mathlib.Tactic
import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-
# Gauss-Wilson → the quadratic character: the half-factorial bridge (OQ-02-ext OQ-03)

**Open question (`wilsons-theorem-oq-02-ext-oq-03`).** The parent Gauss-Wilson work
establishes the value of the product of all units of `(ZMod p)ˣ`, namely Wilson's
law `∏_{u} u = (p-1)! = -1`. The research goal of this node is the *bridge* that
connects that product to the **quadratic character** / Legendre symbol: an explicit
formula relating the value of `(p-1)!` to a square root of `-1` modulo `p`.

Mathlib already contains the quadratic-residue machinery downstream of this bridge
(`ZMod.exists_sq_eq_neg_one_iff`, `legendreSym`, `legendreSym.at_neg_one`,
`ZMod.euler_criterion`, quadratic reciprocity). What is *absent* is the classical
elementary link from Wilson's product to that machinery: the **half-factorial
identity**

  `(((p-1)/2)!)² ≡ (-1)^((p-1)/2 + 1)  (mod p)`,

obtained by folding the product `(p-1)! = ∏_{k=1}^{p-1} k` along the involution
`k ↦ p - k`. Each pair contributes `k·(p-k) ≡ -k²`, so

  `(p-1)! ≡ (-1)^{(p-1)/2} · (((p-1)/2)!)²  (mod p)`,

and Wilson's `(p-1)! ≡ -1` solves for the half-factorial square.

## Why this is the bridge to the Legendre symbol

Writing `m = (p-1)/2`, the identity says `(m!)² ≡ (-1)^{m+1}`. The sign is governed
entirely by `p mod 4`:

  * `p ≡ 1 (mod 4)` ⟹ `m` even ⟹ `(m!)² ≡ -1`: the number `m!` is an **explicit
    square root of `-1`** modulo `p`. This *constructs* the witness whose mere
    existence is `ZMod.exists_sq_eq_neg_one_iff`, and pins down `legendreSym p (-1) = 1`.
  * `p ≡ 3 (mod 4)` ⟹ `m` odd ⟹ `(m!)² ≡ 1`: here `m! ≡ ±1` and `-1` is a non-residue.

So the single product `(p-1)!` from Gauss-Wilson, read through one involution,
produces the value of `(-1/p)` together with an *effective* square root in the
residue case — the elementary input to `legendreSym p (-1) = χ₄ p`.

## Main results

  * `factorial_half_sq` : `(((p/2)! : ZMod p))² = (-1)^(p/2 + 1)` (the bridge identity).
  * `factorial_half_sq_eq_neg_one` : `p % 4 = 1 → (((p/2)! : ZMod p))² = -1`.
  * `factorial_half_sq_eq_one`     : `p % 4 = 3 → (((p/2)! : ZMod p))² = 1`.
  * `isSquare_neg_one_of_mod_four` : `p % 4 = 1 → IsSquare (-1 : ZMod p)`, with the
    *explicit* witness `(p/2)!` (constructive form of `ZMod.exists_sq_eq_neg_one_iff`).
  * `legendreSym_neg_one_eq_one`   : `p % 4 = 1 → legendreSym p (-1) = 1`, derived from
    the explicit square root rather than from `χ₄`.

All proofs are elementary: Wilson's lemma plus a single reflection of the factorial
product. Zero axioms, zero sorries.
-/

namespace WilsonsTheoremOQ02ExtOQ03

open Finset ZMod

variable (p : ℕ) [Fact p.Prime]

/-- **The half-factorial bridge identity.** For an odd prime `p`, writing `m = p/2`
(so `p = 2m+1` and `m = (p-1)/2`), the square of the half-factorial `m!` modulo `p`
equals `(-1)^(m+1)`. This is the elementary consequence of Wilson's theorem obtained
by pairing `k` with `p - k` in the product `(p-1)! = ∏_{k=1}^{p-1} k`. -/
theorem factorial_half_sq (hodd : p % 2 = 1) :
    (((p / 2)! : ZMod p)) ^ 2 = (-1) ^ (p / 2 + 1) := by
  classical
  set m := p / 2 with hm
  have hp_eq : p = 2 * m + 1 := by omega
  have hpm1 : p - 1 = 2 * m := by omega
  -- The pairing identity: `(2m)! ≡ (-1)^m · (m!)²` in `ZMod p`.
  have key : ((2 * m)! : ZMod p) = (-1) ^ m * ((m)! : ZMod p) ^ 2 := by
    -- Cast `(2m)!` to a product over `Ico 1 (2m+1)` and split at `m+1`.
    have e1 : ((2 * m)! : ZMod p) = ∏ x ∈ Ico 1 (2 * m + 1), (x : ZMod p) := by
      rw [← Finset.prod_Ico_id_eq_factorial (2 * m), Finset.prod_natCast]
    have hsplit :
        (∏ x ∈ Ico 1 (m + 1), (x : ZMod p)) * (∏ x ∈ Ico (m + 1) (2 * m + 1), (x : ZMod p))
          = ∏ x ∈ Ico 1 (2 * m + 1), (x : ZMod p) :=
      Finset.prod_Ico_consecutive (fun x => (x : ZMod p)) (by omega) (by omega)
    -- Lower half is `m!`.
    have hL : (∏ x ∈ Ico 1 (m + 1), (x : ZMod p)) = ((m)! : ZMod p) := by
      rw [← Finset.prod_natCast, Finset.prod_Ico_id_eq_factorial]
    -- Upper half: reindex `k ↦ p - k`, each term becomes `-(↑(m-k))`.
    have hU : (∏ x ∈ Ico (m + 1) (2 * m + 1), (x : ZMod p)) = (-1) ^ m * ((m)! : ZMod p) := by
      rw [Finset.prod_Ico_eq_prod_range]
      have hlen : 2 * m + 1 - (m + 1) = m := by omega
      rw [hlen]
      -- replace `↑(m+1+k)` by `-↑(m-k)`
      have hterm : ∀ k ∈ range m, ((m + 1 + k : ℕ) : ZMod p) = - ((m - k : ℕ) : ZMod p) := by
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        have hnat : (m + 1 + k : ℕ) = p - (m - k) := by omega
        rw [hnat, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      rw [Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.card_range]
      -- remaining `∏ k ∈ range m, ↑(m-k) = ↑(m!)`
      congr 1
      rw [← Finset.prod_natCast]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial,
          ← Finset.prod_range_reflect (fun i => i + 1) m]
      refine Finset.prod_congr rfl ?_
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      show m - k = m - 1 - k + 1
      omega
    rw [e1, ← hsplit, hL, hU]
    ring
  -- Wilson's lemma supplies `(2m)! ≡ -1`.
  have wil : ((2 * m)! : ZMod p) = -1 := by
    have h := ZMod.wilsons_lemma p
    rwa [hpm1] at h
  -- Solve `(-1)^m · (m!)² = -1` for `(m!)²`.
  have hcombine : (-1 : ZMod p) ^ m * ((m)! : ZMod p) ^ 2 = -1 := by rw [← key]; exact wil
  have hsq : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc ((m)! : ZMod p) ^ 2
      = (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m * ((m)! : ZMod p) ^ 2) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ZMod p) ^ m * (-1) := by rw [hcombine]
    _ = (-1 : ZMod p) ^ (m + 1) := by rw [pow_succ]

/-- For `p ≡ 1 (mod 4)`, the half-factorial `(p/2)!` is an explicit square root of
`-1` modulo `p`. -/
theorem factorial_half_sq_eq_neg_one (hp4 : p % 4 = 1) :
    (((p / 2)! : ZMod p)) ^ 2 = -1 := by
  have hodd : p % 2 = 1 := by omega
  have : p / 2 % 2 = 0 := by omega
  rw [factorial_half_sq p hodd]
  rcases Nat.even_or_odd (p / 2) with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [show p / 2 + 1 = 2 * t + 1 by omega, pow_succ, pow_mul]; simp
  · omega

/-- For `p ≡ 3 (mod 4)`, the half-factorial squares to `1` modulo `p`. -/
theorem factorial_half_sq_eq_one (hp4 : p % 4 = 3) :
    (((p / 2)! : ZMod p)) ^ 2 = 1 := by
  have hodd : p % 2 = 1 := by omega
  rw [factorial_half_sq p hodd]
  rcases Nat.even_or_odd (p / 2) with ⟨t, ht⟩ | ⟨t, ht⟩
  · omega
  · rw [show p / 2 + 1 = 2 * (t + 1) by omega, pow_mul]; simp

/-- **Constructive `−1` is a square.** For `p ≡ 1 (mod 4)`, `-1` is a square in
`ZMod p`, with the explicit witness `(p/2)!`. This is the effective form of
`ZMod.exists_sq_eq_neg_one_iff` produced by the Wilson bridge. -/
theorem isSquare_neg_one_of_mod_four (hp4 : p % 4 = 1) : IsSquare (-1 : ZMod p) := by
  refine ⟨((p / 2)! : ZMod p), ?_⟩
  have := factorial_half_sq_eq_neg_one p hp4
  rw [← this]; ring

/-- **Bridge to the Legendre symbol.** For `p ≡ 1 (mod 4)`, `legendreSym p (-1) = 1`,
derived here from the explicit Wilson square root `(p/2)!` rather than from `χ₄`. -/
theorem legendreSym_neg_one_eq_one (hp4 : p % 4 = 1) :
    legendreSym p (-1) = 1 := by
  have hcast : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; ring
  have ha0 : ((-1 : ℤ) : ZMod p) ≠ 0 := by
    rw [hcast]; exact neg_ne_zero.mpr one_ne_zero
  have hsq : IsSquare ((-1 : ℤ) : ZMod p) := by
    rw [hcast]; exact isSquare_neg_one_of_mod_four p hp4
  exact (legendreSym.eq_one_iff p ha0).mpr hsq

end WilsonsTheoremOQ02ExtOQ03
