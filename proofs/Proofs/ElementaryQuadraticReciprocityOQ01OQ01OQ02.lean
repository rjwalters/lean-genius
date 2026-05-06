/-
  # Frobenius Step in the Gauss Sum Proof of Quadratic Reciprocity
  # (elementary-quadratic-reciprocity-oq-01-oq-01-oq-02)

  **Step 3 of the Gauss sum pathway**: τ^q = χ(q) · τ  in a field of characteristic q

  Context: `ElementaryQuadraticReciprocityOQ01OQ01.lean` outlines four steps:
    Step 1: Define τ = Σ_a (a/p)·ζ^a  (classical Gauss sum)
    Step 2: τ² = χ(-1) · p            [proved in OQ01OQ01OQ01.lean]
    Step 3: τ^q = χ(q) · τ            ← THIS FILE
    Step 4: Compare τ^q two ways → QR follows

  ## The Frobenius Step

  Working in a field F of characteristic q (q ≠ p, both odd primes), the Frobenius
  endomorphism φ : F → F (x ↦ x^q) is a ring homomorphism. Applied to the Gauss sum:

      τ^q = (Σ_a χ(a)ψ(a))^q = Σ_a χ(a)^q ψ(a)^q   (freshman's dream in char q)
          = Σ_a χ(a) ψ(qa)                            (χ(a)^q = χ(a) since χ quadratic)
          = χ(q) · Σ_a χ(a) ψ(a)                     (reparametrize: b = qa)
          = χ(q) · τ

  ## From Frobenius to Quadratic Reciprocity

  Combining Steps 2 and 3:
    - τ^q = τ · (τ²)^{(q-1)/2} = τ · (χ(-1)·p)^{(q-1)/2}
    - τ^q = χ(q) · τ
    - Therefore: χ(q) = (χ(-1)·p)^{(q-1)/2}

  With χ(-1) = (-1/p) = (-1)^{(p-1)/2} and p^{(q-1)/2} ≡ (p/q) (mod q):
    (q/p) = (-1)^{((p-1)/2)·((q-1)/2)} · (p/q)

  This is the Law of Quadratic Reciprocity.

  ## Key Mathlib Theorems Used

  - `MulChar.IsQuadratic.gaussSum_frob`: τ^q = χ(q)·τ in char q ring (direct)
  - `Char.card_pow_char_pow`: (χ(-1)·p)^{q/2} = χ(q) (combining Steps 2 and 3)
  - `Char.card_pow_card`: Full QR identity in finite fields

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

open MulChar AddChar ZMod

namespace FrobeniusStepQR

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

-- ============================================================================
-- Auxiliary: q is a unit in ZMod p for distinct primes p ≠ q
-- ============================================================================

/-- For distinct primes p ≠ q, the element (q : ZMod p) is a unit.
    Since gcd(p, q) = 1, q is invertible modulo p. -/
private lemma q_isUnit_in_ZMod_p (hpq : p ≠ q) : IsUnit (q : ZMod p) := by
  -- isUnit_prime_iff_not_dvd (hp : p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n
  -- Here p_Mathlib = q, n_Mathlib = p, so: IsUnit (q : ZMod p) ↔ ¬(q ∣ p)
  rw [ZMod.isUnit_prime_iff_not_dvd hq.out]
  intro h  -- h : q ∣ p
  -- hp.out.eq_one_or_self_of_dvd q h : q = 1 ∨ q = p
  exact hpq ((hp.out.eq_one_or_self_of_dvd q h).resolve_left hq.out.one_lt.ne').symm

-- ============================================================================
-- Part I: The Frobenius Step (Main Theorem)
-- ============================================================================

/-- **Frobenius Step** — Step 3 of the Gauss sum QR pathway.

    In a field F of characteristic q, for any quadratic character χ : ZMod p → F
    and additive character ψ : ZMod p → F (p ≠ q distinct primes):

        (gaussSum χ ψ)^q = χ(q) · (gaussSum χ ψ)

    This is a direct consequence of Mathlib's `MulChar.IsQuadratic.gaussSum_frob`,
    which implements the Frobenius argument:
    (1) The Frobenius map x ↦ x^q is a ring endomorphism in characteristic q.
    (2) Applied to the Gauss sum: τ^q = Σ_a χ(a)^q ψ(a)^q = Σ_a χ(a) ψ(qa).
    (3) Reparametrizing b = qa (which is a bijection since q is a unit mod p):
        = χ(q)⁻¹ Σ_b χ(b) ψ(b) = χ(q) · τ  (as χ(q) = ±1, so χ(q)⁻¹ = χ(q)). -/
theorem frobenius_step {F : Type*} [Field F] [Fintype F] [CharP F q]
    (χ : MulChar (ZMod p) F) (hχ : χ.IsQuadratic)
    (ψ : AddChar (ZMod p) F) (hpq : p ≠ q) :
    gaussSum χ ψ ^ q = χ q * gaussSum χ ψ :=
  hχ.gaussSum_frob q (q_isUnit_in_ZMod_p hpq) ψ

-- ============================================================================
-- Part II: Combining Steps 2 and 3 to Get the Key QR Identity
-- ============================================================================

/-- **QR Identity via Frobenius** (Mathlib's Char.card_pow_char_pow with n = 1):

    If we are given that τ² = χ(-1) · p (the Gauss sum squared identity),
    then in a field F of characteristic q (q odd, q ≠ p):

        (χ(-1) · |ZMod p|)^((q-1)/2) = χ(q)

    Derivation:
    - From Frobenius: τ^q = χ(q) · τ (Part I above)
    - From Step 2 (hypothesis): τ² = χ(-1) · p
    - So τ^q = τ · (τ²)^{(q-1)/2} = τ · (χ(-1)·p)^{(q-1)/2}
    - Equating: χ(q) · τ = τ · (χ(-1)·p)^{(q-1)/2}
    - Since τ ≠ 0 (for primitive ψ): (χ(-1)·p)^{(q-1)/2} = χ(q). -/
theorem qr_via_frobenius {F : Type*} [Field F] [Fintype F] [CharP F q]
    (χ : MulChar (ZMod p) F) (hχ : χ.IsQuadratic)
    (ψ : AddChar (ZMod p) F) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hτ_sq : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card (ZMod p)) :
    (χ (-1) * (Fintype.card (ZMod p) : F)) ^ (q / 2) = χ q := by
  have hq_unit := q_isUnit_in_ZMod_p hpq
  have h := Char.card_pow_char_pow hχ ψ q 1 hq_unit hq2 hτ_sq
  simpa [pow_one] using h

-- ============================================================================
-- Part III: Quadratic Reciprocity via Gauss Sums (Finite Field Version)
-- ============================================================================

/-- **Quadratic Reciprocity Identity in ZMod q** (Char.card_pow_card):

    For distinct odd primes p ≠ q and a nontrivial quadratic character χ : ZMod p → ZMod q:

        (χ(-1) · p)^((q-1)/2) = χ(q)   in ZMod q

    Mathematical interpretation:
    - χ(-1) = (-1/p) = (-1)^{(p-1)/2}  [Legendre symbol of -1 mod p]
    - p^{(q-1)/2} ≡ (p/q) (mod q)      [Euler's criterion for Legendre symbol]
    - χ(q) = (q/p)                      [Legendre symbol of q mod p]

    So this identity reads: (-1)^{((p-1)/2)·((q-1)/2)} · (p/q) = (q/p) in ZMod q,
    which is exactly the Law of Quadratic Reciprocity. -/
theorem qr_gauss_sums_identity (χ : MulChar (ZMod p) (ZMod q)) (hχ₁ : χ ≠ 1)
    (hχ₂ : χ.IsQuadratic) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    (χ (-1) * Fintype.card (ZMod p)) ^ (Fintype.card (ZMod q) / 2) =
    χ (Fintype.card (ZMod q)) := by
  apply Char.card_pow_card hχ₁ hχ₂
  · rw [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n]
    exact_mod_cast hpq.symm
  · rw [ZMod.ringChar_zmod_n]
    exact_mod_cast hq2

-- ============================================================================
-- Part IV: The Full QR Pathway Summary
-- ============================================================================

/-- **Summary of the Gauss Sum QR Pathway**:

    Steps 1-4 with explicit Lean witnesses:
    - Step 1: Gauss sum τ = gaussSum χ ψ (for any χ, ψ)
    - Step 2: τ² = χ(-1)·p  [proved in OQ01OQ01OQ01 via `gaussSum_sq`]
    - Step 3: τ^q = χ(q)·τ  [proved above via `gaussSum_frob`]
    - Step 4: Comparing τ^q two ways gives `qr_gauss_sums_identity`

    The full derivation:
    - Char.card_pow_card (which internally uses gaussSum_frob + gaussSum_sq)
    - proves (χ(-1)·p)^{(q-1)/2} = χ(q) in ZMod q.
    This encodes (p/q)·(q/p) = (-1)^{((p-1)/2)·((q-1)/2)}, i.e., QR. -/
theorem gauss_qr_pathway_complete (χ : MulChar (ZMod p) (ZMod q)) (hχ₁ : χ ≠ 1)
    (hχ₂ : χ.IsQuadratic) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    ∃ (result : (ZMod q)),
    result = χ (Fintype.card (ZMod q)) ∧
    result = (χ (-1) * Fintype.card (ZMod p)) ^ (Fintype.card (ZMod q) / 2) :=
  ⟨_, qr_gauss_sums_identity χ hχ₁ hχ₂ hpq hq2, rfl⟩

-- ============================================================================
-- Part V: Concrete Frobenius Verifications
-- ============================================================================

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- **Concrete example**: p = 5, q = 3.
    In any field of characteristic 3, the Frobenius step holds for the
    Legendre character mod 5: τ^3 = χ₅(3)·τ. -/
example {F : Type*} [Field F] [Fintype F] [CharP F 3]
    (χ : MulChar (ZMod 5) F) (hχ : χ.IsQuadratic)
    (ψ : AddChar (ZMod 5) F) :
    gaussSum χ ψ ^ 3 = χ 3 * gaussSum χ ψ :=
  frobenius_step χ hχ ψ (by norm_num)

/-- **Concrete example**: p = 7, q = 5.
    In any field of characteristic 5, the Frobenius step holds: τ^5 = χ₇(5)·τ. -/
example {F : Type*} [Field F] [Fintype F] [CharP F 5]
    (χ : MulChar (ZMod 7) F) (hχ : χ.IsQuadratic)
    (ψ : AddChar (ZMod 7) F) :
    gaussSum χ ψ ^ 5 = χ 5 * gaussSum χ ψ :=
  frobenius_step χ hχ ψ (by norm_num)

/-- **Concrete example**: p = 11, q = 7.
    QR identity: (χ₁₁(-1)·11)^3 = χ₁₁(7) in ZMod 7.
    Since 11 ≡ 4 (mod 7) and (-1/11) = 1 (as 11 ≡ 3 mod 4, (-1/11) = -1):
    QR says (11/7)·(7/11) = (-1)^{5·3} = -1. ✓ -/
example (χ : MulChar (ZMod 11) (ZMod 7)) (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic) :
    (χ (-1) * Fintype.card (ZMod 11)) ^ (Fintype.card (ZMod 7) / 2) =
    χ (Fintype.card (ZMod 7)) :=
  qr_gauss_sums_identity χ hχ₁ hχ₂ (by norm_num) (by norm_num)

end FrobeniusStepQR

/-
  ## Results Summary

  | Theorem | Statement | Proof |
  |---------|-----------|-------|
  | `q_isUnit_in_ZMod_p` | IsUnit(q : ZMod p) when p≠q prime | ZMod.isUnit_prime_iff_not_dvd |
  | `frobenius_step` | τ^q = χ(q)·τ in char-q field | gaussSum_frob (Mathlib) |
  | `qr_via_frobenius` | (χ(-1)·p)^(q/2) = χ(q) | card_pow_char_pow (Mathlib) |
  | `qr_gauss_sums_identity` | Full QR identity in ZMod q | Char.card_pow_card (Mathlib) |
  | `gauss_qr_pathway_complete` | Existence form | corollary |

  **Sorries**: 0
  **Axioms**: 0

  Answer: YES — τ^q = χ(q)·τ is formalized in Lean 4. Mathlib's gaussSum_frob
  directly proves the Frobenius step, and Char.card_pow_card derives QR from it.
-/
