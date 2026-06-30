/-
  The Full Frobenius/Jacobi Zolotarev Lemma for Squarefree Odd Moduli:
  sign(x ↦ a·x on ℤ/n) = J(a | n)  for every odd squarefree n.
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01)

  Open Question (the explicit next step left by the parent oq-01-oq-03-oq-01):

    The parent (`ElementaryQuadraticReciprocityOQ01OQ03OQ01`, namespace
    `ZolotarevBaseCase`) proved the BASE CASE

        sign(ringMulPerm a on ZMod p) = legendreSym p a     (p prime),

    and combined it with the CRT multiplicativity of the grandparent
    (`ZolotarevCRT.sign_ringMulPerm_mul_of_odd`) to close the loop for a
    TWO-PRIME modulus `p*q`.  It explicitly left as a follow-up the fully
    general statement for an arbitrary squarefree odd modulus, "a routine
    induction over the prime factorization adding no new idea."

  This file performs exactly that induction and lands on Mathlib's actual
  `jacobiSym` (`J(a | n)`), giving the genuine Frobenius (1914) generalization
  of Zolotarev's lemma:

        sign(ringMulPerm a on ZMod n) = J(a | n)   for n odd, squarefree.

  0 sorries, 0 axioms.

  ## The argument

  Strong induction on `n` via its smallest prime factor `p = n.minFac`,
  recursing on the cofactor `m = n / p`:

  * `n = 1`: `ZMod 1` is a subsingleton, so the permutation is the identity,
    its sign is `1`, and `J(a | 1) = 1`.
  * `n = p * m` with `p` prime, `Coprime p m` (because `n` is squarefree),
    both odd, `m < n`:
        sign(ringMulPerm a)
          = sign(ringMulPerm a₁) * sign(ringMulPerm a₂)   [CRT, `_mul_of_odd`]
          = legendreSym p a * J(a | m)                     [base case + IH]
          = J(a | p) * J(a | m)                            [`legendre_eq_jacobi`]
          = J(a | p * m) = J(a | n).                       [`jacobiSym.mul_right`]

  The only arithmetic input beyond the parents is the bookkeeping that an odd
  squarefree number splits off its smallest prime factor coprimely.

  ## Honest scope

  This closes the squarefree case completely and unconditionally.  The
  remaining prime-power factors `p^e` (`e ≥ 2`) of a fully general odd `n` are
  NOT handled — the Chinese Remainder Theorem only separates *coprime* factors,
  and the sign of multiplication on `ZMod (p^e)` is a genuinely different
  computation (not bookkeeping); it is left to a follow-up.  No new axioms are
  introduced.

  References:
  - Zolotarev (1872); Frobenius (1914); Rousseau (1991), Amer. Math. Monthly.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01

set_option maxHeartbeats 1600000

namespace ZolotarevSquarefree

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm ringMulPerm_apply sign_ringMulPerm_mul_of_odd legendre_eq_jacobi)
open scoped NumberTheorySymbols

/-
═══════════════════════════════════════════════════════════════════════════════
PART 0: THE INTEGER UNIT FROM A COPRIMALITY HYPOTHESIS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- If an integer `c` is coprime to `k`, its image `(c : ZMod k)` is a unit.
    Bezout: `x·c + y·k = 1` reduces mod `k` to `x·c = 1`. -/
theorem intCast_isUnit_of_isCoprime {k : ℕ} {c : ℤ} (h : IsCoprime c (k : ℤ)) :
    IsUnit ((c : ℤ) : ZMod k) := by
  obtain ⟨x, y, hxy⟩ := h
  have hcast : ((x * c + y * (k : ℤ) : ℤ) : ZMod k) = ((1 : ℤ) : ZMod k) := by
    rw [hxy]
  push_cast at hcast
  simp only [ZMod.natCast_self, mul_zero, add_zero] at hcast
  exact ⟨⟨((c : ℤ) : ZMod k), ((x : ℤ) : ZMod k), by rw [mul_comm]; exact hcast, hcast⟩, rfl⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE MAIN INDUCTION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Frobenius/Jacobi Zolotarev lemma for squarefree odd moduli.**
    For an odd squarefree `n`, an integer `c` coprime to `n`, and the unit
    `u : (ZMod n)ˣ` represented by `c`, the sign of the multiplication-by-`u`
    permutation of the whole ring `ZMod n` equals the Jacobi symbol `J(c | n)`. -/
theorem main : ∀ (n : ℕ) [NeZero n], 0 < n → Odd n → Squarefree n →
    ∀ (c : ℤ), IsCoprime c (n : ℤ) → ∀ (u : (ZMod n)ˣ),
      (u : ZMod n) = (c : ZMod n) →
      ((Equiv.Perm.sign (ringMulPerm u) : ℤ)) = J(c | n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _inst hn hodd hsf c hcop u hu
    by_cases hn1 : n = 1
    · -- Base of the recursion: ZMod 1 is a subsingleton.
      subst hn1
      have hsign : Equiv.Perm.sign (ringMulPerm u) = 1 := by
        have : ringMulPerm u = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [hsign, Units.val_one, jacobiSym.one_right]
    · -- Inductive step: peel off the smallest prime factor.
      have hn2 : 1 < n := by omega
      obtain ⟨p, m, hp, hcop_pm, hm0, hpm⟩ :
          ∃ p m, p.Prime ∧ Nat.Coprime p m ∧ 0 < m ∧ p * m = n := by
        refine ⟨n.minFac, n / n.minFac, Nat.minFac_prime hn1, ?_, ?_, ?_⟩
        · rw [(Nat.minFac_prime hn1).coprime_iff_not_dvd]
          intro hdvd
          have h2 : n.minFac * n.minFac ∣ n := by
            have hd := mul_dvd_mul_left n.minFac hdvd
            rwa [Nat.mul_div_cancel' (Nat.minFac_dvd n)] at hd
          exact (Nat.minFac_prime hn1).ne_one (Nat.isUnit_iff.mp (hsf _ h2))
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)) (Nat.minFac_pos n)
        · exact Nat.mul_div_cancel' (Nat.minFac_dvd n)
      subst hpm
      -- Local instances and arithmetic facts about the two factors.
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      haveI : NeZero m := ⟨hm0.ne'⟩
      obtain ⟨hodd_p, hodd_m⟩ := Nat.odd_mul.mp hodd
      have hp2 : p ≠ 2 := by rintro rfl; norm_num at hodd_p
      have hsf_m : Squarefree m := hsf.squarefree_of_dvd (dvd_mul_left m p)
      have hmlt : m < p * m := (Nat.lt_mul_iff_one_lt_left hm0).mpr hp.one_lt
      -- Split the coprimality across the factorization.
      rw [Nat.cast_mul] at hcop
      have hcop_p : IsCoprime c (p : ℤ) := hcop.of_mul_right_left
      have hcop_m : IsCoprime c (m : ℤ) := hcop.of_mul_right_right
      -- The CRT component units.
      set u₁ : (ZMod p)ˣ := (intCast_isUnit_of_isCoprime hcop_p).unit with hu₁def
      set u₂ : (ZMod m)ˣ := (intCast_isUnit_of_isCoprime hcop_m).unit with hu₂def
      have hu₁ : (u₁ : ZMod p) = (c : ZMod p) := IsUnit.unit_spec _
      have hu₂ : (u₂ : ZMod m) = (c : ZMod m) := IsUnit.unit_spec _
      -- Component-matching hypotheses for the CRT lemma.
      have h₁ : (u₁ : ZMod p)
          = ((ZMod.chineseRemainder hcop_pm) (u : ZMod (p * m))).1 := by
        rw [hu₁, hu]; simp [map_intCast]
      have h₂ : (u₂ : ZMod m)
          = ((ZMod.chineseRemainder hcop_pm) (u : ZMod (p * m))).2 := by
        rw [hu₂, hu]; simp [map_intCast]
      -- CRT multiplicativity of the sign.
      have key : Equiv.Perm.sign (ringMulPerm u)
          = Equiv.Perm.sign (ringMulPerm u₁) * Equiv.Perm.sign (ringMulPerm u₂) :=
        sign_ringMulPerm_mul_of_odd hcop_pm hodd_p hodd_m u u₁ u₂ h₁ h₂
      have key' : ((Equiv.Perm.sign (ringMulPerm u) : ℤ))
          = ((Equiv.Perm.sign (ringMulPerm u₁) : ℤ))
              * ((Equiv.Perm.sign (ringMulPerm u₂) : ℤ)) := by
        rw [key]; push_cast; ring
      -- The prime part is the base case; the cofactor part is the IH.
      have hp_part : ((Equiv.Perm.sign (ringMulPerm u₁) : ℤ)) = J(c | p) := by
        rw [ZolotarevBaseCase.sign_ringMulPerm_eq_legendre hp2 u₁]
        have hbridge : legendreSym p ((u₁ : ZMod p).val : ℤ) = legendreSym p c := by
          rw [ZolotarevBaseCase.legendreSym_unit_eq u₁, hu₁]; rfl
        rw [hbridge, legendre_eq_jacobi p c]
      have hm_part : ((Equiv.Perm.sign (ringMulPerm u₂) : ℤ)) = J(c | m) :=
        ih m hmlt hm0 hodd_m hsf_m c hcop_m u₂ hu₂
      rw [key', hp_part, hm_part, ← jacobiSym.mul_right c p m]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: CLEAN STATEMENT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Zolotarev–Frobenius for squarefree odd `n`** (clean binder form). -/
theorem sign_ringMulPerm_eq_jacobiSym {n : ℕ} [NeZero n] (hn : 0 < n)
    (hodd : Odd n) (hsf : Squarefree n) (c : ℤ) (hcop : IsCoprime c (n : ℤ))
    (u : (ZMod n)ˣ) (hu : (u : ZMod n) = (c : ZMod n)) :
    ((Equiv.Perm.sign (ringMulPerm u) : ℤ)) = J(c | n) :=
  main n hn hodd hsf c hcop u hu

end ZolotarevSquarefree

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The full squarefree-odd Frobenius/Jacobi Zolotarev lemma
   (answering oq-01-oq-03-oq-01's listed next step)

### What's proved (0 sorries, 0 axioms):
- `intCast_isUnit_of_isCoprime`: a small Bezout bridge — an integer coprime to
  `k` casts to a unit of `ZMod k` (used to manufacture the CRT component units).
- `main` / `sign_ringMulPerm_eq_jacobiSym`: for every ODD SQUAREFREE `n` and
  integer `c` coprime to `n`,
      sign(ringMulPerm c on ZMod n) = J(c | n),
  the genuine Frobenius generalization of Zolotarev's lemma, landing on
  Mathlib's `jacobiSym`.  Proof = strong induction on `n` via its smallest
  prime factor, combining the parent's base case (`sign(·) = legendreSym`) with
  the grandparent's CRT multiplicativity (`sign_ringMulPerm_mul_of_odd`) and
  `jacobiSym.mul_right`.

### Honest scope:
Squarefree odd moduli only.  Prime-power factors `p^e` (`e ≥ 2`) need a separate
argument (CRT does not split them, and the sign on `ZMod (p^e)` is a new
computation) — left to a follow-up.  No new axioms.

### Key insight:
The general odd-squarefree statement is exactly the recursive structure of the
Jacobi symbol itself: `jacobiSym.mul_right` (denominator multiplicativity) is the
value-level shadow of `sign_ringMulPerm_mul_of_odd` (CRT multiplicativity of the
permutation sign), and the recursion bottoms out at the single prime base case.
-/

#check @ZolotarevSquarefree.intCast_isUnit_of_isCoprime
#check @ZolotarevSquarefree.main
#check @ZolotarevSquarefree.sign_ringMulPerm_eq_jacobiSym
