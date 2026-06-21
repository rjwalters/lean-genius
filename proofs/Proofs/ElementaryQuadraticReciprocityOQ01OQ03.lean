/-
  CRT Decomposition of the Zolotarev Multiplication Permutation
  (elementary-quadratic-reciprocity-oq-01-oq-03)

  Open Question (from elementary-quadratic-reciprocity-oq-01, OQ #3):
  "Can the CRT decomposition of the multiplication permutation on ℤ/pqℤ be
  formalized to give a self-contained Zolotarev QR proof?"

  The parent (OQ-01) formalized Zolotarev's lemma for a PRIME modulus: the
  Legendre symbol (a/p) equals the sign of the permutation x ↦ ax on the
  units (ZMod p)ˣ.  Frobenius (1914) generalized this to COMPOSITE moduli and
  the Jacobi symbol, and the mechanism is the Chinese Remainder Theorem: the
  multiplication-by-a permutation on ℤ/mn factors, through the CRT ring
  isomorphism, into the product of the multiplication-by-a permutations on
  ℤ/m and ℤ/n.

  This file formalizes that decomposition. Its content (all 0 sorries, 0 axioms):

  * `ringMulPerm a` — multiplication by a unit `a` as a permutation of the
    WHOLE ring `ZMod n` (Frobenius works on all n residues, not just the units;
    crucially `|ZMod n| = n` is ODD for odd n, whereas `|(ZMod n)ˣ| = φ(n)` is
    even — and an even number of points would make every sign trivial).
  * `signRingHom : (ZMod n)ˣ →* ℤˣ` — the Zolotarev sign character for ANY
    modulus, a generalization of the parent's `signMulHom`.
  * `sign_prodCongr` — a general, Mathlib-absent lemma: the sign of a product
    permutation `σ ×ₚ τ` is `sign σ ^ |β| * sign τ ^ |α|`.
  * `sign_ringMulPerm_crt` — the CRT decomposition itself.
  * `sign_ringMulPerm_mul_of_odd` — for ODD coprime moduli the exponents are
    odd, so the sign character is genuinely MULTIPLICATIVE across the CRT
    factorization, exactly mirroring `jacobiSym.mul_right`.

  References:
  - Zolotarev (1872): Nouvelle démonstration de la loi de réciprocité de Legendre
  - Frobenius (1914): generalization to Jacobi symbols / composite moduli
  - Lerch (1896); Rousseau (1991), Amer. Math. Monthly
-/
import Mathlib

set_option maxHeartbeats 800000

namespace ZolotarevCRT

open Equiv Equiv.Perm Finset

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: MULTIPLICATION BY A UNIT AS A PERMUTATION OF THE WHOLE RING
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Multiplication by a unit `a` is a permutation of the entire ring `ZMod n`.
    Unlike the parent's `mulPerm` (which acts on the units `(ZMod p)ˣ`), this
    acts on all `n` residues — the setting required for the Frobenius/Jacobi
    generalization, since `|ZMod n| = n` is odd for odd `n`. -/
def ringMulPerm {n : ℕ} (a : (ZMod n)ˣ) : Equiv.Perm (ZMod n) where
  toFun x := (a : ZMod n) * x
  invFun x := (↑a⁻¹ : ZMod n) * x
  left_inv x := by
    simp [← mul_assoc, ← Units.val_mul]
  right_inv x := by
    simp [← mul_assoc, ← Units.val_mul]

@[simp] theorem ringMulPerm_apply {n : ℕ} (a : (ZMod n)ˣ) (x : ZMod n) :
    ringMulPerm a x = (a : ZMod n) * x := rfl

/-- `ringMulPerm` of `1` is the identity. -/
theorem ringMulPerm_one {n : ℕ} : ringMulPerm (1 : (ZMod n)ˣ) = 1 := by
  ext x; simp

/-- `ringMulPerm` is multiplicative: it is a group homomorphism. -/
theorem ringMulPerm_mul {n : ℕ} (a b : (ZMod n)ˣ) :
    ringMulPerm (a * b) = ringMulPerm a * ringMulPerm b := by
  ext x
  simp [Equiv.Perm.mul_apply, mul_assoc, Units.val_mul]

/-- The multiplication permutation as a monoid homomorphism `(ZMod n)ˣ →* Perm (ZMod n)`. -/
def ringMulPermHom {n : ℕ} : (ZMod n)ˣ →* Equiv.Perm (ZMod n) where
  toFun := ringMulPerm
  map_one' := ringMulPerm_one
  map_mul' := ringMulPerm_mul

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE ZOLOTAREV SIGN CHARACTER FOR ANY MODULUS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Zolotarev sign character `(ZMod n)ˣ →* ℤˣ`, defined for ANY (positive)
    modulus `n` (the parent only had the prime case). -/
def signRingHom {n : ℕ} [NeZero n] : (ZMod n)ˣ →* ℤˣ :=
  (Equiv.Perm.sign).comp ringMulPermHom

@[simp] theorem signRingHom_apply {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) :
    signRingHom a = Equiv.Perm.sign (ringMulPerm a) := rfl

/-- The sign character is a quadratic character: it squares to the identity. -/
theorem signRingHom_sq {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) : signRingHom a ^ 2 = 1 := by
  simp only [signRingHom_apply]
  exact Int.units_sq _

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SIGN OF A PRODUCT PERMUTATION  (general, absent from Mathlib)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For a unit of `ℤ` and an odd exponent, the power is the unit itself
    (since `ℤˣ = {±1}` has exponent 2). -/
theorem units_pow_odd (u : ℤˣ) {k : ℕ} (hk : Odd k) : u ^ k = u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_pow]
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    simpa using hk.neg_one_pow

/-- The sign of a product permutation `σ ×ₚ τ` on `α × β` is
    `sign σ ^ |β| * sign τ ^ |α|`.  This is not in Mathlib; we derive it from
    `sign_prodCongrLeft` and `sign_prodCongrRight` applied to constant families. -/
theorem sign_prodCongr {α β : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Equiv.Perm.sign (σ.prodCongr τ)
      = Equiv.Perm.sign σ ^ Fintype.card β * Equiv.Perm.sign τ ^ Fintype.card α := by
  have hdecomp : σ.prodCongr τ
      = prodCongrLeft (fun _ : β => σ) * prodCongrRight (fun _ : α => τ) := by
    apply Equiv.ext
    rintro ⟨a, b⟩
    simp [Equiv.Perm.mul_apply,
      prodCongrLeft_apply, prodCongrRight_apply, Equiv.prodCongr_apply, Prod.map_apply']
  rw [hdecomp, map_mul, sign_prodCongrLeft, sign_prodCongrRight]
  simp [Finset.prod_const, Finset.card_univ]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE CRT DECOMPOSITION
═══════════════════════════════════════════════════════════════════════════════ -/

variable {m n : ℕ}

/-- **CRT decomposition of the Zolotarev permutation sign.**

    Through the Chinese Remainder isomorphism `ZMod (m*n) ≃+* ZMod m × ZMod n`,
    the sign of multiplication-by-`a` on `ZMod (m*n)` decomposes as

      `sign(ringMulPerm a) = sign(ringMulPerm a₁) ^ n * sign(ringMulPerm a₂) ^ m`,

    where `a₁, a₂` are the CRT components of `a`.  This is the structural heart
    of the Frobenius/Jacobi generalization of Zolotarev's lemma. -/
theorem sign_ringMulPerm_crt [NeZero m] [NeZero n] (h : m.Coprime n)
    (a : (ZMod (m * n))ˣ) (a₁ : (ZMod m)ˣ) (a₂ : (ZMod n)ˣ)
    (h₁ : (a₁ : ZMod m) = ((ZMod.chineseRemainder h) (a : ZMod (m * n))).1)
    (h₂ : (a₂ : ZMod n) = ((ZMod.chineseRemainder h) (a : ZMod (m * n))).2) :
    Equiv.Perm.sign (ringMulPerm a)
      = Equiv.Perm.sign (ringMulPerm a₁) ^ n * Equiv.Perm.sign (ringMulPerm a₂) ^ m := by
  set e := ZMod.chineseRemainder h with he
  -- The CRT iso intertwines `ringMulPerm a` with the product permutation.
  have hsq : ∀ x : ZMod (m * n),
      e.toEquiv (ringMulPerm a x)
        = (Equiv.prodCongr (ringMulPerm a₁) (ringMulPerm a₂)) (e.toEquiv x) := by
    intro x
    simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ringMulPerm_apply,
      Equiv.prodCongr_apply, Prod.map_apply']
    rw [map_mul, h₁, h₂]
    rfl
  rw [sign_eq_sign_of_equiv (ringMulPerm a)
        (Equiv.prodCongr (ringMulPerm a₁) (ringMulPerm a₂)) e.toEquiv hsq,
      sign_prodCongr, ZMod.card n, ZMod.card m]

/-- **The Zolotarev sign character is multiplicative across an odd CRT
    factorization.**  When `m` and `n` are odd, the cardinality exponents `n`
    and `m` are odd, so each `sign ^ odd = sign`.  This is the exact
    permutation-theoretic shadow of `jacobiSym.mul_right`
    (`J(a | m*n) = J(a | m) * J(a | n)`). -/
theorem sign_ringMulPerm_mul_of_odd [NeZero m] [NeZero n] (h : m.Coprime n)
    (hm : Odd m) (hn : Odd n)
    (a : (ZMod (m * n))ˣ) (a₁ : (ZMod m)ˣ) (a₂ : (ZMod n)ˣ)
    (h₁ : (a₁ : ZMod m) = ((ZMod.chineseRemainder h) (a : ZMod (m * n))).1)
    (h₂ : (a₂ : ZMod n) = ((ZMod.chineseRemainder h) (a : ZMod (m * n))).2) :
    Equiv.Perm.sign (ringMulPerm a)
      = Equiv.Perm.sign (ringMulPerm a₁) * Equiv.Perm.sign (ringMulPerm a₂) := by
  rw [sign_ringMulPerm_crt h a a₁ a₂ h₁ h₂,
      units_pow_odd _ hn, units_pow_odd _ hm]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: PARALLEL WITH THE JACOBI SYMBOL
═══════════════════════════════════════════════════════════════════════════════ -/

open scoped NumberTheorySymbols in
/-- The Jacobi symbol is multiplicative in its (odd) denominator — the
    value-level statement that `sign_ringMulPerm_mul_of_odd` mirrors at the
    level of permutation signs.  (Restated from Mathlib's `jacobiSym.mul_right`.) -/
theorem jacobiSym_mul_right_mirror (a : ℤ) (b₁ b₂ : ℕ) [NeZero b₁] [NeZero b₂] :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
  jacobiSym.mul_right a b₁ b₂

open scoped NumberTheorySymbols in
/-- The prime base case (`legendreSym.to_jacobiSym`): for a prime `p` the
    Jacobi symbol IS the Legendre symbol, which the parent (`OQ-01`,
    `zolotarev_lemma`) identified with a permutation sign.  Composing this base
    case with the CRT multiplicativity above yields the full Frobenius/Jacobi
    statement. -/
theorem legendre_eq_jacobi (p : ℕ) [Fact p.Prime] (a : ℤ) :
    legendreSym p a = J(a | p) :=
  jacobiSym.legendreSym.to_jacobiSym p a

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The sign character of the trivial unit is trivial, for any modulus. -/
example {n : ℕ} [NeZero n] : signRingHom (1 : (ZMod n)ˣ) = 1 := map_one _

/-- `signRingHom` is a genuine group homomorphism (multiplicativity of the
    Zolotarev character for composite moduli). -/
example {n : ℕ} [NeZero n] (a b : (ZMod n)ˣ) :
    signRingHom (a * b) = signRingHom a * signRingHom b := map_mul _ _ _

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## CRT decomposition of Zolotarev's permutation (answering OQ-01's third
   open question)

### What's proved (0 sorries, 0 axioms):
- `ringMulPerm`: multiplication-by-a-unit on the WHOLE ring `ZMod n`
  (the Frobenius setting; |ZMod n| = n is odd for odd n).
- `signRingHom : (ZMod n)ˣ →* ℤˣ`: the Zolotarev sign character for ANY
  modulus — a generalization of the parent's prime-only `signMulHom`.
- `sign_prodCongr`: sign of a product permutation = `sign σ ^ |β| * sign τ ^ |α|`
  (a general lemma not present in Mathlib).
- `sign_ringMulPerm_crt`: the CRT decomposition of the multiplication-permutation
  sign through `ZMod.chineseRemainder`.
- `sign_ringMulPerm_mul_of_odd`: for ODD coprime moduli the sign character is
  multiplicative across the CRT factorization — the permutation-theoretic image
  of `jacobiSym.mul_right`.

### Honest scope:
This file formalizes the STRUCTURAL CRT mechanism: it proves that the Zolotarev
sign character decomposes (and, for odd moduli, multiplies) exactly as the
Jacobi symbol does in its denominator.  It does NOT close the loop to Jacobi
*values* — that needs the base case `sign(ringMulPerm a on ZMod p) = legendreSym p a`,
which combines the parent's `zolotarev_lemma` (units version) with a fixed-point
sign-restriction argument (multiplication fixes `0 ∈ ZMod p`).  That base case
is the remaining glue and is left as the next step.

### Key insight:
The multiplicativity of the Jacobi symbol in its denominator is NOT a separate
number-theoretic fact: it is the shadow of the Chinese Remainder Theorem acting
on permutations.  The only arithmetic input is that an odd number raised to an
odd power preserves a sign — `units_pow_odd`.
-/

#check @ringMulPerm
#check @ringMulPermHom
#check @signRingHom
#check @signRingHom_sq
#check @sign_prodCongr
#check @sign_ringMulPerm_crt
#check @sign_ringMulPerm_mul_of_odd
#check @units_pow_odd

end ZolotarevCRT
