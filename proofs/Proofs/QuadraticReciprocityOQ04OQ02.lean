import Mathlib

/-!
# Euler liars form a subgroup, and the Solovay–Strassen ½-bound (quadratic-reciprocity-oq-04-oq-01)

## What this proves

The parent entry `quadratic-reciprocity-oq-04` exhibited a single failure of the Jacobi
symbol to detect quadratic residues: `J(2 | 15) = 1` yet `2` is not a square mod `15`.
This file upgrades that single counterexample into the structural theorem that powers the
**Solovay–Strassen primality test**.

Fix an odd modulus `n > 1`. Call a unit `a ∈ (ℤ/nℤ)ˣ` an **Euler liar** when it satisfies
the Euler congruence
`a^((n-1)/2) ≡ J(a | n)  (mod n)`,
the identity that holds for *every* unit when `n` is prime (Euler's criterion). The set of
Euler liars is denoted `E(n)`.

* **Structural core (any odd `n > 1`).** `E(n)` is a *subgroup* of `(ℤ/nℤ)ˣ`. The proof is
  the observation that the Euler congruence equates two homomorphisms: `a ↦ a^((n-1)/2)`
  and `a ↦ J(a | n)` (multiplicativity of the Jacobi symbol in the numerator). Consequently,
  the moment `E(n)` is a *proper* subgroup — i.e. one Euler *witness* exists — Lagrange's
  theorem forces `|E(n)| ≤ φ(n)/2`. This is the "one reduction beats a thousand cases" heart
  of the test: half of all residues expose compositeness, so `k` independent trials fail with
  probability `≤ 2^{-k}`.

* **Unconditional witness (odd `n = p·m`, `p` an odd prime, `gcd(p,m)=1`, `m > 1`).** Every
  such `n` — in particular every squarefree odd composite — admits an Euler witness, so the
  `½`-bound holds unconditionally there. The witness is built by CRT: pick a non-residue `b`
  mod `p` and lift `(b, 1)` to `(ℤ/nℤ)ˣ`. Its Jacobi symbol is `(-1)·1 = -1`, but its
  `((n-1)/2)`-th power is `≡ 1 (mod m)`, and `1 ≠ -1` in `ℤ/mℤ` (as `m ≥ 3`), so the Euler
  congruence fails mod `m`.

## Status

- [x] Complete proof, no sorries
- [x] 0 `axiom` declarations, no structure-encoded assumptions, no `native_decide`
- [x] Structural: `E(n)` is a `Subgroup`; proper ⟹ `|E(n)| ≤ φ(n)/2`
- [x] Number-theoretic witness for `n = p·m` (covers all squarefree odd composites)
-/

namespace QuadraticReciprocityOQ04OQ02

open scoped BigOperators

/-- `1 < n` supplies `NeZero n`, so all the `ZMod n` machinery is available from `Fact (1 < n)`
alone. -/
instance factNeZero (n : ℕ) [Fact (1 < n)] : NeZero n :=
  ⟨by have := (Fact.out : 1 < n); omega⟩

/-! ## The Jacobi symbol of a unit, and its multiplicativity -/

/-- `jUnit u` is the Jacobi symbol `J(a | n)` where `a` is the canonical representative of the
unit `u ∈ (ℤ/nℤ)ˣ`. Because `u` is a unit, `gcd(a, n) = 1`, so the value is `±1`. -/
def jUnit {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) : ℤ :=
  jacobiSym ((u : ZMod n).val : ℤ) n

/-- The Jacobi symbol of a unit is `1` or `-1`. -/
theorem jUnit_eq_one_or {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    jUnit u = 1 ∨ jUnit u = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  have h : Nat.gcd (u : ZMod n).val n = 1 := ZMod.val_coe_unit_coprime u
  unfold Int.gcd
  simp only [Int.natAbs_natCast]
  exact h

/-- `jUnit` sends `1` to `1`. -/
theorem jUnit_one {n : ℕ} [Fact (1 < n)] :
    jUnit (1 : (ZMod n)ˣ) = 1 := by
  unfold jUnit
  simp [ZMod.val_one n, jacobiSym.one_left]

/-- **Multiplicativity.** `jUnit` is a homomorphism to `{±1}`: `J(uv) = J(u)·J(v)`. This is
the multiplicativity of the Jacobi symbol in the numerator, transported through the fact that
the Jacobi symbol only depends on the numerator mod `n`. -/
theorem jUnit_mul {n : ℕ} [NeZero n] (u v : (ZMod n)ˣ) :
    jUnit (u * v) = jUnit u * jUnit v := by
  unfold jUnit
  rw [← jacobiSym.mul_left]
  refine jacobiSym.mod_left' ?_
  have hval : (↑(u * v) : ZMod n) = (↑u : ZMod n) * (↑v : ZMod n) := by
    push_cast; ring
  rw [hval, ZMod.val_mul]
  push_cast [Int.natCast_mod]
  rw [Int.emod_emod_of_dvd _ dvd_rfl]

/-! ## Euler liars form a subgroup -/

/-- The set of **Euler liars** mod `n`: units satisfying the Euler congruence
`a^((n-1)/2) ≡ J(a | n) (mod n)`, packaged as a subgroup of `(ℤ/nℤ)ˣ`.

Membership equates the two homomorphisms `a ↦ a^((n-1)/2)` and `a ↦ J(a | n)`, so it is
closed under multiplication and inversion. -/
def eulerLiars (n : ℕ) [Fact (1 < n)] : Subgroup (ZMod n)ˣ where
  carrier := {u | ((u : ZMod n)) ^ ((n - 1) / 2) = ((jUnit u : ℤ) : ZMod n)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, one_pow, jUnit_one, Int.cast_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Units.val_mul, mul_pow, ha, hb, jUnit_mul]
    push_cast
    ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    -- `J a⁻¹ = J a` because both are `±1` and their product is `J 1 = 1`.
    have hja : jUnit a⁻¹ = jUnit a := by
      have hmul : jUnit (a * a⁻¹) = jUnit a * jUnit a⁻¹ := jUnit_mul a a⁻¹
      rw [mul_inv_cancel, jUnit_one] at hmul
      rcases jUnit_eq_one_or a with h | h <;> rcases jUnit_eq_one_or a⁻¹ with h' | h' <;>
        rw [h, h'] at hmul ⊢ <;> omega
    -- `a^k` squares to `1` (its value is `±1`), so `(a^k)⁻¹ = a^k`; hence `(↑a⁻¹)^k = ↑(a^k)`.
    have hsq : (a ^ ((n - 1) / 2)) * (a ^ ((n - 1) / 2)) = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      simp only [Units.val_pow_eq_pow_val, ha]
      rcases jUnit_eq_one_or a with h | h <;> rw [h] <;> push_cast <;> ring
    have hinv : (a ^ ((n - 1) / 2))⁻¹ = a ^ ((n - 1) / 2) := inv_eq_of_mul_eq_one_right hsq
    calc ((a⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)
        = ((a⁻¹ ^ ((n - 1) / 2) : (ZMod n)ˣ) : ZMod n) := by
          rw [Units.val_pow_eq_pow_val]
      _ = (((a ^ ((n - 1) / 2))⁻¹ : (ZMod n)ˣ) : ZMod n) := by rw [inv_pow]
      _ = ((a ^ ((n - 1) / 2) : (ZMod n)ˣ) : ZMod n) := by rw [hinv]
      _ = ((a : ZMod n)) ^ ((n - 1) / 2) := by rw [Units.val_pow_eq_pow_val]
      _ = ((jUnit a : ℤ) : ZMod n) := ha
      _ = ((jUnit a⁻¹ : ℤ) : ZMod n) := by rw [hja]

/-- Membership in `eulerLiars` unfolds to the Euler congruence. -/
theorem mem_eulerLiars {n : ℕ} [Fact (1 < n)] {u : (ZMod n)ˣ} :
    u ∈ eulerLiars n ↔ ((u : ZMod n)) ^ ((n - 1) / 2) = ((jUnit u : ℤ) : ZMod n) :=
  Iff.rfl

/-! ## The density bound: a proper subgroup has index ≥ 2 -/

/-- **Structural Solovay–Strassen bound.** If `E(n)` is a proper subgroup — equivalently, at
least one Euler *witness* exists — then the Euler liars number at most half the units:
`|E(n)| ≤ φ(n)/2`. Pure group theory: a proper subgroup of a finite group has index `≥ 2`. -/
theorem eulerLiars_card_le {n : ℕ} [Fact (1 < n)] (h : eulerLiars n ≠ ⊤) :
    Nat.card (eulerLiars n) ≤ Nat.card (ZMod n)ˣ / 2 := by
  have hidx : 1 < (eulerLiars n).index := Subgroup.one_lt_index_of_ne_top h
  have hmul : (eulerLiars n).index * Nat.card (eulerLiars n) = Nat.card (ZMod n)ˣ :=
    (eulerLiars n).index_mul_card
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc Nat.card (eulerLiars n) * 2
      ≤ Nat.card (eulerLiars n) * (eulerLiars n).index := by
        apply Nat.mul_le_mul_left; omega
    _ = (eulerLiars n).index * Nat.card (eulerLiars n) := by ring
    _ = Nat.card (ZMod n)ˣ := hmul

/-! ## An unconditional Euler witness for `n = p · m`

For `n = p · m` with `p` an odd prime coprime to an odd `m > 1`, we exhibit a concrete Euler
witness, so `eulerLiars n` is proper and the `½`-bound above applies unconditionally. This
covers every squarefree odd composite modulus (and more). -/

section Witness

variable {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime p m)
  (hm1 : 1 < m) (hmodd : Odd m)

include hp hp2 hcop hm1 hmodd in
/-- **Euler witnesses exist for `n = p·m`.** The Euler-liar subgroup is proper: there is a unit
whose Euler congruence fails. Concretely, lift `(non-residue mod p, 1 mod m)` through the CRT
isomorphism; its Jacobi symbol is `-1` but its power is `≡ 1 (mod m)`. -/
theorem eulerLiars_ne_top [Fact (1 < p * m)] :
    eulerLiars (p * m) ≠ ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero m := ⟨by omega⟩
  -- a non-residue `b` mod `p`
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare
    (by simpa [ZMod.ringChar_zmod_n] using hp2 : ringChar (ZMod p) ≠ 2)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb ⟨0, by ring⟩
  -- the CRT preimage of `(b, 1)`, and its residues mod `p` and mod `m`
  set a₀ : ZMod (p * m) := (ZMod.chineseRemainder hcop).symm (b, 1) with ha₀
  have hcrt : (ZMod.chineseRemainder hcop) a₀ = (b, 1) :=
    (ZMod.chineseRemainder hcop).apply_symm_apply _
  have hfst : (ZMod.castHom (dvd_mul_right p m) (ZMod p)) a₀ = b := by
    have hc := RingHom.congr_fun
      (Subsingleton.elim (ZMod.castHom (dvd_mul_right p m) (ZMod p))
        ((RingHom.fst (ZMod p) (ZMod m)).comp (ZMod.chineseRemainder hcop).toRingHom)) a₀
    rw [hc]; simp [hcrt]
  have hsnd : (ZMod.castHom (dvd_mul_left m p) (ZMod m)) a₀ = 1 := by
    have hc := RingHom.congr_fun
      (Subsingleton.elim (ZMod.castHom (dvd_mul_left m p) (ZMod m))
        ((RingHom.snd (ZMod p) (ZMod m)).comp (ZMod.chineseRemainder hcop).toRingHom)) a₀
    rw [hc]; simp [hcrt]
  -- `a₀` is a unit
  have hbunit : IsUnit ((b, 1) : ZMod p × ZMod m) :=
    Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr hb0, isUnit_one⟩
  have hunit : IsUnit a₀ := by
    have := hbunit.map (ZMod.chineseRemainder hcop).symm
    rwa [ha₀]
  set u : (ZMod (p * m))ˣ := hunit.unit with hu
  have hval : (u : ZMod (p * m)) = a₀ := hunit.unit_spec
  -- the representative and its residues
  set A : ℕ := (u : ZMod (p * m)).val with hA
  have hAp : ((A : ℤ) : ZMod p) = b := by
    rw [hA, Int.cast_natCast, ZMod.natCast_val, ← ZMod.castHom_apply (h := dvd_mul_right p m),
      hval]
    exact hfst
  have hAm : ((A : ℤ) : ZMod m) = 1 := by
    rw [hA, Int.cast_natCast, ZMod.natCast_val, ← ZMod.castHom_apply (h := dvd_mul_left m p),
      hval]
    exact hsnd
  -- `J(u | p·m) = -1`
  have hJ : jUnit u = -1 := by
    unfold jUnit
    rw [show ((u : ZMod (p * m)).val : ℤ) = (A : ℤ) from rfl,
      jacobiSym.mul_right (A : ℤ) p m]
    have hJp : jacobiSym (A : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym p (A : ℤ), legendreSym.eq_neg_one_iff]
      rw [hAp]; exact hb
    have hJm : jacobiSym (A : ℤ) m = 1 := by
      have hmod : (A : ℤ) % (m : ℤ) = (1 : ℤ) % (m : ℤ) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mp (by rw [Int.cast_one]; exact hAm)
      rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
    rw [hJp, hJm]; ring
  -- projecting the Euler congruence mod `m` forces `1 = -1`, impossible since `m ≥ 3`
  intro htop
  have hmem : u ∈ eulerLiars (p * m) := htop ▸ Subgroup.mem_top u
  rw [mem_eulerLiars, hJ, Int.cast_neg, Int.cast_one] at hmem
  -- apply the ring hom `ZMod (p*m) → ZMod m`
  have hproj := congrArg (ZMod.castHom (dvd_mul_left m p) (ZMod m)) hmem
  rw [map_pow, map_neg, map_one, hval, hsnd, one_pow] at hproj
  -- `hproj : (1 : ZMod m) = -1`
  have hne : (1 : ZMod m) ≠ -1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hm2 : m = 2 := by omega
    rw [hm2] at hmodd
    exact (by decide : ¬ Odd 2) hmodd
  exact hne hproj

include hp hp2 hcop hm1 hmodd in
/-- **Solovay–Strassen ½-bound for `n = p·m`.** For `p` an odd prime coprime to an odd `m > 1`,
at most half of the units of `ℤ/(p·m)ℤ` are Euler liars. Every squarefree odd composite `n`
factors this way, so its Euler witnesses number at least `φ(n)/2`. -/
theorem solovay_strassen_card_le [Fact (1 < p * m)] :
    Nat.card (eulerLiars (p * m)) ≤ Nat.card (ZMod (p * m))ˣ / 2 :=
  eulerLiars_card_le (eulerLiars_ne_top hp hp2 hcop hm1 hmodd)

end Witness

end QuadraticReciprocityOQ04OQ02
