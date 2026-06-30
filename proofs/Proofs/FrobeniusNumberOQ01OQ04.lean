/-
  OQ-01-OQ-04: The Apéry Set of ⟨a, b⟩ — Minimal Representatives and Reflection
  Symmetry
  (frobenius-number-oq-01-oq-04)

  For coprime a, b ≥ 2 the numerical semigroup S = ⟨a, b⟩ = {a·x + b·y : x, y ∈ ℕ}
  has, with respect to a, the **Apéry set**

      Ap(S, a) = {0, b, 2b, …, (a−1)b},

  the least element of S in each of the a residue classes mod a (the elements
  `w_k = k·b`, k < a, are pairwise incongruent mod a because gcd(a, b) = 1).
  The Apéry set is the central computational device of numerical-semigroup theory
  (Apéry 1946; Selmer 1977); the gallery so far works directly with the
  `Representable` predicate and never names it.  This file builds the Apéry set for
  the two-generator case and proves:

  • **Apéry characterization** (`apery_le_iff_representable`,
    `representable_iff_aperyIndex`): inside a fixed residue class mod a, a number is
    representable iff it is ≥ the Apéry element of that class.  Thus `w_k = k·b` is
    exactly the smallest element of S in its class, and membership in S is decided by
    a single comparison against the Apéry element of the class.

  • **Reflection symmetry** (`apery_symm`, `apery_max`): the involution k ↦ a−1−k
    sends the Apéry set to itself with `w_k + w_{a−1−k} = (a−1)·b = g + a`, where
    `g = ab − a − b` is the Frobenius number; the largest Apéry element is `g + a`.
    This reflection is the Apéry-set source of the Frobenius involution n ↦ g − n.

  • **Frobenius number is a gap, via Apéry minimality**
    (`frobeniusNumber_mod`, `frobeniusNumber_not_representable`): `g` lies strictly
    below the maximal Apéry element `(a−1)·b` of its own residue class, so by
    minimality `g ∉ S` — an Apéry-set re-derivation of Sylvester's non-representability
    of the Frobenius number.

  The Apéry set established here is the standard entry point to Selmer's genus formula
  `g(S) = (Σ_{w∈Ap} w)/a − (a−1)/2` (the per-class gap count `⌊w_k/a⌋`), a natural
  follow-up.

  Status: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.FrobeniusNumber

namespace FrobeniusAperySet

open FrobeniusNumber Finset

variable {a b : ℕ}

/-! ## The Apéry index of a residue class

For coprime `a, b` the `a` numbers `0·b, 1·b, …, (a−1)·b` are pairwise incongruent
mod `a`, so every residue class mod `a` contains exactly one of them.  We package
existence: every `n` is congruent mod `a` to a unique `k·b` with `k < a`. -/

/-- The map `k ↦ k·b mod a` is injective on `Fin a` (coprimality cancels `b`). -/
private theorem aperyIndex_inj (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (fun k : Fin a => (⟨k.val * b % a, Nat.mod_lt _ ha⟩ : Fin a)) := by
  intro i j h
  simp only [Fin.mk.injEq] at h
  have hmod : i.val * b ≡ j.val * b [MOD a] := h
  have hij : i.val ≡ j.val [MOD a] := Nat.ModEq.cancel_right_of_coprime hab hmod
  have heq : i.val % a = j.val % a := hij
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at heq
  exact Fin.ext heq

/-- **Apéry index.** Every `n` is congruent mod `a` to a unique `k·b` with `k < a`. -/
theorem exists_aperyIndex (ha : 0 < a) (hab : Nat.Coprime a b) (n : ℕ) :
    ∃ k < a, n ≡ k * b [MOD a] := by
  have hsurj := Finite.injective_iff_surjective.mp (aperyIndex_inj ha hab)
  obtain ⟨⟨k, hk⟩, hkr⟩ := hsurj ⟨n % a, Nat.mod_lt _ ha⟩
  simp only [Fin.mk.injEq] at hkr
  -- hkr : k * b % a = n % a
  exact ⟨k, hk, hkr.symm⟩

/-! ## Apéry characterization: `w_k = k·b` is the least element of its class -/

/-- If `n` lies in the residue class of `k·b` (k < a) and `k·b ≤ n`, then `n` is
    representable: write `n = a·q + b·k`. -/
theorem representable_of_aperyIndex {n k : ℕ}
    (hmod : n ≡ k * b [MOD a]) (hle : k * b ≤ n) : Representable a b n := by
  have hdvd : a ∣ n - k * b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  obtain ⟨q, hq⟩ := hdvd
  have hbk : k * b = b * k := Nat.mul_comm k b
  exact ⟨q, k, by omega⟩

/-- **Apéry minimality.** If `n` is representable and lies in the residue class of
    `k·b` with `k < a`, then `k·b ≤ n`: the Apéry element `w_k = k·b` is the least
    element of `⟨a,b⟩` in its class. -/
theorem aperyIndex_le_of_representable (hab : Nat.Coprime a b)
    {n k : ℕ} (hk : k < a) (hrep : Representable a b n) (hmod : n ≡ k * b [MOD a]) :
    k * b ≤ n := by
  obtain ⟨x, y, hxy⟩ := hrep
  -- n ≡ b·y (mod a) since a·x ≡ 0
  have h1 : n ≡ b * y [MOD a] := by
    have hn : n = b * y + a * x := by rw [hxy]; ring
    rw [hn]
    have key := (Nat.modEq_zero_iff_dvd.mpr (⟨x, rfl⟩ : a ∣ a * x)).add_left (b * y)
    rwa [Nat.add_zero] at key
  -- b·y ≡ b·k (mod a)
  have h2 : b * y ≡ b * k [MOD a] := by
    have h := h1.symm.trans hmod
    rwa [Nat.mul_comm k b] at h
  -- cancel b: y ≡ k (mod a)
  have h3 : y ≡ k [MOD a] := Nat.ModEq.cancel_left_of_coprime hab h2
  have h4 : k ≤ y := by
    have h : y % a = k % a := h3
    rw [Nat.mod_eq_of_lt hk] at h
    rw [← h]; exact Nat.mod_le y a
  calc k * b ≤ y * b := Nat.mul_le_mul_right b h4
    _ = b * y := Nat.mul_comm y b
    _ ≤ a * x + b * y := Nat.le_add_left _ _
    _ = n := hxy.symm

/-- **Apéry characterization.** Inside the residue class of `k·b` (k < a), a number
    is representable iff it is at least the Apéry element `w_k = k·b`. -/
theorem apery_le_iff_representable (hab : Nat.Coprime a b)
    {n k : ℕ} (hk : k < a) (hmod : n ≡ k * b [MOD a]) :
    k * b ≤ n ↔ Representable a b n :=
  ⟨representable_of_aperyIndex hmod, fun hrep => aperyIndex_le_of_representable hab hk hrep hmod⟩

/-! ## Reflection symmetry of the Apéry set -/

/-- **Apéry reflection.** For `k ≤ a − 1`, the Apéry elements `w_k = k·b` and
    `w_{a−1−k} = (a−1−k)·b` are mirror images: their sum is the maximal Apéry
    element `(a−1)·b`. -/
theorem apery_symm {k : ℕ} (hk : k ≤ a - 1) :
    k * b + (a - 1 - k) * b = (a - 1) * b := by
  have : k + (a - 1 - k) = a - 1 := by omega
  calc k * b + (a - 1 - k) * b = (k + (a - 1 - k)) * b := by ring
    _ = (a - 1) * b := by rw [this]

/-- **Largest Apéry element.** `max Ap(S,a) = (a−1)·b = g + a`, where `g` is the
    Frobenius number `ab − a − b`. -/
theorem apery_max (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (a - 1) * b = frobeniusNumber a b + a := by
  have hge : a + b ≤ a * b := by nlinarith
  have h1 : (a - 1) * b + b = a * b := by
    have h2 : (a - 1 + 1) * b = a * b := by congr 1; omega
    have h3 : (a - 1 + 1) * b = (a - 1) * b + b := by ring
    omega
  simp only [frobeniusNumber]; omega

/-! ## Apéry-set characterization of representability and the Frobenius number

Combining the index existence with the per-class characterization gives a global
description of `S = ⟨a,b⟩` purely in terms of the Apéry set, from which the classical
non-representability of the Frobenius number follows by Apéry minimality. -/

/-- **Global Apéry characterization.** `n ∈ ⟨a,b⟩` iff `n` dominates the Apéry
    element of its residue class: there is `k < a` with `n ≡ k·b (mod a)` and
    `k·b ≤ n`. -/
theorem representable_iff_aperyIndex (ha : 0 < a) (hab : Nat.Coprime a b) (n : ℕ) :
    Representable a b n ↔ ∃ k < a, n ≡ k * b [MOD a] ∧ k * b ≤ n := by
  constructor
  · intro hrep
    obtain ⟨k, hk, hmod⟩ := exists_aperyIndex ha hab n
    exact ⟨k, hk, hmod, aperyIndex_le_of_representable hab hk hrep hmod⟩
  · rintro ⟨k, _, hmod, hle⟩
    exact representable_of_aperyIndex hmod hle

/-- The Frobenius number lies in the residue class of the maximal Apéry element
    `(a−1)·b`. -/
theorem frobeniusNumber_mod (ha : 2 ≤ a) (hb : 2 ≤ b) :
    frobeniusNumber a b ≡ (a - 1) * b [MOD a] := by
  have hmax : (a - 1) * b = frobeniusNumber a b + a := apery_max ha hb
  -- (a-1)*b - g = a, so a ∣ (a-1)*b - g, giving g ≡ (a-1)*b
  have hdvd : a ∣ (a - 1) * b - frobeniusNumber a b := ⟨1, by omega⟩
  exact ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd)

/-- **Frobenius number is a gap, via Apéry minimality.** Because `g = (a−1)b − a`
    lies strictly below the Apéry element `(a−1)·b` of its own residue class, and
    `(a−1)·b` is the *least* element of `⟨a,b⟩` in that class, `g` is not
    representable.  This re-derives Sylvester's non-representability of the Frobenius
    number directly from the Apéry-set structure. -/
theorem frobeniusNumber_not_representable (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : Nat.Coprime a b) : ¬ Representable a b (frobeniusNumber a b) := by
  intro hrep
  have hk : a - 1 < a := by omega
  have hmod : frobeniusNumber a b ≡ (a - 1) * b [MOD a] := frobeniusNumber_mod ha hb
  have hle : (a - 1) * b ≤ frobeniusNumber a b :=
    aperyIndex_le_of_representable hab hk hrep hmod
  have hmax : (a - 1) * b = frobeniusNumber a b + a := apery_max ha hb
  omega

end FrobeniusAperySet
