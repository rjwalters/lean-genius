import Mathlib
import Proofs.AutomorphicNumberOQ01

/-!
# The complementary pairing of automorphic idempotents

## What This Proves

The parent file `AutomorphicNumberOQ01` shows that for every `k ≥ 1` the ring
`ZMod (10 ^ k)` has **exactly four idempotents** `e * e = e` — equivalently four
`k`-digit automorphic residues `n ^ 2 ≡ n (mod 10 ^ k)`, namely `0`, `1`, and the
familiar `…5` / `…6` numbers (`5, 6`; `25, 76`; `376, 625`; …).

This file describes the **structure** of those four residues, not just their count.

* **Orthogonal complement algebra.** In any commutative ring, if `e` is idempotent then
  so is `1 - e`, and the two are *orthogonal complements*:
  `e + (1 - e) = 1` and `e * (1 - e) = 0`.
* **Complementary pair (main theorem).** `automorphic_complementary_pair`: the four
  idempotents of `ZMod (10 ^ k)` are exactly `{0, 1, a, 1 - a}` for a nontrivial
  idempotent `a` (one of the `…5`/`…6` automorphic numbers).  The two nontrivial ones,
  `a` and `1 - a`, satisfy `a + (1 - a) = 1` and `a * (1 - a) = 0`; concretely
  `5 + 6 = 1`, `5 * 6 = 0` in `ZMod 10`, etc.  So `0 ↔ 1` and `…5 ↔ …6` are the two
  complementary pairs.
* **Last digit determines the residue (main theorem).** `same_last_digit`: two
  automorphic residues modulo `10 ^ k` that share the same last digit
  (`(10 : ZMod (10 ^ k)) ∣ e - f`) are equal.  Hence each of the four residues has a
  *distinct* last digit, and an automorphic number is pinned down by its final digit.

The engine for the last-digit theorem is the elementary identity
`(e - f) ^ 3 = e - f` for idempotents `e, f` (a difference of idempotents is "tripotent"),
combined with the fact that a difference lying in the nil ideal `(10)` of `ZMod (10 ^ k)`
is nilpotent; a tripotent nilpotent element is `0`.  This is exactly the uniqueness of
idempotent lifts modulo a nil ideal, proved here from scratch.

## Status

Fully machine-checked: `0` sorries, `0` axioms.  Builds on the verified parent file.
-/

namespace AutomorphicNumberOQ01OQ02

open Finset

/-! ## Orthogonal-complement algebra (any commutative ring) -/

variable {R : Type*} [CommRing R]

/-- If `e` is idempotent then so is its complement `1 - e`. -/
theorem compl_idem {e : R} (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination he

/-- An idempotent and its complement are **orthogonal**: their product is `0`. -/
theorem mul_compl {e : R} (he : e * e = e) : e * (1 - e) = 0 := by
  linear_combination -he

/-- An idempotent and its complement **add to one**. -/
theorem add_compl (e : R) : e + (1 - e) = 1 := by ring

/-- A difference of idempotents is **tripotent**: `(e - f) ^ 3 = e - f`.  This is the
algebraic engine behind uniqueness of idempotent lifts. -/
theorem idem_diff_cube {e f : R} (he : e * e = e) (hf : f * f = f) :
    (e - f) ^ 3 = e - f := by
  linear_combination (e + 1 - 3 * f) * he + (3 * e - f - 1) * hf

/-- An element that is both **idempotent and nilpotent** is `0`. -/
theorem idem_nil_zero {g : R} (hg : g * g = g) (h : IsNilpotent g) : g = 0 := by
  obtain ⟨m, hm⟩ := h
  have hpow : ∀ j : ℕ, g ^ (j + 1) = g := by
    intro j
    induction j with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hg]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have h1 : (1 : R) = 0 := by simpa using hm
    haveI := subsingleton_of_zero_eq_one h1.symm
    exact Subsingleton.elim _ _
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hpow j] at hm
    exact hm

/-- **Uniqueness of idempotent lifts modulo a nil ideal.**  If `e, f` are idempotents
whose difference is nilpotent, then `e = f`. -/
theorem idem_eq_of_sub_nilpotent {e f : R} (he : e * e = e) (hf : f * f = f)
    (h : IsNilpotent (e - f)) : e = f := by
  have hcube : (e - f) ^ 3 = e - f := idem_diff_cube he hf
  -- `(e - f) ^ 2` is idempotent: `(e-f)^4 = (e-f)·(e-f)^3 = (e-f)·(e-f) = (e-f)^2`.
  have hsqidem : (e - f) ^ 2 * (e - f) ^ 2 = (e - f) ^ 2 := by
    calc (e - f) ^ 2 * (e - f) ^ 2 = (e - f) * (e - f) ^ 3 := by ring
      _ = (e - f) * (e - f) := by rw [hcube]
      _ = (e - f) ^ 2 := by ring
  -- and nilpotent, being a power of the nilpotent `e - f`.
  have hnil2 : IsNilpotent ((e - f) ^ 2) := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by rw [← pow_mul, mul_comm, pow_mul, hn]; simp⟩
  have hd2 : (e - f) ^ 2 = 0 := idem_nil_zero hsqidem hnil2
  have hd0 : e - f = 0 := by
    rw [← hcube]
    calc (e - f) ^ 3 = (e - f) * (e - f) ^ 2 := by ring
      _ = (e - f) * 0 := by rw [hd2]
      _ = 0 := by rw [mul_zero]
  exact sub_eq_zero.mp hd0

/-! ## The four automorphic residues of `ZMod (10 ^ k)` -/

/-- In `ZMod (10 ^ k)` the element `10` is nilpotent: `10 ^ k = 0`. -/
theorem ten_pow_eq_zero (k : ℕ) : (10 : ZMod (10 ^ k)) ^ k = 0 := by
  have h : ((10 ^ k : ℕ) : ZMod (10 ^ k)) = 0 := ZMod.natCast_self _
  calc (10 : ZMod (10 ^ k)) ^ k = ((10 ^ k : ℕ) : ZMod (10 ^ k)) := by push_cast; ring
    _ = 0 := h

/-- **Last digit determines the residue.**  Two automorphic residues modulo `10 ^ k`
whose difference is divisible by `10` (i.e. they share their last digit) are equal.
Consequently the four idempotents of `ZMod (10 ^ k)` have four *distinct* last digits. -/
theorem same_last_digit {k : ℕ} {e f : ZMod (10 ^ k)}
    (he : e * e = e) (hf : f * f = f) (hdvd : (10 : ZMod (10 ^ k)) ∣ (e - f)) :
    e = f := by
  obtain ⟨c, hc⟩ := hdvd
  have hnil : IsNilpotent (e - f) :=
    ⟨k, by rw [hc, mul_pow, ten_pow_eq_zero, zero_mul]⟩
  exact idem_eq_of_sub_nilpotent he hf hnil

/-- **Main theorem — the complementary pairing.**  For every `k ≥ 1` the four
idempotents of `ZMod (10 ^ k)` are exactly `{0, 1, a, 1 - a}` where `a` is a nontrivial
idempotent (one of the `…5` / `…6` automorphic numbers).  The two nontrivial residues
`a` and `1 - a` are orthogonal complements: `a + (1 - a) = 1` and `a * (1 - a) = 0`. -/
theorem automorphic_complementary_pair (k : ℕ) (hk : 0 < k) :
    ∃ a b : ZMod (10 ^ k),
      a * a = a ∧ b * b = b ∧ a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧
      a + b = 1 ∧ a * b = 0 ∧ a ≠ b ∧
      (univ.filter (fun e : ZMod (10 ^ k) => e * e = e)) = {0, 1, a, b} := by
  haveI : Fact (1 < 10 ^ k) := ⟨Nat.one_lt_pow hk.ne' (by norm_num)⟩
  set S := univ.filter (fun e : ZMod (10 ^ k) => e * e = e) with hSdef
  have hScard : S.card = 4 := AutomorphicNumberOQ01.automorphic_idempotent_count k hk
  -- `{0, 1} ⊆ S` and there are 4 idempotents, so an idempotent `a ∉ {0, 1}` exists.
  have hmemS : ∀ x : ZMod (10 ^ k), x ∈ S ↔ x * x = x := by
    intro x; rw [hSdef]; simp
  have hsub01 : ({0, 1} : Finset (ZMod (10 ^ k))) ⊆ S := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [hmemS]
    rcases hx with rfl | rfl <;> simp
  have hcard01 : ({0, 1} : Finset (ZMod (10 ^ k))).card = 2 := by
    rw [card_insert_of_notMem (by simp), card_singleton]
  -- Since `S` has 4 elements but `{0, 1}` only 2, some idempotent lies outside `{0, 1}`.
  have hex : ∃ a ∈ S, a ∉ ({0, 1} : Finset (ZMod (10 ^ k))) := by
    by_contra h
    push_neg at h
    have hsubset : S ⊆ ({0, 1} : Finset (ZMod (10 ^ k))) := fun x hx => h x hx
    have hle := card_le_card hsubset
    rw [hScard, hcard01] at hle
    omega
  obtain ⟨a, ha_S, ha_not⟩ := hex
  have ha : a * a = a := (hmemS a).mp ha_S
  have ha0 : a ≠ 0 := by intro h; apply ha_not; simp [h]
  have ha1 : a ≠ 1 := by intro h; apply ha_not; simp [h]
  -- The complement `b = 1 - a` is the other nontrivial idempotent.
  have hb : (1 - a) * (1 - a) = 1 - a := compl_idem ha
  have hb0 : (1 - a) ≠ 0 := by intro h; exact ha1 (by linear_combination -h)
  have hb1 : (1 - a) ≠ 1 := by intro h; exact ha0 (by linear_combination -h)
  have hab : a ≠ 1 - a := by
    intro heq
    have h2a : (1 : ZMod (10 ^ k)) = 2 * a := by linear_combination -heq
    have : a = 1 := by
      calc a = a * 1 := (mul_one a).symm
        _ = a * (2 * a) := by rw [h2a]
        _ = 2 * (a * a) := by ring
        _ = 2 * a := by rw [ha]
        _ = 1 := h2a.symm
    exact ha1 this
  refine ⟨a, 1 - a, ha, hb, ha0, ha1, hb0, hb1, add_compl a, mul_compl ha, hab, ?_⟩
  -- The four distinct idempotents `0, 1, a, 1 - a` exhaust the 4-element set `S`.
  have hsub : ({0, 1, a, 1 - a} : Finset (ZMod (10 ^ k))) ⊆ S := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [hmemS]
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact ha
    · exact hb
  have hcard4 : ({0, 1, a, 1 - a} : Finset (ZMod (10 ^ k))).card = 4 := by
    have m1 : a ∉ ({1 - a} : Finset (ZMod (10 ^ k))) := by simpa using hab
    have m2 : (1 : ZMod (10 ^ k)) ∉ ({a, 1 - a} : Finset (ZMod (10 ^ k))) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm⟩
    have m3 : (0 : ZMod (10 ^ k)) ∉ ({1, a, 1 - a} : Finset (ZMod (10 ^ k))) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨zero_ne_one, fun h => ha0 h.symm, fun h => hb0 h.symm⟩
    rw [show ({0, 1, a, 1 - a} : Finset (ZMod (10 ^ k)))
          = insert 0 (insert 1 (insert a {1 - a})) from rfl,
        card_insert_of_notMem m3, card_insert_of_notMem m2,
        card_insert_of_notMem m1, card_singleton]
  exact (eq_of_subset_of_card_le hsub (by rw [hScard, hcard4])).symm

/-! ## Concrete complementary pairs

The two nontrivial idempotents of `ZMod (10 ^ k)` are the classic automorphic numbers
ending in `…5` and `…6`.  Here are the smallest pairs, verified by `decide`: each pair
sums to `1` and multiplies to `0`, exactly as `automorphic_complementary_pair` predicts. -/

/-- `5` and `6` are complementary idempotents mod `10`. -/
example : (5 : ZMod 10) + 6 = 1 ∧ (5 : ZMod 10) * 6 = 0 := by decide

/-- `25` and `76` are complementary idempotents mod `100`. -/
example : (25 : ZMod 100) + 76 = 1 ∧ (25 : ZMod 100) * 76 = 0 := by decide

/-- `376` and `625` are complementary idempotents mod `1000`. -/
example : (376 : ZMod 1000) + 625 = 1 ∧ (376 : ZMod 1000) * 625 = 0 := by decide

end AutomorphicNumberOQ01OQ02
