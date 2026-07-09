import Mathlib

/-
# abel-ruffini-oq-04-oq-01-oq-03 (sharpness witness): non-cyclic groups of order `pq`

`AbelRuffiniOQ04OQ01OQ03.lean` proves the two halves of the classical order-`pq`
classification for primes `p < q`:

* **Positive half** `isCyclic_of_card_eq_prime_mul_prime_of_not_dvd` — if `p ∤ q − 1` then every
  group of order `p·q` is cyclic;
* **Necessity** `dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime` — if some order-`pq` group
  fails to be cyclic then `p ∣ q − 1`.

The necessity direction is proved as a pure contrapositive of the positive half, so it does **not**
exhibit any non-cyclic group.  This file supplies the missing **existence witness** that makes the
dichotomy genuinely *sharp*: whenever the arithmetic condition `p ∣ q − 1` is met, a finite
non-cyclic group of order `pq` actually exists.

We realize the witness cleanly for the family `p = 2` using Mathlib's `DihedralGroup`.  For an odd
prime `q` one has `2 ∣ q − 1` automatically, and

    DihedralGroup q     has order `2q`  (`DihedralGroup.nat_card`)
    DihedralGroup q     is not cyclic   (`dihedralGroup_not_isCyclic`)

so `DihedralGroup q` is a non-cyclic group of order `2q`.  Consequently the implication
"order `2q` ⟹ cyclic" is *false* for every odd prime `q`
(`not_forall_isCyclic_card_eq_two_mul`), i.e. the condition `p ∤ q − 1` in the positive half cannot
be dropped — it is exactly the boundary between the cyclic-forced and non-cyclic-possible regimes.

The non-cyclicity is elementary: `r 1` and `sr 0` fail to commute
(`r 1 * sr 0 = sr (-1)` but `sr 0 * r 1 = sr 1`, and `-1 ≠ 1` in `ZMod q` once `q > 2`), while every
cyclic group is commutative (`IsCyclic.commutative`).

Self-contained: imports only `Mathlib`; the parent classification is referenced by name only.
No axioms, no sorries.
-/

open DihedralGroup

namespace AbelRuffiniOQ04OQ01OQ03Sharpness

/-- **`DihedralGroup n` is not cyclic for `n > 2`.**  The rotation `r 1` and the reflection
`sr 0` do not commute: `r 1 * sr 0 = sr (0 - 1) = sr (-1)` while `sr 0 * r 1 = sr (0 + 1) = sr 1`,
and `-1 ≠ 1` in `ZMod n` precisely because `n ∤ 2` when `n > 2`.  A cyclic group is commutative
(`IsCyclic.commutative`), so `DihedralGroup n` cannot be cyclic. -/
theorem dihedralGroup_not_isCyclic {n : ℕ} (hn : 2 < n) :
    ¬ IsCyclic (DihedralGroup n) := by
  intro hcyc
  haveI := hcyc
  -- A cyclic group is commutative, so `r 1` and `sr 0` would commute.
  have hcomm : (r 1 : DihedralGroup n) * sr 0 = sr 0 * r 1 :=
    (IsCyclic.commutative (α := DihedralGroup n)).comm (r 1) (sr 0)
  rw [r_mul_sr, sr_mul_r, zero_sub, zero_add, sr.injEq] at hcomm
  -- Now `hcomm : (-1 : ZMod n) = 1`, forcing `(2 : ZMod n) = 0`, i.e. `n ∣ 2`.
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by
    have h : (2 : ZMod n) = 0 := by linear_combination -hcomm
    exact_mod_cast h
  have hdvd : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h2
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)

/-- An odd prime is at least `3`. -/
private theorem two_lt_of_odd_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q) : 2 < q := by
  rcases eq_or_lt_of_le hq.two_le with heq | hlt
  · rw [← heq] at hodd; exact absurd hodd (by decide)
  · exact hlt

/-- **Sharpness witness (family `p = 2`).**  For every odd prime `q`, there is a *finite,
non-cyclic* group of order `2q` — namely `DihedralGroup q`.  Since `2 ∣ q − 1` for every odd `q`,
this shows the necessity condition `p ∣ q − 1` of
`dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime` is realizable, so the order-`pq`
classification is genuinely two-sided rather than only sufficient. -/
theorem exists_finite_not_isCyclic_card_eq_two_mul {q : ℕ} (hq : q.Prime) (hodd : Odd q) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = 2 * q ∧ ¬ IsCyclic G := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  exact ⟨DihedralGroup q, inferInstance, inferInstance,
    DihedralGroup.nat_card, dihedralGroup_not_isCyclic (two_lt_of_odd_prime hq hodd)⟩

/-- **The order-`2q` classification is sharp.**  For every odd prime `q` (so that `2 ∣ q − 1`),
it is *false* that every finite group of order `2q` is cyclic — the dihedral witness above refutes
it.  This is the precise sense in which the hypothesis `p ∤ q − 1` cannot be removed from the
positive half of the classification. -/
theorem not_forall_isCyclic_card_eq_two_mul {q : ℕ} (hq : q.Prime) (hodd : Odd q) :
    ¬ ∀ (G : Type) [Group G] [Finite G], Nat.card G = 2 * q → IsCyclic G := by
  intro H
  obtain ⟨G, hG, hFin, hcard, hnc⟩ := exists_finite_not_isCyclic_card_eq_two_mul hq hodd
  exact hnc (@H G hG hFin hcard)

/-- **Smallest instance.**  A non-cyclic group of order `6` exists (`DihedralGroup 3 ≅ S₃`); this is
the least order `pq` (`p = 2, q = 3`) admitting a non-cyclic group. -/
theorem exists_finite_not_isCyclic_card_six :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nat.card G = 6 ∧ ¬ IsCyclic G := by
  obtain ⟨G, hG, hFin, hcard, hnc⟩ :=
    exists_finite_not_isCyclic_card_eq_two_mul (q := 3) (by norm_num) (by decide)
  exact ⟨G, hG, hFin, hcard.trans (by norm_num), hnc⟩

end AbelRuffiniOQ04OQ01OQ03Sharpness
