/-
# An Inductive CRT Certificate for an Arbitrary List of Pairwise-Coprime Moduli

## Open question (`chinese-remainder-constructive-oq-05-oq-02`)

The sibling `chinese-remainder-constructive-oq-05-oq-01` proves CRT *uniqueness*
certificates for two moduli (`crt_pair_iff`) and three moduli (`crt_triple_iff`). Its open
question asks to generalise these to an **arbitrary list of pairwise-coprime moduli** — an
inductive CRT certificate — connecting to the list thread of `oq-04`.

## Result

* `prod_dvd_of_forall_dvd` — the combination engine: for any list `ms` of **pairwise**
  coprime naturals, if every `m ∈ ms` divides `d` then `ms.prod` divides `d`. (One list
  induction; the head is coprime to the tail product by `coprime_list_prod_right_iff`, and
  `Nat.Coprime.mul_dvd_of_dvd_of_dvd` folds it in.)

* `crt_list_unique` — the **n-modulus uniqueness certificate**: for pairwise-coprime `ms`,
  any two residue solutions below `ms.prod` that agree modulo every `m ∈ ms` are equal.
  This is the list generalisation of the sibling's `crt_pair_iff`/`crt_triple_iff`: a
  solution found below the product is *the* solution.

* `crt_345_unique` — a concrete instance over `[3,4,5]` (product `60`), in the style of the
  sibling's worked examples, discharged through `crt_list_unique`.

0 sorries, 0 axioms.
-/

import Mathlib

namespace ChineseRemainderConstructiveOQ05OQ02

open Nat

/-- **Combination engine.** For a list `ms` of *pairwise*-coprime naturals, the product
`ms.prod` divides any common multiple `d` of its entries. The inductive heart of the
n-modulus Chinese Remainder Theorem: the head `a` is coprime to the tail product (so
`a · t.prod ∣ d` once both factors divide `d`). -/
theorem prod_dvd_of_forall_dvd {d : ℕ} :
    ∀ {ms : List ℕ}, ms.Pairwise Nat.Coprime → (∀ m ∈ ms, m ∣ d) → ms.prod ∣ d := by
  intro ms
  induction ms with
  | nil => intro _ _; simp
  | cons a t ih =>
      intro hpw hdvd
      rw [List.pairwise_cons] at hpw
      obtain ⟨ha, htail⟩ := hpw
      have hda : a ∣ d := hdvd a (List.mem_cons.mpr (Or.inl rfl))
      have hdt : t.prod ∣ d := ih htail (fun m hm => hdvd m (List.mem_cons.mpr (Or.inr hm)))
      have hcop : Nat.Coprime a t.prod := Nat.coprime_list_prod_right_iff.mpr ha
      rw [List.prod_cons]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hda hdt

/-- **n-modulus CRT uniqueness certificate.** For a list `ms` of pairwise-coprime moduli,
any two values below `ms.prod` that share all residues `· % m` (`m ∈ ms`) are equal. Hence
a residue system has *at most one* solution in `[0, ms.prod)` — the certificate that a
found solution is the unique one. Generalises the two- and three-modulus certificates of
the sibling entry to arbitrarily many moduli. -/
theorem crt_list_unique {ms : List ℕ} (hpw : ms.Pairwise Nat.Coprime)
    {a b : ℕ} (ha : a < ms.prod) (hb : b < ms.prod)
    (h : ∀ m ∈ ms, a % m = b % m) : a = b := by
  rcases le_total a b with hab | hab
  · -- a ≤ b: every m divides b − a, hence so does ms.prod; but b − a < ms.prod.
    have hdvd : ∀ m ∈ ms, m ∣ b - a := fun m hm =>
      (Nat.modEq_iff_dvd' hab).mp (h m hm)
    have hpd : ms.prod ∣ b - a := prod_dvd_of_forall_dvd hpw hdvd
    have hz : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hpd (by omega)
    omega
  · -- b ≤ a, symmetric.
    have hdvd : ∀ m ∈ ms, m ∣ a - b := fun m hm =>
      (Nat.modEq_iff_dvd' hab).mp (h m hm).symm
    have hpd : ms.prod ∣ a - b := prod_dvd_of_forall_dvd hpw hdvd
    have hz : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hpd (by omega)
    omega

/-- **Worked instance** over the pairwise-coprime moduli `[3, 4, 5]` (product `60`), in the
style of the sibling entry's examples: any two values below `60` with the same residues
mod `3`, `4`, and `5` coincide. -/
theorem crt_345_unique {a b : ℕ} (ha : a < 60) (hb : b < 60)
    (h3 : a % 3 = b % 3) (h4 : a % 4 = b % 4) (h5 : a % 5 = b % 5) : a = b := by
  have hpw : ([3, 4, 5] : List ℕ).Pairwise Nat.Coprime := by decide
  have hprod : ([3, 4, 5] : List ℕ).prod = 60 := by decide
  refine crt_list_unique hpw (ms := [3, 4, 5]) ?_ ?_ ?_
  · rw [hprod]; exact ha
  · rw [hprod]; exact hb
  · intro m hm
    fin_cases hm <;> assumption

end ChineseRemainderConstructiveOQ05OQ02
