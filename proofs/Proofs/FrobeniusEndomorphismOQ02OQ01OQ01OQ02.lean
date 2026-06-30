/-
  The Frobenius power subgroups recover the divisor lattice:
  `⟨frob^e⟩ ≤ ⟨frob^d⟩ ⇔ d ∣ e`.

  Let `K` be a finite field of characteristic `p`, an extension of its prime
  subfield `𝔽_p = ZMod p` of degree `n = [K : 𝔽_p]`.  The Galois group
  `Gal(K / 𝔽_p) = ⟨frob⟩` is cyclic of order `n`, and the parent entry
  (`FrobeniusEndomorphismOQ02OQ01OQ01`) identified its rung-by-rung fixed fields:
  for every divisor `d ∣ n` the cyclic subgroup `⟨frob^d⟩` has fixed field the
  unique copy of `𝔽_{p^d}` inside `K`, and the assignment `d ↦ fixedField⟨frob^d⟩`
  is injective on the divisors of `n`.

  That gives the *set-level* bijection `{subfields} ↔ {divisors of n}`.  This file
  upgrades it to the **lattice** statement on the subgroup side: it pins down the
  inclusions among the subgroups `⟨frob^d⟩` themselves, purely in terms of
  divisibility of the exponents.  This is exactly the second open question left by
  the parent: *identify the subfield containment `𝔽_{p^d} ⊆ 𝔽_{p^e} ⇔ d ∣ e`
  directly in terms of Frobenius powers, as `⟨frob^e⟩ ≤ ⟨frob^d⟩ ⇔ d ∣ e`,
  recovering the lattice (not just set) isomorphism.*

  ## The mathematics

  The result is not special to the Frobenius — it is the lattice of cyclic
  subgroups of a finite cyclic group, expressed through `orderOf`.  The clean
  general fact is:

  > For an element `g` of a group and `d ∣ orderOf g`,
  > `g ^ e ∈ ⟨g ^ d⟩ ⇔ d ∣ e`.

  The `⟸` direction is structural: if `e = d·m` then `g^e = (g^d)^m ∈ ⟨g^d⟩`.
  The `⟹` direction is the arithmetic heart.  Writing `g^e = (g^d)^k` for an
  integer `k` gives `g^(d·k − e) = 1`, hence `orderOf g ∣ d·k − e`; since
  `d ∣ orderOf g` we get `d ∣ d·k − e`, and as `d ∣ d·k` this forces `d ∣ e`.

  Passing to subgroups (`Subgroup.zpowers_le`) turns membership into containment,
  and feeding in `orderOf (frob p) = n` (the order of the Frobenius) specialises
  everything to the Galois group.

  ## Results

  * `pow_mem_zpowers_pow_iff_dvd` — the general group lemma
    `g ^ e ∈ ⟨g ^ d⟩ ⇔ d ∣ e` for `d ∣ orderOf g`;
  * `zpowers_pow_le_iff` — its subgroup form
    `⟨g ^ e⟩ ≤ ⟨g ^ d⟩ ⇔ d ∣ e`;
  * `zpowers_frob_pow_le_iff` — **the headline**: for `d ∣ n`,
    `⟨frob^e⟩ ≤ ⟨frob^d⟩ ⇔ d ∣ e`, the order-reversing divisor lattice in the
    Galois group;
  * `zpowers_frob_pow_eq_iff` — the resulting injectivity on the subgroup side:
    for `d, e ∣ n`, `⟨frob^d⟩ = ⟨frob^e⟩ ⇔ d = e`.

  Together with the parent's `fixedField_frob_pow_injOn_divisors`, the inclusions
  `⟨frob^e⟩ ≤ ⟨frob^d⟩ ⇔ d ∣ e` make `d ↦ ⟨frob^d⟩` an order-reversing
  embedding of the divisors of `n` into the subgroup lattice — the lattice
  isomorphism behind the Galois correspondence for finite fields.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.  Built on Mathlib's
  `orderOf_dvd_iff_zpow_eq_one`, `Subgroup.zpowers_le`, `Subgroup.mem_zpowers_iff`
  and the parent's `orderOf_frob`.
-/
import Mathlib
-- Only `frob` and `orderOf_frob` from the grandparent are needed; the divisor-lattice
-- *fixed fields* are the subject of the direct parent `FrobeniusEndomorphismOQ02OQ01OQ01`.
import Proofs.FrobeniusEndomorphismOQ02

namespace FrobeniusEndomorphismOQ02OQ01OQ01OQ02

open FrobeniusEndomorphismOQ02
open Module (finrank)

/-! ### Part I: the general group lemma -/

/-- **The cyclic-subgroup lattice, membership form.**  For an element `g` of a
group and a divisor `d ∣ orderOf g`, the power `g ^ e` lies in the cyclic
subgroup `⟨g ^ d⟩` exactly when `d ∣ e`.

`⟸` is structural (`g^(d·m) = (g^d)^m`).  `⟹` is arithmetic: from
`g^e = (g^d)^k` one gets `g^(d·k − e) = 1`, so `orderOf g ∣ d·k − e`; with
`d ∣ orderOf g` this gives `d ∣ d·k − e`, and `d ∣ d·k` forces `d ∣ e`. -/
theorem pow_mem_zpowers_pow_iff_dvd {G : Type*} [Group G] {g : G} {d e : ℕ}
    (hd : d ∣ orderOf g) :
    g ^ e ∈ Subgroup.zpowers (g ^ d) ↔ d ∣ e := by
  constructor
  · intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    -- `hk : (g ^ d) ^ k = g ^ e` (with `k : ℤ`); rewrite to a single `zpow`.
    rw [← zpow_natCast g d, ← zpow_mul, ← zpow_natCast g e] at hk
    -- `hk : g ^ ((d : ℤ) * k) = g ^ (e : ℤ)`, hence `g ^ ((d : ℤ) * k − e) = 1`.
    have h1 : g ^ ((d : ℤ) * k - (e : ℤ)) = 1 := by
      rw [zpow_sub, hk, mul_inv_cancel]
    rw [← orderOf_dvd_iff_zpow_eq_one] at h1
    -- `h1 : (orderOf g : ℤ) ∣ (d : ℤ) * k − e`.
    have hdord : (d : ℤ) ∣ (orderOf g : ℤ) := Int.natCast_dvd_natCast.mpr hd
    have hdsub : (d : ℤ) ∣ ((d : ℤ) * k - (e : ℤ)) := hdord.trans h1
    have hde : (d : ℤ) ∣ (e : ℤ) := by
      have hdk : (d : ℤ) ∣ (d : ℤ) * k := dvd_mul_right _ _
      have := dvd_sub hdk hdsub
      simpa using this
    exact_mod_cast hde
  · rintro ⟨m, rfl⟩
    rw [pow_mul]
    exact pow_mem (Subgroup.mem_zpowers _) m

/-- **The cyclic-subgroup lattice, subgroup form.**  For `d ∣ orderOf g`,
`⟨g ^ e⟩ ≤ ⟨g ^ d⟩ ⇔ d ∣ e`. -/
theorem zpowers_pow_le_iff {G : Type*} [Group G] {g : G} {d e : ℕ}
    (hd : d ∣ orderOf g) :
    Subgroup.zpowers (g ^ e) ≤ Subgroup.zpowers (g ^ d) ↔ d ∣ e := by
  rw [Subgroup.zpowers_le]
  exact pow_mem_zpowers_pow_iff_dvd hd

/-! ### Part II: the Frobenius / Galois specialisation -/

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

/-- **The headline.**  In the cyclic Galois group `Gal(K / 𝔽_p) = ⟨frob⟩` of
order `n = [K : 𝔽_p]`, for a divisor `d ∣ n` the subgroup inclusion
`⟨frob^e⟩ ≤ ⟨frob^d⟩` holds exactly when `d ∣ e`.

This is the order-reversing divisor lattice on the subgroup side of the Galois
correspondence: larger fields `𝔽_{p^e}` (`d ∣ e`) correspond to smaller
stabilising subgroups `⟨frob^e⟩ ≤ ⟨frob^d⟩`. -/
theorem zpowers_frob_pow_le_iff {d e : ℕ} (hd : d ∣ finrank (ZMod p) K) :
    Subgroup.zpowers (frob p ^ e : K ≃ₐ[ZMod p] K)
        ≤ Subgroup.zpowers (frob p ^ d) ↔ d ∣ e := by
  apply zpowers_pow_le_iff
  rw [orderOf_frob]
  exact hd

/-- **Injectivity on the subgroup side.**  For divisors `d, e ∣ n` the cyclic
subgroups `⟨frob^d⟩` and `⟨frob^e⟩` coincide exactly when `d = e`: distinct
divisors give distinct subgroups.  This is the subgroup-lattice counterpart of
the parent's `fixedField_frob_pow_injOn_divisors`, and combined with the
`≤`-criterion it makes `d ↦ ⟨frob^d⟩` an order-reversing embedding of the
divisors of `n`. -/
theorem zpowers_frob_pow_eq_iff {d e : ℕ}
    (hd : d ∣ finrank (ZMod p) K) (he : e ∣ finrank (ZMod p) K) :
    Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K)
        = Subgroup.zpowers (frob p ^ e) ↔ d = e := by
  constructor
  · intro h
    -- `⟨frob^d⟩ ≤ ⟨frob^e⟩` gives `e ∣ d`; the reverse gives `d ∣ e`.
    have h1 : e ∣ d := (zpowers_frob_pow_le_iff p he).mp (le_of_eq h)
    have h2 : d ∣ e := (zpowers_frob_pow_le_iff p hd).mp (le_of_eq h.symm)
    exact Nat.dvd_antisymm h2 h1
  · rintro rfl
    rfl

end FrobeniusEndomorphismOQ02OQ01OQ01OQ02
