/-
# Abel–Ruffini (OQ-04-OQ-01-OQ-03): every group of order `p·q` is solvable

This companion file to `Proofs.AbelRuffiniOQ04OQ01OQ03` closes the one genuine gap in the
`p·q` story that the parent's *cyclic classification* cannot reach.

The parent proves the sharp classical classification of groups of order `p·q`:
`isCyclic_of_card_eq_prime_mul_prime_of_not_dvd` (cyclic when `p ∤ q − 1`) together with its
converse `dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime` (`p ∣ q − 1` when not cyclic).
But the **non-abelian** case `p ∣ q − 1` — e.g. the order-`21` group
`⟨a,b ∣ a⁷ = b³ = 1, b a b⁻¹ = a²⟩`, or every non-abelian order-`p·q` group — is left entirely
outside the cyclic/abelian results, even though such groups are still **solvable** (which is
what an Abel–Ruffini radical-tower argument actually needs).

This file supplies that missing, fully general fact:

  **`isSolvable_of_card_eq_prime_mul_prime`** — for distinct primes `p < q`, *every* finite
  group of order `p·q` is solvable, whether abelian or not.

## The argument

For `p < q` the Sylow `q`-subgroup `Q` (of prime order `q`, index `p`) is **normal**: by
Sylow III its count `n_q` divides the index `p` and satisfies `n_q ≡ 1 (mod q)`; the only
divisors of the prime `p` are `1` and `p`, and `p ≡ 1 (mod q)` is impossible since
`1 < p < q`, so `n_q = 1`. A unique Sylow subgroup is normal. Then `Q` has prime order hence
is cyclic hence solvable, and the quotient `G ⧸ Q` has prime order `p` hence is cyclic hence
solvable; the extension engine `isSolvable_of_normal_solvable_quotient` (from the parent file)
concludes `G` is solvable.

The normality argument here is the **larger-prime** one (`n_q ∣ p`, always forcing `n_q = 1`
for `p < q`), which is *unconditional* — unlike the parent's `zpowers_sylow_normal`, whose
`huniq` divisor hypothesis fails exactly in the non-abelian `p ∣ q − 1` regime. That is why
this covers the case the cyclic classification cannot.

Everything reuses the parent's exported extension engine `isSolvable_of_normal_solvable_quotient`
plus Mathlib's Sylow theory (`card_sylow_modEq_one`, `Sylow.card_dvd_index`,
`Sylow.card_eq_multiplicity`, `isCyclic_of_prime_card`, `IsCyclic.commGroup`, `isSolvable_of_comm`).
This file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `isSolvable_of_card_eq_prime_mul_prime` — order `p·q` (`p < q` primes) ⟹ solvable.
* order-`21` example — a genuinely-non-abelian-possible order (`3 ∣ 7 − 1`) that the parent's
  cyclic/abelian results do **not** reach, now shown solvable.
-/
import Mathlib
import Proofs.AbelRuffiniOQ04OQ01OQ03

namespace AbelRuffiniSylowElim

/-- **Every finite group of order `p·q` is solvable** (`p < q` distinct primes).

Reaches the full order-`p·q` landscape, including the non-abelian `p ∣ q − 1` case that the
parent's cyclic classification (`isCyclic_of_card_eq_prime_mul_prime_of_not_dvd`) cannot cover.
The Sylow `q`-subgroup is normal (its Sylow count `n_q ∣ p` and `n_q ≡ 1 mod q` force `n_q = 1`
since `1 < p < q`), of prime order hence cyclic hence solvable; the quotient has prime order `p`
hence is cyclic hence solvable; conclude by the extension engine. -/
theorem isSolvable_of_card_eq_prime_mul_prime {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hlt : p < q) (hcard : Nat.card G = p * q) :
    IsSolvable G := by
  haveI : Fintype G := Fintype.ofFinite G
  -- `q ∤ p`, since `p < q` and both are prime.
  have hqnp : ¬ q ∣ p := fun hdvd => absurd (Nat.le_of_dvd hp.out.pos hdvd) (not_le.mpr hlt)
  -- A Sylow `q`-subgroup has order exactly `q`.
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  have hQcard : Nat.card (↑Q : Subgroup G) = q := by
    have hqm : (p * q).factorization q = 1 := by
      rw [Nat.factorization_mul hp.out.pos.ne' hq.out.pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hqnp, hq.out.factorization, Finsupp.single_eq_same]
    rw [Q.card_eq_multiplicity, hcard, hqm, pow_one]
  -- Its index is `p`.
  have hidx : (↑Q : Subgroup G).index = p := by
    have hh := (↑Q : Subgroup G).index_mul_card
    rw [hQcard, hcard] at hh
    exact Nat.eq_of_mul_eq_mul_right hq.out.pos hh
  -- Sylow III: `n_q ∣ p` and `n_q ≡ 1 (mod q)` force `n_q = 1`.
  have hsylow_one : Nat.card (Sylow q G) = 1 := by
    have h_mod := card_sylow_modEq_one q G
    have h_dvd := Sylow.card_dvd_index Q
    rw [hidx] at h_dvd
    rw [Nat.ModEq, Nat.mod_eq_of_lt hq.out.one_lt] at h_mod
    rcases (Nat.dvd_prime hp.out).mp h_dvd with h1 | hpp
    · exact h1
    · rw [hpp, Nat.mod_eq_of_lt hlt] at h_mod
      exact absurd h_mod (by have := hp.out.one_lt; omega)
  -- Uniqueness ⇒ the Sylow `q`-subgroup is normal.
  haveI : Subsingleton (Sylow q G) := by
    haveI := Fintype.ofFinite (Sylow q G)
    rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
  haveI hNQ : (↑Q : Subgroup G).Normal := by
    apply Subgroup.Normal.mk; intro n hn g
    have hs : g • Q = Q := Subsingleton.elim _ _
    rw [Sylow.smul_eq_iff_mem_normalizer] at hs
    exact ((Subgroup.mem_normalizer_iff.mp hs) n).mp hn
  -- `Q` has prime order ⇒ cyclic ⇒ solvable.
  haveI : IsSolvable (↑Q : Subgroup G) := by
    haveI hcyc : IsCyclic (↑Q : Subgroup G) := isCyclic_of_prime_card hQcard
    apply isSolvable_of_comm
    letI := hcyc.commGroup
    exact fun a b => mul_comm a b
  -- `G ⧸ Q` has prime order `p` ⇒ cyclic ⇒ solvable.
  haveI : IsSolvable (G ⧸ (↑Q : Subgroup G)) := by
    have hpc : Nat.card (G ⧸ (↑Q : Subgroup G)) = p := by
      rw [← Subgroup.index_eq_card]; exact hidx
    haveI hcyc : IsCyclic (G ⧸ (↑Q : Subgroup G)) := isCyclic_of_prime_card hpc
    apply isSolvable_of_comm
    letI := hcyc.commGroup
    exact fun a b => mul_comm a b
  -- Extension of a solvable group by a solvable group is solvable.
  exact isSolvable_of_normal_solvable_quotient (↑Q : Subgroup G)

/-- **Order `21` is solvable.**  `21 = 3 · 7` with `3 ∣ 7 − 1 = 6`, so a group of order `21`
may be non-abelian (`⟨a,b ∣ a⁷ = b³ = 1, b a b⁻¹ = a²⟩`).  Such a group is therefore *not*
reached by the parent's cyclic/abelian classification of order-`p·q` groups — yet it is
solvable, by `isSolvable_of_card_eq_prime_mul_prime`.  This is the smallest order witnessing the
strict added reach of the solvability result over the cyclic one. -/
example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 21) : IsSolvable G := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact isSolvable_of_card_eq_prime_mul_prime (p := 3) (q := 7) (by norm_num)
    (hcard.trans (by norm_num))

end AbelRuffiniSylowElim
