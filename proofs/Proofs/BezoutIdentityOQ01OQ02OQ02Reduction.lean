/-
# Primitivity is a local-global condition: nonvanishing of every prime reduction

Research: bezout-identity-oq-01-oq-02-oq-02

The parent file `BezoutIdentityOQ01OQ02OQ02.lean` characterizes primitivity of an
integer vector `v : Fin n → ℤ` in several equivalent ways — a dual pairing to `1`
(`IsPrimitive`), the entries generating the unit ideal (`isPrimitive_iff_span_eq_top`),
every common divisor being a unit (`isPrimitive_iff_forall_isUnit_of_dvd`), and the
`Finset`-gcd being `1` (`isPrimitive_iff_finsetGcd_eq_one`).  All of those live over `ℤ`
itself.

This file adds the **local (finite-field) picture**, absent from the whole `bezout`
family: primitivity is exactly the failure of every prime `p` to be a *common divisor*
of the entries, equivalently the nonvanishing of the reduction `v mod p` in `(ZMod p)ⁿ`
for **every** prime `p`.  This is the classical "a vector is primitive iff it is nonzero
modulo every prime" statement — a local-global / Hasse-flavoured reformulation that
turns the single global obstruction (`gcd ≠ 1`) into a family of independent local ones.

Main results (all dimension-free unless noted):

* `not_isPrimitive_iff_exists_prime_forall_dvd` — the sharp obstruction: `v` fails to be
  primitive **iff** some prime `p` divides *all* of its entries.  (Works even at `n = 0`
  and for `v = 0`.)
* `not_isPrimitive_of_prime_dvd` / `IsPrimitive.exists_not_dvd_of_prime` — the two
  one-directional corollaries: a common prime divisor kills primitivity, and a primitive
  vector escapes every prime in some coordinate.
* `forall_dvd_iff_reduction_eq_zero` — the bridge: `p` divides every entry iff the mod-`p`
  reduction `i ↦ (v i : ZMod p)` is the zero vector.
* `isPrimitive_iff_forall_prime_not_forall_dvd` — the positive `ℤ`-form.
* `isPrimitive_iff_forall_prime_reduction_ne_zero` — **the capstone**: `v` is primitive
  iff its reduction to `𝔽_p = ZMod p` is nonzero for every prime `p`.
* `isPrimitive_iff_forall_reduction_ne_zero` — the modulus form (no primality needed):
  primitive iff the reduction mod `m` is nonzero for every `m ≥ 2`.
* `prime_dvd_finsetGcd_iff_reduction_eq_zero` — ties the local picture back to the global
  content: a prime divides the `Finset`-gcd iff the mod-`p` reduction vanishes.

Nothing here is axiomatized — everything reduces to the parent's `ℤ`-characterizations
and the standard `ZMod`/divisibility bridge, so the whole file is
`propext`/`Classical.choice`/`Quot.sound`-only.
-/
import Mathlib
import Proofs.BezoutIdentityOQ01OQ02OQ02

namespace BezoutPrimitive

variable {n : ℕ}

/-! ### The sharp prime obstruction to primitivity -/

/-- **A prime common divisor is the sharp obstruction to primitivity.**  A vector `v`
fails to be primitive *iff* some prime `p` divides every entry of `v`.

Forward: if `v` is not primitive then, by `isPrimitive_iff_forall_isUnit_of_dvd`, some
non-unit `d` divides all entries.  A non-unit integer has `|d| ≠ 1`, hence a prime factor
`q` (`Int.exists_prime_and_dvd`); its natural absolute value `p = |q|` is a prime dividing
`d`, and therefore every entry.  Reverse: a prime `p` dividing all entries would, if `v`
were primitive, be a unit (`isPrimitive_iff_forall_isUnit_of_dvd`), contradicting
primality.  Dimension-free — correct even at `n = 0` (no vector is primitive, and the
empty conjunction makes `2` a witness) and for `v = 0`. -/
theorem not_isPrimitive_iff_exists_prime_forall_dvd (v : Fin n → ℤ) :
    ¬ IsPrimitive v ↔ ∃ p : ℕ, p.Prime ∧ ∀ i, (p : ℤ) ∣ v i := by
  constructor
  · intro hv
    rw [isPrimitive_iff_forall_isUnit_of_dvd] at hv
    push_neg at hv
    obtain ⟨d, hd_dvd, hd_nonunit⟩ := hv
    have hne1 : d.natAbs ≠ 1 := fun hh => hd_nonunit (Int.isUnit_iff_natAbs_eq.mpr hh)
    obtain ⟨q, hq_prime, hq_dvd⟩ := Int.exists_prime_and_dvd hne1
    exact ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hq_prime,
      fun i => Int.natAbs_dvd.mpr (hq_dvd.trans (hd_dvd i))⟩
  · rintro ⟨p, hp, hdvd⟩ hv
    have hu := (isPrimitive_iff_forall_isUnit_of_dvd v).mp hv (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega

/-- **A common prime divisor kills primitivity** (the easy half of the obstruction). -/
theorem not_isPrimitive_of_prime_dvd (p : ℕ) (hp : p.Prime) {v : Fin n → ℤ}
    (hd : ∀ i, (p : ℤ) ∣ v i) : ¬ IsPrimitive v :=
  (not_isPrimitive_iff_exists_prime_forall_dvd v).mpr ⟨p, hp, hd⟩

/-- **A primitive vector escapes every prime in some coordinate.**  The contrapositive
form of the obstruction: for a primitive `v` and any prime `p`, at least one entry is not
divisible by `p`. -/
theorem IsPrimitive.exists_not_dvd_of_prime {v : Fin n → ℤ} (hv : IsPrimitive v)
    (p : ℕ) (hp : p.Prime) : ∃ i, ¬ (p : ℤ) ∣ v i := by
  by_contra h
  push_neg at h
  exact not_isPrimitive_of_prime_dvd p hp h hv

/-- **The positive `ℤ`-form.**  `v` is primitive iff no prime divides all of its entries. -/
theorem isPrimitive_iff_forall_prime_not_forall_dvd (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∀ p : ℕ, p.Prime → ¬ ∀ i, (p : ℤ) ∣ v i := by
  constructor
  · intro hv p hp hdvd
    exact not_isPrimitive_of_prime_dvd p hp hdvd hv
  · intro h
    by_contra hv
    obtain ⟨p, hp, hdvd⟩ := (not_isPrimitive_iff_exists_prime_forall_dvd v).mp hv
    exact h p hp hdvd

/-! ### The finite-field reduction picture -/

/-- **Bridge to the mod-`p` reduction.**  A natural number `p > 0` divides every entry of
`v` iff the reduction `i ↦ (v i : ZMod p)` is the zero vector of `(ZMod p)ⁿ`.  Entrywise
this is `ZMod.intCast_zmod_eq_zero_iff_dvd`. -/
theorem forall_dvd_iff_reduction_eq_zero (p : ℕ) [NeZero p] (v : Fin n → ℤ) :
    (∀ i, (p : ℤ) ∣ v i) ↔ (fun i => ((v i : ZMod p))) = 0 := by
  constructor
  · intro h
    funext i
    simp only [Pi.zero_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h i
  · intro h i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun h i
    simpa only [Pi.zero_apply] using this

/-- **The local-global characterization (capstone).**  An integer vector is primitive iff
its reduction to the finite field `𝔽_p = ZMod p` is nonzero for **every** prime `p`.  The
single global condition `gcd = 1` is thereby decomposed into a family of independent local
nonvanishing conditions, one per prime. -/
theorem isPrimitive_iff_forall_prime_reduction_ne_zero (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∀ p : ℕ, p.Prime → (fun i => ((v i : ZMod p))) ≠ 0 := by
  rw [isPrimitive_iff_forall_prime_not_forall_dvd]
  refine forall_congr' fun p => ?_
  refine imp_congr_right fun hp => ?_
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [forall_dvd_iff_reduction_eq_zero]

/-- **A common non-unit divisor kills primitivity** (modulus form of the obstruction). -/
theorem not_isPrimitive_of_forall_dvd {m : ℤ} (hm : ¬ IsUnit m) {v : Fin n → ℤ}
    (hd : ∀ i, m ∣ v i) : ¬ IsPrimitive v :=
  fun hv => hm ((isPrimitive_iff_forall_isUnit_of_dvd v).mp hv m hd)

/-- **The modulus form.**  Primality is not actually needed for the reduction picture:
`v` is primitive iff its reduction mod `m` is nonzero for every modulus `m ≥ 2`.  The
extra composite moduli are redundant (a nonzero reduction mod `p ∣ m` forces a nonzero
reduction mod `m`), but the statement is often the convenient one. -/
theorem isPrimitive_iff_forall_reduction_ne_zero (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∀ m : ℕ, 2 ≤ m → (fun i => ((v i : ZMod m))) ≠ 0 := by
  constructor
  · intro hv m hm hzero
    haveI : NeZero m := ⟨by omega⟩
    have hdvd := (forall_dvd_iff_reduction_eq_zero m v).mpr hzero
    have hmu : ¬ IsUnit (m : ℤ) := by
      rw [Int.isUnit_iff]
      have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      omega
    exact not_isPrimitive_of_forall_dvd hmu hdvd hv
  · intro h
    rw [isPrimitive_iff_forall_prime_reduction_ne_zero]
    exact fun p hp => h p hp.two_le

/-! ### Local picture vs. the global content -/

/-- **The local reductions detect the content.**  A prime `p` divides the `Finset`-gcd
(the content) of `v` iff the mod-`p` reduction of `v` vanishes.  This is the per-prime
refinement of `isPrimitive_iff_finsetGcd_eq_one`: primitivity is `gcd = 1`, i.e. no prime
divides the content, i.e. every prime reduction is nonzero. -/
theorem prime_dvd_finsetGcd_iff_reduction_eq_zero (p : ℕ) [NeZero p] (v : Fin n → ℤ) :
    (p : ℤ) ∣ Finset.univ.gcd v ↔ (fun i => ((v i : ZMod p))) = 0 := by
  rw [← forall_dvd_iff_reduction_eq_zero]
  constructor
  · intro h i
    exact h.trans (Finset.gcd_dvd (Finset.mem_univ i))
  · intro h
    exact Finset.dvd_gcd fun i _ => h i

end BezoutPrimitive
