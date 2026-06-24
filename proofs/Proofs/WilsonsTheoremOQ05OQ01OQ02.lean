import Mathlib

/-
# Gauss's prime-power form of Wilson's theorem

**Open Question (`wilsons-theorem-oq-05-oq-01-oq-02`)**: the parent chain
`wilsons-theorem-oq-05 → …-oq-01` classified the *classical* residue
`(n - 1)! mod n` for every `n` (prime ⟹ `n-1`, `n = 4` ⟹ `2`, composite `≠ 4`
⟹ `0`).  That trichotomy is about the bare factorial `(n-1)!`.  This file follows
the *other* registered branch: instead of the residue of `(n-1)!`, study the
**product of the units of `ℤ/nℤ`** — equivalently `∏_{1 ≤ a < n, gcd(a,n)=1} a`
— and prove the **prime-power generalisation of Wilson's theorem** due to Gauss.

Mathlib proves Wilson only for a *prime* modulus, where `ℤ/pℤ` is a field:
`prod_univ_units_id_eq_neg_one` gives `∏_{x ∈ (ℤ/pℤ)ˣ} x = -1`, and its proof
pairs each unit with its inverse, the only self-paired survivors being `±1`
(`Units.inv_eq_self_iff`, which needs an integral domain).  For a prime *power*
`p^k` the ring `ℤ/p^kℤ` is **not** a domain, so that lemma does not apply.  The
correct statement is nonetheless

  `∏_{x ∈ (ℤ/p^kℤ)ˣ} x = -1`   for every **odd** prime `p` and `k ≥ 1`,

and the reason is structural rather than field-theoretic: `(ℤ/p^kℤ)ˣ` is a
**cyclic** group (Gauss's primitive-root theorem, `ZMod.isCyclic_units_of_prime_pow`)
of *even* order, and in any finite cyclic group of even order the equation
`x² = 1` has *exactly two* solutions, `1` and the unique element of order two.

## The reusable engine

The heart of the file is a clean group-theoretic lemma, of independent interest
and absent from Mathlib in this packaged form:

* `prod_univ_eq_orderTwo` — **in a finite cyclic group, if `t` is an element with
  `t·t = 1` and `t ≠ 1`, then the product of *all* the group elements is `t`.**
  (`t` is then automatically the unique involution.)  The proof is the
  inverse-pairing involution `x ↦ x⁻¹` on `univ.erase t`: cyclicity forces the
  only fixed points of squaring to be `{1, t}` (`IsCyclic.card_pow_eq_one_le`
  bounds the solution count of `x² = 1` by `2`), so after erasing `t` the lone
  surviving fixed point is `1` and the pairing kills everything, leaving `t`.

## The number-theoretic payload

* `gauss_prime_pow_units` — `∏_{x ∈ (ℤ/p^kℤ)ˣ} x = -1` for odd prime `p`, `k ≥ 1`;
* `gauss_prime_pow_cast` — the same identity pushed into `ℤ/p^kℤ`;
* `wilson_units_prime` — the `k = 1` slice recovers the classical prime case
  (matching Mathlib's `prod_univ_units_id_eq_neg_one`), so this is a genuine
  generalisation of Wilson's theorem and not a sibling result;
* `prod_units_zmod_nine` — a concrete check at `p = 3, k = 2`: the six units of
  `ℤ/9ℤ` multiply to `-1 = 8`.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace WilsonsTheoremOQ05OQ01OQ02

open Finset

/-! ### The group-theoretic engine -/

/-- In a finite cyclic group, the only solutions of `x² = 1` are `1` and a fixed
element `t` of order two: once we know one nontrivial square root `t` of `1`,
every square root is `1` or `t`.  This is the cyclic replacement for the
integral-domain fact `Units.inv_eq_self_iff`. -/
theorem sq_eq_one_iff_eq_one_or_eq
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) {u : G} (hu : u * u = 1) :
    u = 1 ∨ u = t := by
  -- The squaring-fixed set has at most two elements, and `{1, t}` already gives two.
  have hle : (univ.filter (fun a : G => a ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hsub : ({1, t} : Finset G) ⊆ univ.filter (fun a : G => a ^ 2 = 1) := by
    intro x hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases mem_insert.1 hx with h | h
    · subst h; simp
    · rw [mem_singleton] at h; subst h; rw [sq]; exact ht2
  have hcard : ({1, t} : Finset G).card = 2 := card_pair (Ne.symm ht1)
  have heq : ({1, t} : Finset G) = univ.filter (fun a : G => a ^ 2 = 1) :=
    eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have humem : u ∈ ({1, t} : Finset G) := by
    rw [heq, mem_filter]; exact ⟨mem_univ _, by rw [sq]; exact hu⟩
  rcases mem_insert.1 humem with h | h
  · exact Or.inl h
  · exact Or.inr (mem_singleton.1 h)

/-- **The product of all elements of a finite cyclic group is its unique
involution.**  If `t · t = 1` and `t ≠ 1` in a finite cyclic group `G`, then
`∏_{x ∈ G} x = t`.  (Such a `t` is automatically the only element of order two.)
The proof pairs each element with its inverse on `univ.erase t`. -/
theorem prod_univ_eq_orderTwo
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∏ x : G, x = t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- The inverse-pairing involution wipes out everything once `t` is removed.
  have key : ∏ x ∈ univ.erase t, x = 1 := by
    refine prod_involution (fun a _ => a⁻¹) (fun a _ => mul_inv_cancel a) ?_ ?_ ?_
    · -- non-fixed: `a ≠ 1 → a⁻¹ ≠ a`
      intro a ha hane hcontra
      have hcontra' : a⁻¹ = a := hcontra
      -- `a⁻¹ = a` forces `a * a = 1`, so `a = 1` or `a = t`; but `a ≠ t`, hence `a = 1`.
      have hsq : a * a = 1 := by nth_rewrite 1 [← hcontra']; exact inv_mul_cancel a
      rcases sq_eq_one_iff_eq_one_or_eq ht2 ht1 hsq with h | h
      · exact hane h
      · exact (mem_erase.1 ha).1 h
    · -- closure: `a⁻¹ ∈ univ.erase t`
      intro a ha
      refine mem_erase.2 ⟨?_, mem_univ _⟩
      intro hc
      have hc' : a⁻¹ = t := hc
      -- `a⁻¹ = t` ⟹ `a = t⁻¹ = t`, contradicting `a ≠ t`.
      exact (mem_erase.1 ha).1 (by rw [← inv_inv a, hc', htinv])
    · -- involutivity
      intro a _; exact inv_inv a
  calc ∏ x : G, x = ∏ x ∈ insert t (univ.erase t), x := by
        rw [insert_erase (mem_univ t)]
    _ = t * ∏ x ∈ univ.erase t, x := prod_insert (notMem_erase t univ)
    _ = t := by rw [key, mul_one]

/-! ### Gauss's prime-power Wilson theorem -/

/-- `-1 ≠ 1` among the units of `ℤ/mℤ` whenever the modulus `m` exceeds `2`
(so `2 ≠ 0` in `ℤ/mℤ`).  This is the unique-nontrivial-square-root input the
engine needs, for both the prime-power and prime moduli below. -/
theorem neg_one_ne_one_units {m : ℕ} [NeZero m] (hm : 2 < m) :
    (-1 : (ZMod m)ˣ) ≠ 1 := by
  intro h
  have hc : (-1 : ZMod m) = 1 := by simpa using congrArg Units.val h
  have h2 : (2 : ZMod m) = 0 := by linear_combination -hc
  have hdvd : m ∣ 2 := by
    have hcast : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h2
    exact (ZMod.natCast_eq_zero_iff 2 m).1 hcast
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

variable {p : ℕ}

/-- **Gauss's prime-power form of Wilson's theorem.**  For every odd prime `p`
and every `k ≥ 1`, the product of all units of `ℤ/p^kℤ` is `-1`. -/
theorem gauss_prime_pow_units (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : k ≠ 0)
    [NeZero (p ^ k)] : ∏ x : (ZMod (p ^ k))ˣ, x = -1 := by
  haveI : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  have h2lt : 2 < p ^ k :=
    lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) (Nat.le_self_pow hk p)
  exact prod_univ_eq_orderTwo (by simp) (neg_one_ne_one_units h2lt)

/-- Gauss's identity pushed into the ring `ℤ/p^kℤ`: the product of the units,
viewed as ring elements, is `-1`. -/
theorem gauss_prime_pow_cast (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : k ≠ 0)
    [NeZero (p ^ k)] : (∏ x : (ZMod (p ^ k))ˣ, (x : ZMod (p ^ k))) = -1 := by
  have h := gauss_prime_pow_units hp hp2 hk
  have e : (Units.coeHom (ZMod (p ^ k))) (∏ x : (ZMod (p ^ k))ˣ, x)
         = ∏ x : (ZMod (p ^ k))ˣ, (x : ZMod (p ^ k)) := map_prod _ _ _
  rw [← e, h]; simp

/-- The `k = 1` slice recovers the **classical Wilson theorem** for a prime
modulus, `∏_{x ∈ (ℤ/pℤ)ˣ} x = -1`. -/
theorem wilson_units_prime (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p] :
    ∏ x : (ZMod p)ˣ, x = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  have h2lt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  exact prod_univ_eq_orderTwo (by simp) (neg_one_ne_one_units h2lt)

/-! ### A concrete check: the six units of `ℤ/9ℤ` -/

/-- The units of `ℤ/9ℤ` are `{1, 2, 4, 5, 7, 8}` and their product is `-1 = 8`,
the `p = 3, k = 2` instance of Gauss's prime-power Wilson theorem. -/
theorem prod_units_zmod_nine :
    (∏ x : (ZMod 9)ˣ, (x : ZMod 9)) = -1 := by
  haveI : NeZero ((3 : ℕ) ^ 2) := ⟨by norm_num⟩
  have h := gauss_prime_pow_cast (p := 3) (by norm_num) (by norm_num) (k := 2) (by norm_num)
  simpa using h

end WilsonsTheoremOQ05OQ01OQ02
