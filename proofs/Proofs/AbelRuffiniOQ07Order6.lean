/-
  Order-6 ⟹ transposition infrastructure for `abel-ruffini-oq-07` (Gal(X⁵ − X − 1) ≅ S₅).

  (Originally an Aristotle target; both lemmas are now proved, so this file has been
  promoted to a registered gallery module — `import Proofs.AbelRuffiniOQ07Order6` in
  `Proofs.lean` — so CI verifies it like any other gallery proof.)

  ## Why this file exists
  The gallery entry `AbelRuffiniOQ07.lean` is a fully verified (0 sorry / 0 axiom)
  group-theoretic *reduction*: it proves `Gal(X⁵−X−1) ≅ S₅` modulo two number-theoretic
  inputs, of which `5 ∣ |Gal|` is now discharged unconditionally from Selmer's
  irreducibility theorem.  The SOLE remaining input is a **transposition** in the Galois
  group, which comes from the order-6 Frobenius at `p = 2`.

  The abstract Dedekind–Frobenius bridge `orderOf (arithFrobAt R G Q) = inertiaDegIn p S`
  is now PROVED and axiom-free in `DedekindFrobeniusBridge.lean`.  Instantiated at
  `R = ℤ`, `S = 𝓞 K`, `G = Gal`, and a prime `Q` over `2` (where the residue degree in
  the degree-120 splitting field equals the order of the Frobenius, namely `6`), it yields
  an element `σ ∈ f.Gal` with `orderOf σ = 6`.

  The generic group-theoretic step that turns that order-6 element into the swap the
  reduction consumes is the lemma below — the generic form of the concrete
  `frob2_pow_three_isSwap` already in the gallery file.  It is pure `S₅` combinatorics
  (Mathlib-only, no `Proofs.*` dependency), hence a clean Aristotle target.

  ## Math content
  In `S₅` the only cycle type of order `6` is `(2,3)` (partitions of `5` with `lcm = 6`:
  a part divisible by `3` forces a `3`, leaving sum `≤ 2`, so a single `2`; `6 ∉ {2..5}`).
  An element of cycle type `(2,3)` is `c₂ · c₃` (disjoint), whose cube is `c₂ · c₃³ = c₂`,
  a transposition.  Hence `orderOf σ = 6 ⟹ (σ ^ 3).IsSwap`.

  ## Status (this revision)
  Both lemmas below are now **proved** (0 sorry, 0 axiom).  The proof of
  `orderOf_eq_six_pow_three_isSwap` runs entirely through Mathlib's cycle-type API:
  the cycle type of `σ` is pinned to `{3, 2}` from `lcm = orderOf = 6` and
  `sum ≤ card (Fin 5) = 5`; the sign of `σ` is then `-1`, and a parity argument on the
  involution `σ ^ 3` (whose cycle type is `replicate k 2`) forces `k = 1`, i.e. a swap.
-/
import Mathlib

open Equiv Equiv.Perm

namespace AbelRuffiniOQ07Order6

/-- **The generic order-6 ⟹ transposition step.**
    In `S₅`, an element of order `6` necessarily has cycle type `(2,3)`, so its cube is a
    transposition.  This is the reusable form of the gallery file's concrete
    `frob2_pow_three_isSwap`; combined with the now-proved Dedekind–Frobenius bridge
    (which supplies an order-6 element of `f.Gal` from the inertia degree at `p = 2`), it
    discharges the last open input of `abel-ruffini-oq-07`. -/
theorem orderOf_eq_six_pow_three_isSwap
    (σ : Equiv.Perm (Fin 5)) (hσ : orderOf σ = 6) : (σ ^ 3).IsSwap := by
  -- `σ ≠ 1` and `σ ^ 6 = 1`.
  have hσne : σ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hσ; exact absurd hσ (by norm_num)
  have hσ6 : σ ^ 6 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  -- Step 1: classify the cycle type of `σ` as `{3, 2}`.
  have hsum : σ.cycleType.sum ≤ 5 := by
    have := σ.sum_cycleType_le; rwa [Fintype.card_fin] at this
  have hmem : ∀ x ∈ σ.cycleType, x = 2 ∨ x = 3 := by
    intro x hx
    have hdvd : x ∣ 6 := by have := dvd_of_mem_cycleType hx; rwa [hσ] at this
    have hge : 2 ≤ x := two_le_of_mem_cycleType hx
    have hle : x ≤ 5 :=
      le_trans (Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx) hsum
    interval_cases x <;> omega
  have h3 : (3 : ℕ) ∈ σ.cycleType := by
    by_contra h3
    have hall2 : ∀ x ∈ σ.cycleType, x = 2 := fun x hx =>
      (hmem x hx).resolve_right (fun h => h3 (h ▸ hx))
    have hdvd : orderOf σ ∣ 2 := by
      rw [← lcm_cycleType]; exact Multiset.lcm_dvd.mpr fun b hb => by rw [hall2 b hb]
    rw [hσ] at hdvd; norm_num at hdvd
  have h2 : (2 : ℕ) ∈ σ.cycleType := by
    by_contra h2
    have hall3 : ∀ x ∈ σ.cycleType, x = 3 := fun x hx =>
      (hmem x hx).resolve_left (fun h => h2 (h ▸ hx))
    have hdvd : orderOf σ ∣ 3 := by
      rw [← lcm_cycleType]; exact Multiset.lcm_dvd.mpr fun b hb => by rw [hall3 b hb]
    rw [hσ] at hdvd; norm_num at hdvd
  have key : σ.cycleType = {3, 2} := by
    have e3 : σ.cycleType = 3 ::ₘ σ.cycleType.erase 3 := (Multiset.cons_erase h3).symm
    have h2' : (2 : ℕ) ∈ σ.cycleType.erase 3 :=
      (Multiset.mem_erase_of_ne (by norm_num : (2 : ℕ) ≠ 3)).mpr h2
    have e2 : σ.cycleType.erase 3 = 2 ::ₘ (σ.cycleType.erase 3).erase 2 :=
      (Multiset.cons_erase h2').symm
    have hrest : ((σ.cycleType.erase 3).erase 2).sum = 0 := by
      have hexp : σ.cycleType.sum = 3 + (2 + ((σ.cycleType.erase 3).erase 2).sum) := by
        conv_lhs => rw [e3, Multiset.sum_cons, e2, Multiset.sum_cons]
      omega
    have hrest0 : (σ.cycleType.erase 3).erase 2 = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have hx2 : 2 ≤ x :=
        two_le_of_mem_cycleType (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
      have hxle : x ≤ ((σ.cycleType.erase 3).erase 2).sum :=
        Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx
      omega
    rw [e3, e2, hrest0]
  -- Step 2: `sign σ = -1` from the cycle type `{3, 2}` (sum `5`, two cycles).
  have hsign : Equiv.Perm.sign σ = -1 := by
    rw [sign_of_cycleType, key]; decide
  -- Step 3: `σ ^ 3` is an involution, so its cycle type is `replicate k 2`.
  have hpow2 : (σ ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hσ6
  have hct3 : (σ ^ 3).cycleType
      = Multiset.replicate (Multiset.card (σ ^ 3).cycleType) 2 :=
    cycleType_of_pow_prime_eq_one (p := 2) hpow2
  set k := Multiset.card (σ ^ 3).cycleType with hk
  have hne3 : σ ^ 3 ≠ 1 := by
    intro h
    have hd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h
    rw [hσ] at hd; norm_num at hd
  have hpos : 0 < k := card_cycleType_pos.mpr hne3
  have le5 : (σ ^ 3).cycleType.sum ≤ 5 := by
    have := (σ ^ 3).sum_cycleType_le; rwa [Fintype.card_fin] at this
  have esum : (σ ^ 3).cycleType.sum = k * 2 := by
    rw [hct3, Multiset.sum_replicate, smul_eq_mul]
  have hk2 : k * 2 ≤ 5 := esum ▸ le5
  -- Step 4: parity forces `k = 1` (rule out the double-transposition `k = 2`).
  have hsignpow : Equiv.Perm.sign (σ ^ 3) = -1 := by rw [map_pow, hsign]; decide
  have hsignct : Equiv.Perm.sign (σ ^ 3) = (-1) ^ (k * 2 + k) := by
    rw [sign_of_cycleType, esum]
  have hodd : Odd (k * 2 + k) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [hev.neg_one_pow] at hsignct
    rw [hsignpow] at hsignct
    exact absurd hsignct (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hk1 : k = 1 := by omega
  -- Conclude: `(σ ^ 3).cycleType = {2}`, i.e. `σ ^ 3` is a transposition.
  rw [isSwap_iff_cycleType, hct3, hk1]; rfl

/-- **Consumer assembly variant (real Galois-group facing).**
    A subgroup `G ≤ S₅` with `5 ∣ |G|` that contains an order-6 element equals `⊤`.
    This is `gal_eq_top_of_five_dvd_and_swap` with the swap input replaced by the
    order-6 element the bridge produces, so the open gap of `abel-ruffini-oq-07` becomes
    exactly "`∃ σ ∈ Gal, orderOf σ = 6`" — the abstract bridge's output. -/
theorem gal_eq_top_of_five_dvd_and_order6
    {G : Subgroup (Equiv.Perm (Fin 5))} [DecidablePred (· ∈ G)]
    (h5 : 5 ∣ Fintype.card G)
    {σ : Equiv.Perm (Fin 5)} (hσG : σ ∈ G) (hσ : orderOf σ = 6) :
    G = ⊤ := by
  refine Equiv.Perm.subgroup_eq_top_of_swap_mem ?_ ?_ (G.pow_mem hσG 3)
      (orderOf_eq_six_pow_three_isSwap σ hσ)
  · rw [Fintype.card_fin]; norm_num
  · rwa [Fintype.card_fin]

end AbelRuffiniOQ07Order6
