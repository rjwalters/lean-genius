/-
  TURNKEY ORPHAN DRAFT — Step 3 (`sylow_p_is_pcycle`) of the Galois-direction
  classification `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.

  The registered file carries `sylow_p_is_pcycle` as a `sorry` stub (Step 3 of
  the 5-step plan). This companion proves the SAME statement (re-stated
  standalone — Step 3 references no parent-file definitions). It is an ORPHAN:
  NOT imported by `Proofs.lean`, so it is OUTSIDE any CI/registered build gate
  and cannot affect the green registered build. Once a build backend is
  available: build this file; if green, fold the body into the registered
  `sylow_p_is_pcycle` (the signatures match verbatim).

  ## Status — SOURCE-VERIFIED, BUILD-PENDING (S15 authored; S17 corrected, researcher-5)

  Authored under DUAL BLACKOUT: Aristotle MCP `prove`/`prove_file` return 404
  ("Resource not found"); the host-wide `proofs/.lake` is a self-referential
  symlink (`.lake -> .lake`), so every worktree's Mathlib package oleans are
  inaccessible and `docker-build.sh` would trigger a multi-GB Mathlib re-clone
  (the known git-128 failure). No local compile possible.

  S17 (researcher-5): checked the `?`-flagged calls against the Mathlib source
  mirror (`/private/tmp/mathlib-grep`, Mathlib v4.26.0) and fixed three real
  signature bugs that would have failed the first build:
    1. `padicValNat_factorial_self`: the lemma is `Nat.factorization_factorial`
       (namespace `Nat`, NOT a `Nat.Prime` method) and takes an explicit bound
       `log p n < b`; supplied `b = p` via `Nat.log_lt_self p hp.pos.ne'`.
    2. `isCyclic_of_prime_card` takes the **`Nat.card`** equation, not
       `Fintype.card`; now fed `hcardP` (was `hcardP_ft`).
    3. `Equiv.Perm.isCycle_of_prime_order` takes **two** args stated over
       `orderOf σ` — `(orderOf σ).Prime` and `#σ.support < 2 * orderOf σ` — not
       `(hp) (hords) (hsupp_lt)`; rewrote accordingly.
  Inline confidence: ★ = source-verified / very standard; ? = medium (the
  orbit–stabilizer / `Fintype` vs `Nat.card` plumbing at Step A/B still wants a
  first build to confirm instance resolution). The mathematics is unchanged.

  See `research/problems/.../knowledge.md` §"S15 Step-3 discharge plan" for the
  strategy, the shared `|P| = p` kernel (common to Steps 1 and 3), and fallbacks.
-/
import Mathlib

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep3

variable {p : ℕ} [Fact p.Prime]

/-- Legendre at the prime `p` itself: `v_p(p!) = 1`.
    `v_p(p!) = ∑_{i=1}^{p-1} ⌊p / p^i⌋`; the `i = 1` term is `1`, every `i ≥ 2`
    term is `0` (since `p^i > p`), so the sum is `1`.  Self-contained; the only
    genuinely new obligation in Step 3. -/
theorem padicValNat_factorial_self (hp : p.Prime) :
    (Nat.factorial p).factorization p = 1 := by
  -- ★ `Nat.factorization_factorial (hp : p.Prime) {n b} (h : log p n < b) :`
  --   `(n)!.factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i`  (Legendre; takes a bound).
  --   Use the bound `b = p` via `Nat.log_lt_self p hp.pos.ne' : log p p < p`.
  have hlog : Nat.log p p < p := Nat.log_lt_self p hp.pos.ne'
  rw [Nat.factorization_factorial hp hlog]
  rw [Finset.sum_eq_single 1]
  · rw [pow_one, Nat.div_self hp.pos]
  · intro i hi hne
    apply Nat.div_eq_of_lt
    have hi2 : 2 ≤ i := by
      rcases Finset.mem_Ico.mp hi with ⟨h1, _⟩; omega
    calc p < p ^ 2 := by nlinarith [hp.two_le]
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos.le hi2
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨le_refl 1, hp.one_lt⟩) h

/-- **Step 3 (p-cycle structure).** The Sylow-`p` subgroup `P` of a primitive
    solvable `H ≤ S_p` is generated (via the inclusion `ι = H.subtype ∘ P.subtype`)
    by a single `p`-cycle `σ ∈ S_p`. -/
theorem sylow_p_is_pcycle
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H)
    (P : Sylow p H) :
    ∃ σ : Equiv.Perm (ZMod p), σ.IsCycle ∧ σ.support.card = p ∧
      ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
        Subgroup.zpowers σ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- ι : ↥P → S_p, composite of the two subgroup inclusions (a MonoidHom).
  set ι : (P : Subgroup H) →* Equiv.Perm (ZMod p) :=
    H.subtype.comp (P : Subgroup H).subtype with hιdef
  have hι_inj : Function.Injective ι :=
    (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective _)  -- ★
  ----------------------------------------------------------------
  -- Step A:  p ∣ Nat.card H   (primitivity ⇒ transitivity on a p-point set).
  ----------------------------------------------------------------
  haveI : MulAction.IsPretransitive H (ZMod p) := _hPrim.toIsPretransitive  -- ★
  have horbit : Nat.card (MulAction.orbit H (0 : ZMod p)) = p := by
    have huniv : MulAction.orbit H (0 : ZMod p) = Set.univ :=
      MulAction.orbit_eq_univ (0 : ZMod p)                                -- ★
    rw [huniv, Nat.card_congr (Equiv.Set.univ (ZMod p)),
        Nat.card_eq_fintype_card, ZMod.card]                             -- ★
  have hpH : p ∣ Nat.card H := by
    -- ? bearer (Nat.card form): orbit–stabilizer
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      H (0 : ZMod p)
    exact ⟨Nat.card (MulAction.stabilizer H (0 : ZMod p)), by rw [← hos, horbit]⟩
  ----------------------------------------------------------------
  -- Step B:  Nat.card ↥P = p.
  ----------------------------------------------------------------
  -- lower bound: p ∣ |P|  (Sylow card = p ^ v_p(|H|), and v_p(|H|) ≥ 1).
  have hkpos : 0 < (Nat.card H).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpH            -- ★ (Step 5 uses this)
  have hpP : p ∣ Nat.card (P : Subgroup H) := by
    rw [P.card_eq_multiplicity]                                          -- ★ (Step 5 uses this)
    exact dvd_pow_self p hkpos.ne'
  -- upper bound: v_p(|H|) ≤ v_p(p!) = 1   (Lagrange in S_p + Legendre).
  have hHdvd : Nat.card H ∣ Nat.card (Equiv.Perm (ZMod p)) :=
    Subgroup.card_subgroup_dvd_card H                                    -- ?
  have hcard_perm : Nat.card (Equiv.Perm (ZMod p)) = Nat.factorial p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]          -- ?
  have hvpH : (Nat.card H).factorization p ≤ 1 := by
    have hle : (Nat.card H).factorization p
        ≤ (Nat.card (Equiv.Perm (ZMod p))).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by rw [hcard_perm]; exact (Nat.factorial_pos p).ne')).2 hHdvd p  -- ?
    rwa [hcard_perm, padicValNat_factorial_self hp] at hle
  have hcardP : Nat.card (P : Subgroup H) = p := by
    have hk1 : (Nat.card H).factorization p = 1 := le_antisymm hvpH hkpos
    rw [P.card_eq_multiplicity, hk1, pow_one]                            -- ★
  have hcardP_ft : Fintype.card (P : Subgroup H) = p := by
    rw [← Nat.card_eq_fintype_card]; exact hcardP
  ----------------------------------------------------------------
  -- Step C:  ↥P cyclic of prime order ⇒ generator a; σ := ι a is a p-cycle.
  ----------------------------------------------------------------
  -- ★ `isCyclic_of_prime_card [Fact p.Prime] (h : Nat.card α = p) : IsCyclic α`
  --   (takes the `Nat.card` equation, NOT `Fintype.card`).
  haveI hcyc : IsCyclic (P : Subgroup H) := isCyclic_of_prime_card hcardP
  obtain ⟨a, ha⟩ := hcyc.exists_generator                                 -- ★ (∀ x, x ∈ zpowers a)
  have horda : orderOf a = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hcardP_ft]              -- ?
  have hords : orderOf (ι a) = p := by
    rw [orderOf_injective ι hι_inj a, horda]                             -- ★
  have hcycσ : (ι a).IsCycle := by
    -- ★ `Equiv.Perm.isCycle_of_prime_order (h1 : (orderOf σ).Prime)`
    --   `(h2 : #σ.support < 2 * orderOf σ) : σ.IsCycle`  — TWO args, stated over `orderOf σ`.
    have hprime : (orderOf (ι a)).Prime := hords ▸ hp
    have hsupp_lt : (ι a).support.card < 2 * orderOf (ι a) := by
      have hle : (ι a).support.card ≤ Fintype.card (ZMod p) :=
        Finset.card_le_univ _
      rw [ZMod.card] at hle
      rw [hords]; omega
    exact Equiv.Perm.isCycle_of_prime_order hprime hsupp_lt
  refine ⟨ι a, hcycσ, ?_, ?_⟩
  · -- support.card = orderOf = p
    rw [← hcycσ.orderOf, hords]                                          -- ★ IsCycle.orderOf
  · -- ι sends every element of P into ⟨σ⟩
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha g)                 -- ★ (a ^ k = g)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow ι a k, hk]⟩  -- ★

end AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep3
