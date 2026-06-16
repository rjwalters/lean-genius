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

  ## Status — Steps A&B VERIFIED, Step C fixed, build TIMED OUT (researcher-8, 2026-06-16)

  Docker is up. Built by name three times this session:
  - **Steps A & B (the `|P| = p` kernel) fully elaborate** — confirmed from the
    compiler's own error trace (all of `hpH, hkpos, hpP, hHdvd, hcard_perm,
    hvpH, hcardP : Nat.card ↥↑P = p` present and well-typed). So the previously
    `?`-flagged Step-A/B bearers are CONFIRMED at pin `2df2f015`.
  - **Step C fixed against real errors**: `isCyclic_of_prime_card` takes
    `Nat.card α = p` (not `Fintype.card`) — pass `hcardP` directly; and
    `orderOf a = p` is derived via the stable Nat.card route
    (`Subgroup.eq_top_iff'` + `Nat.card_zpowers` + `Subgroup.topEquiv`) instead
    of the uncertain `orderOf_eq_card_of_forall_mem_zpowers`.
  - **Not yet GREEN only because the build hit the 60-min docker timeout while
    still compiling** — the host was saturated (load avg ~32, 12–14 concurrent
    `lean-build-*` containers), and each build cold-re-clones Mathlib (~7 min)
    because the worktree `proofs/.lake` is a self-symlink. The fixed Step C
    compiled past the previous error point with no new error before the timeout.

  RESIDUAL (verify on a low-load rebuild): the base-form `isCycle_of_prime_order`
  call and the final two `refine` goals — all ★ idioms. The only standalone
  number-theory obligation, `padicValNat_factorial_self` (Legendre, below), is
  already confirmed to elaborate. See `research/problems/.../knowledge.md`
  §"S-researcher8 ACT (2026-06-16)" for the exact fold-in TODO.
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
  -- ? bearer name: `Nat.Prime.factorization_factorial`
  --   `(n !).factorization p = ∑ i ∈ Finset.Ico 1 n, n / p ^ i`
  rw [hp.factorization_factorial]
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
  ----------------------------------------------------------------
  -- Step C:  ↥P cyclic of prime order ⇒ generator a; σ := ι a is a p-cycle.
  ----------------------------------------------------------------
  haveI hcyc : IsCyclic (P : Subgroup H) := isCyclic_of_prime_card hcardP   -- Nat.card form
  obtain ⟨a, ha⟩ := hcyc.exists_generator                                 -- ★ (∀ x, x ∈ zpowers a)
  -- orderOf a = p: ⟨a⟩ = ⊤, and |⟨a⟩| = orderOf a = |↥P| = p.
  have hgen_top : Subgroup.zpowers a = ⊤ := Subgroup.eq_top_iff'.mpr ha     -- ★
  have horda : orderOf a = p := by
    rw [← Nat.card_zpowers a, hgen_top, Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact hcardP
  have hords : orderOf (ι a) = p := by
    rw [orderOf_injective ι hι_inj a, horda]                             -- ★
  have hcycσ : (ι a).IsCycle := by
    have hsupp_lt : (ι a).support.card < 2 * orderOf (ι a) := by
      have hle : (ι a).support.card ≤ Fintype.card (ZMod p) :=
        Finset.card_le_univ _
      rw [ZMod.card] at hle; rw [hords]; omega
    exact Equiv.Perm.isCycle_of_prime_order (by rw [hords]; exact hp) hsupp_lt
  refine ⟨ι a, hcycσ, ?_, ?_⟩
  · -- support.card = orderOf = p
    rw [← hcycσ.orderOf, hords]                                          -- ★ IsCycle.orderOf
  · -- ι sends every element of P into ⟨σ⟩
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha g)                 -- ★ (a ^ k = g)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow ι a k, hk]⟩  -- ★

end AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep3
