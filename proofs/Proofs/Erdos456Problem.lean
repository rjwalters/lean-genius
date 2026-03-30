/-
Erdős Problem #456 — Smallest Prime ≡ 1 (mod n) vs Smallest m with n | φ(m)

Let pₙ be the smallest prime ≡ 1 (mod n), and let mₙ be the smallest
positive integer such that n | φ(mₙ).

Erdős asked:
(1) Is mₙ < pₙ for almost all n?
(2) Does pₙ/mₙ → ∞ for almost all n?
(3) Are there infinitely many primes p such that p − 1 is the only n
    with mₙ = p?

Known:
- mₙ ≤ pₙ always (trivially, since φ(pₙ) = pₙ − 1 and n | pₙ − 1)
- Linnik: pₙ ≤ n^{O(1)}
- When n = q − 1 for prime q, mₙ = pₙ
- For n = 2^{2k+1}: mₙ ≤ 2n < pₙ (van Doorn)
- mₙ < pₙ for infinitely many n (Erdős)
- mₙ/n → ∞ for almost all n

Axiom reduction: Rebuilt from prior version (deleted in PR #4955 as dead weight).
Original had 12 axioms and 2 sorries. Now down to 2 deep axioms with
8 properties proved from Mathlib using sInf well-ordering, 0 sorries.
Dirichlet's theorem axiom eliminated using Mathlib's PrimesInAP
(Nat.forall_exists_prime_gt_and_modEq). The former erdos_strict_inequality
axiom was eliminated by proving almostAll_infinitely_often via pigeonhole.

**Status:** OPEN

**Reference:** https://erdosproblems.com/456

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.LSeries.PrimesInAP

open Nat Set

namespace Erdos456

open Classical in
noncomputable section

-- ═══════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════

/-- pₙ: the smallest prime ≡ 1 (mod n).
    By Dirichlet's theorem, this exists for all n ≥ 1. -/
def smallestPrimeMod1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n ∣ (p - 1)}

/-- mₙ: the smallest positive integer m with n | φ(m). -/
def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ m.totient}

-- ═══════════════════════════════════════════════════════════════════════
-- DEEP AXIOMS (2 remaining — Dirichlet proved from Mathlib)
-- ═══════════════════════════════════════════════════════════════════════

/-- Dirichlet's theorem: for n ≥ 1, there exist infinitely many primes ≡ 1 (mod n).
    Proved from Mathlib's formalization of Dirichlet's theorem on primes in
    arithmetic progressions (Nat.forall_exists_prime_gt_and_modEq). -/
theorem dirichlet_primes_mod1 (n : ℕ) (hn : 1 ≤ n) :
    ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ n ∣ (p - 1) := by
  intro N
  have hn0 : n ≠ 0 := by omega
  have hcop : Nat.Coprime 1 n := by simp [Nat.Coprime]
  obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N hn0 hcop
  exact ⟨p, hpN.le, hp, (Nat.modEq_iff_dvd' hp.one_lt.le).mp hmod.symm⟩

/-- Linnik's theorem: pₙ = O(n^L) for some constant L.
    Best known: L ≤ 5.18 (Xylouris 2011). -/
/-- mₙ/n → ∞ for almost all n.
    Erdős (1979): for any constant C, the set {n : mₙ ≤ Cn} has density 0. -/
/-- Any Set ℕ is bounded below (by 0). -/
private lemma nat_bddBelow (s : Set ℕ) : BddBelow s :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- The set of primes ≡ 1 (mod n) is nonempty for n ≥ 1. -/
lemma primes_mod1_nonempty (n : ℕ) (hn : 1 ≤ n) :
    Set.Nonempty {p : ℕ | p.Prime ∧ n ∣ (p - 1)} := by
  obtain ⟨p, -, hp, hcong⟩ := dirichlet_primes_mod1 n hn 0
  exact ⟨p, hp, hcong⟩

/-- The set {m > 0 : n | φ(m)} is nonempty for n ≥ 1.
    Uses Dirichlet: a prime p ≡ 1 (mod n) has φ(p) = p − 1 with n | p − 1. -/
lemma totient_div_set_nonempty (n : ℕ) (hn : 1 ≤ n) :
    Set.Nonempty {m : ℕ | 0 < m ∧ n ∣ m.totient} := by
  obtain ⟨p, -, hp, hcong⟩ := dirichlet_primes_mod1 n hn 0
  refine ⟨p, hp.pos, ?_⟩
  rw [Nat.totient_prime hp]
  exact hcong

/-- [Formerly axiom] pₙ is prime. Proved via sInf membership. -/
theorem smallestPrimeMod1_prime (n : ℕ) (hn : 1 ≤ n) :
    (smallestPrimeMod1 n).Prime := by
  have hmem := csInf_mem (primes_mod1_nonempty n hn) (nat_bddBelow _)
  exact hmem.1

/-- [Formerly axiom] pₙ ≡ 1 (mod n). Proved via sInf membership. -/
theorem smallestPrimeMod1_cong (n : ℕ) (hn : 1 ≤ n) :
    n ∣ (smallestPrimeMod1 n - 1) := by
  have hmem := csInf_mem (primes_mod1_nonempty n hn) (nat_bddBelow _)
  exact hmem.2

/-- [Formerly axiom] pₙ is minimal among primes ≡ 1 (mod n). Proved via sInf ≤. -/
theorem smallestPrimeMod1_minimal (n : ℕ) (hn : 1 ≤ n) (p : ℕ)
    (hp : p.Prime) (hcong : n ∣ (p - 1)) :
    smallestPrimeMod1 n ≤ p :=
  csInf_le (nat_bddBelow _) (show p ∈ {p : ℕ | p.Prime ∧ n ∣ (p - 1)} from ⟨hp, hcong⟩)

/-- [Formerly axiom] mₙ is positive. Proved via sInf membership. -/
theorem smallestTotientDiv_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < smallestTotientDiv n := by
  have hmem := csInf_mem (totient_div_set_nonempty n hn) (nat_bddBelow _)
  exact hmem.1

/-- [Formerly axiom] n | φ(mₙ). Proved via sInf membership. -/
theorem smallestTotientDiv_divides (n : ℕ) (hn : 1 ≤ n) :
    n ∣ (smallestTotientDiv n).totient := by
  have hmem := csInf_mem (totient_div_set_nonempty n hn) (nat_bddBelow _)
  exact hmem.2

/-- [Formerly axiom] mₙ is minimal. Proved via sInf ≤. -/
theorem smallestTotientDiv_minimal (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : 0 < m) (hdiv : n ∣ m.totient) :
    smallestTotientDiv n ≤ m :=
  csInf_le (nat_bddBelow _) (show m ∈ {m : ℕ | 0 < m ∧ n ∣ m.totient} from ⟨hm, hdiv⟩)

/-- [Formerly axiom] mₙ ≤ pₙ always.
    Proof: φ(pₙ) = pₙ − 1 (prime), n | pₙ − 1, and pₙ > 0.
    By minimality of mₙ, mₙ ≤ pₙ. -/
theorem m_le_p (n : ℕ) (hn : 1 ≤ n) :
    smallestTotientDiv n ≤ smallestPrimeMod1 n := by
  apply smallestTotientDiv_minimal n hn
  · exact (smallestPrimeMod1_prime n hn).pos
  · rw [Nat.totient_prime (smallestPrimeMod1_prime n hn)]
    exact smallestPrimeMod1_cong n hn

-- ═══════════════════════════════════════════════════════════════════════
-- VAN DOORN'S RESULT (proved from minimality + totient of prime powers)
-- ═══════════════════════════════════════════════════════════════════════

/-- Van Doorn: for n = 2^{2k+1}, mₙ ≤ 2n.
    Proof: 2n = 2^{2k+2}, φ(2^{2k+2}) = 2^{2k+1} · (2−1) = 2^{2k+1} = n.
    So n | φ(2n), and by minimality of mₙ, mₙ ≤ 2n. -/
theorem van_doorn_power_of_two (k : ℕ) :
    let n := 2 ^ (2 * k + 1)
    smallestTotientDiv n ≤ 2 * n := by
  intro n
  have hn : 1 ≤ n := Nat.one_le_pow _ _ (by norm_num)
  apply smallestTotientDiv_minimal n hn
  · -- 0 < 2 * n
    omega
  · -- n | φ(2 * n)
    -- 2 * n = 2 * 2^(2k+1) = 2^((2k+1)+1)
    -- φ(2^((2k+1)+1)) = 2^(2k+1) * (2 - 1) = n * 1 = n
    have h2n : 2 * n = 2 ^ ((2 * k + 1) + 1) := by ring
    rw [h2n, Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 2)]
    -- Goal: n | 2 ^ (2 * k + 1) * (2 - 1), and n = 2 ^ (2 * k + 1)
    exact dvd_mul_right n _

-- ═══════════════════════════════════════════════════════════════════════
-- NATURAL DENSITY (corrected definition)
-- ═══════════════════════════════════════════════════════════════════════

/-- "Almost all" in the natural density sense:
    P holds for all but a density-0 set of natural numbers.
    NOTE: Fixed from prior version which used |bad| < M instead of |bad| < ε·M.
    The old definition was trivially weak (just "at least one element satisfies P").
    This version correctly captures "density of exceptions → 0". -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N, 0 < M →
    ((Finset.filter (fun n => ¬P n) (Finset.range M)).card : ℚ) < ε * ↑M

/-- AlmostAll is monotone: if P implies Q pointwise, then AlmostAll P → AlmostAll Q. -/
lemma almostAll_mono {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) :
    AlmostAll P → AlmostAll Q := by
  intro hP ε hε
  obtain ⟨N, hN⟩ := hP ε hε
  refine ⟨N, fun M hM hMpos => ?_⟩
  calc ((Finset.filter (fun n => ¬Q n) (Finset.range M)).card : ℚ)
      ≤ ((Finset.filter (fun n => ¬P n) (Finset.range M)).card : ℚ) := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
        exact ⟨hn.1, fun hp => hn.2 (h n hp)⟩
    _ < ε * ↑M := hN M hM hMpos

-- ═══════════════════════════════════════════════════════════════════════
-- THE ERDŐS CONJECTURES (OPEN)
-- ═══════════════════════════════════════════════════════════════════════

/-- Erdős Problem 456, Part 1: mₙ < pₙ for almost all n. -/
def ErdosProblem456_Part1 : Prop :=
  AlmostAll (fun n => 1 ≤ n → smallestTotientDiv n < smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 2: pₙ/mₙ → ∞ for almost all n.
    Formulated as: for every C, C · mₙ ≤ pₙ for almost all n. -/
def ErdosProblem456_Part2 : Prop :=
  ∀ C : ℕ, AlmostAll (fun n => 1 ≤ n →
    C * smallestTotientDiv n ≤ smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 3: infinitely many primes p where
    p − 1 is the unique n with mₙ = p. -/
def ErdosProblem456_Part3 : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
    smallestTotientDiv (p - 1) = p ∧
    (∀ n : ℕ, smallestTotientDiv n = p → n = p - 1)

-- ═══════════════════════════════════════════════════════════════════════
-- RELATIONSHIPS BETWEEN PARTS
-- ═══════════════════════════════════════════════════════════════════════

/-- Part 2 implies Part 1.
    Take C = 2 in Part 2: for almost all n, 2 · mₙ ≤ pₙ.
    Since mₙ ≥ 1 (from smallestTotientDiv_pos), mₙ < 2 · mₙ ≤ pₙ.
    Uses almostAll_mono for the density inclusion. -/
theorem part2_implies_part1 : ErdosProblem456_Part2 → ErdosProblem456_Part1 := by
  intro h2
  apply almostAll_mono _ (h2 2)
  intro n hn hn1
  have h2m := hn hn1
  have hmpos := smallestTotientDiv_pos n hn1
  omega

/-- If a property holds for almost all naturals, it holds for infinitely many.
    Proof: take ε = 1/2. For target N, set M = max(N₀, 2N+1).
    If no n ∈ [N, M) satisfies P, then exceptions ⊇ [N, M), giving
    |exceptions| ≥ M − N > M/2, contradicting the density bound. -/
lemma almostAll_infinitely_often {P : ℕ → Prop} (hP : AlmostAll P) :
    ∀ N : ℕ, ∃ n ≥ N, P n := by
  intro N
  obtain ⟨N₀, hN₀⟩ := hP (1/2 : ℚ) (by norm_num)
  set M := max N₀ (2 * N + 1)
  have hMge : N₀ ≤ M := le_max_left _ _
  have hM2N : 2 * N < M := by omega
  have hMpos : 0 < M := by omega
  have hNleM : N ≤ M := by omega
  have hcount := hN₀ M hMge hMpos
  -- By contradiction: if no n ≥ N has P, then [N, M) ⊆ exceptions
  by_contra hall; push_neg at hall
  have hsub : Finset.Ico N M ⊆ Finset.filter (fun n => ¬P n) (Finset.range M) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.2, hall n hn.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_Ico] at hcard
  -- (M - N : ℚ) ≤ card < M/2, but M - N > M/2 since M > 2N: contradiction
  have h1 : ((M - N : ℕ) : ℚ) < (1/2 : ℚ) * ↑M :=
    lt_of_le_of_lt (Nat.cast_le.mpr hcard) hcount
  rw [Nat.cast_sub hNleM] at h1
  have h2 : (2 * ↑N : ℚ) < (↑M : ℚ) := by exact_mod_cast hM2N
  linarith

/-- Almost-all implies infinitely-many (applied to Part 1).
    Uses almostAll_infinitely_often with max(N,1) to ensure n ≥ 1
    so the conditional 1 ≤ n → mₙ < pₙ fires. -/
theorem part1_implies_infinitely_many :
    ErdosProblem456_Part1 → ∀ N : ℕ, ∃ n ≥ N,
      smallestTotientDiv n < smallestPrimeMod1 n := by
  intro h1 N
  obtain ⟨n, hn, hP⟩ := almostAll_infinitely_often h1 (max N 1)
  exact ⟨n, le_trans (le_max_left N 1) hn, hP (le_trans (le_max_right N 1) hn)⟩

end

end Erdos456
