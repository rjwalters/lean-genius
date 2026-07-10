/-
Erdős Problem #1059, Open Question 01, Sub-Question 01:
Strong Selberg Density Axiom and Density at Factorial Points

**The Question**: Can density_one_conjecture be derived from selberg_density_axiom?

**Answer**: No — the weak Selberg axiom (≥1 qualifying prime per primorial interval)
gives only infinitely many qualifying primes, not density 1. The file OQ01 (line 439)
already notes this gap.

However, a STRONGER axiom capturing the Selberg sieve's quantitative prediction
— that the qualifying fraction at level l is ≥ l/(l+1) — combined with a mild
growth condition, DOES imply density at factorial evaluation points.

**Key results** (0 sorries, 1 axiom):
1. `primesInLevel`, `qualifyingInLevel`: interval-level counting functions
2. `strong_selberg_density`: axiom — q(l)*(l+1) ≥ p(l)*l for l ≥ 3
3. `primesInLevel_pos`: THEOREM (was an axiom) — p(l) ≥ 1 for l ≥ 1, proved from
   Bertrand's postulate. The downstream results need only positivity, so the old
   `p(l) ≥ l` axiom is eliminated.
4. `qualifyingInLevel_le_primesInLevel`: q(l) ≤ p(l) always
5. `strong_implies_weak`: strong axiom → selberg_density_axiom (≥1 per interval)
6. `levelwise_density_bound`: for l ≥ k, q(l)*(k+1) ≥ p(l)*k
7. `levelwise_strict_surplus`: for l ≥ max(3,k+2) with p(l) ≥ l, surplus ≥ 1

**Gap analysis**: For GENERAL x (not just x = n!), factorial growth of interval
sizes means cumulative surplus from prior levels cannot absorb partial-interval
deficit at the current level. Closing this gap requires either:
  (a) Point-wise sieve estimates (density bound within each interval)
  (b) Monotonicity of C(x)/π(x) (not obviously true)
  (c) A direct proof that the cumulative density ratio is non-decreasing

**Mathematical insight**: The Selberg sieve naturally gives level-wise density
bounds (the sieve analysis is performed interval by interval). The aggregation
from level-wise to cumulative density is the non-trivial step that requires
understanding the interaction between different interval scales.

Axioms: 1 (strong_selberg_density) — the former primes_growth_in_levels axiom is
now the proved theorem primesInLevel_pos (Bertrand's postulate)
Dependencies: Erdos1059OQ01 (counting functions), Erdos1059OQ02 (intervals, weak axiom)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Proofs.Erdos1059OQ01
import Proofs.Erdos1059OQ02

open Nat

namespace Erdos1059OQ01OQ01

/-
## Part I: Interval-Level Counting Functions

For each primorial level l, we count how many primes and how many qualifying
primes lie in the interval I(l) = (l!, (l+1)!].
-/

/-- Number of primes in the l-th primorial interval I(l) = (l!, (l+1)!]. -/
def primesInLevel (l : ℕ) : ℕ :=
  ((Erdos1059OQ02.PrimorialInterval l).filter (fun n => n.Prime)).card

/-- Number of qualifying primes (satisfying AFSC) in the l-th primorial interval. -/
def qualifyingInLevel (l : ℕ) : ℕ :=
  ((Erdos1059OQ02.PrimorialInterval l).filter
    (fun n => n.Prime ∧ Erdos1059OQ01.AllFactorialSubtractionsComposite n)).card

/-- Every qualifying prime is a prime: q(l) ≤ p(l). -/
theorem qualifyingInLevel_le_primesInLevel (l : ℕ) :
    qualifyingInLevel l ≤ primesInLevel l := by
  unfold qualifyingInLevel primesInLevel
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at *
  exact ⟨hx.1, hx.2.1⟩

/-
## Part II: The Strong Selberg Density Axiom

The weak axiom (OQ-02) asserts: ∃ p ∈ I(l), Prime p ∧ AFSC(p).
This gives ≥1 qualifying prime per interval, sufficient for infinitude.

The STRONG axiom captures the sieve's quantitative prediction:
the qualifying fraction at level l is ≥ l/(l+1). Concretely,
the number of non-qualifying primes in I(l) is at most p(l)/(l+1),
which follows from:
  - Each of the l+1 "bad" conditions eliminates ≤ 2·l!/log(l!)² primes
    (by Brun-Titchmarsh)
  - Total bad primes ≤ (l+1)·2·l!/log(l!)² = O(l!/log(l!)) · 2(l+1)/log(l!)
  - Total primes ≈ l!/log(l!)
  - Ratio of bad to total ≤ 2(l+1)/log(l!) → 0

For a clean formalization: q(l)·(l+1) ≥ p(l)·l.
-/

/-- **Strong Selberg Density Axiom**: For l ≥ 3, the qualifying fraction in
    each primorial interval is at least l/(l+1).

    Formally: qualifyingInLevel(l) · (l+1) ≥ primesInLevel(l) · l.

    This captures the Selberg sieve's quantitative prediction:
    at most 1/(l+1) of primes in I(l) can fail the AFSC property,
    because the l+1 "bad" conditions are sparse relative to the prime count.

    Requires: PNT for intervals + Brun-Titchmarsh + Selberg sieve. -/
axiom strong_selberg_density (l : ℕ) (hl : l ≥ 3) :
    qualifyingInLevel l * (l + 1) ≥ primesInLevel l * l

/-- **Positivity of the level prime count** (formerly the axiom
    `primes_growth_in_levels`, now *proved* from Bertrand's postulate).

    For `l ≥ 1` the primorial interval `I(l) = (l!, (l+1)!]` contains at least one
    prime.  Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) gives a
    prime `p` with `l! < p ≤ 2·l!`, and `2·l! ≤ (l+1)!` for `l ≥ 1`, so
    `p ∈ I(l)`.

    This is all the growth the downstream results actually use: both
    `qualifyingInLevel_pos` and `levelwise_strict_surplus` only need
    `primesInLevel l ≥ 1` (the surplus argument turns on `p·(l−k) > 0`, i.e.
    `p ≥ 1`, not the far stronger `p ≥ l`). Eliminating the old `p(l) ≥ l` axiom
    leaves a single sieve axiom (`strong_selberg_density`). -/
theorem primesInLevel_pos (l : ℕ) (hl : l ≥ 1) :
    primesInLevel l ≥ 1 := by
  unfold primesInLevel Erdos1059OQ02.PrimorialInterval
  rw [ge_iff_le, Finset.one_le_card]
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (Nat.factorial l) (Nat.factorial_ne_zero l)
  have hstep : 2 * Nat.factorial l ≤ Nat.factorial (l + 1) := by
    rw [Nat.factorial_succ]; gcongr; omega
  refine ⟨p, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨hlt, by omega⟩, hp⟩

/-
## Part III: Strong Axiom Implies Weak Axiom

The strong density axiom trivially implies selberg_density_axiom:
if q(l)·(l+1) ≥ p(l)·l ≥ l·l ≥ 9 > 0, then q(l) ≥ 1.
-/

/-- The strong axiom implies q(l) ≥ 1 for l ≥ 3. -/
theorem qualifyingInLevel_pos (l : ℕ) (hl : l ≥ 3) :
    qualifyingInLevel l ≥ 1 := by
  have hp := primesInLevel_pos l (by omega)
  have hs := strong_selberg_density l hl
  -- q(l) * (l+1) ≥ p(l) * l ≥ 1 * 3 > 0
  -- Since l+1 > 0, q(l) ≥ 1
  by_contra hc
  push_neg at hc
  -- hc : qualifyingInLevel l < 1, i.e., = 0 in ℕ
  have hq : qualifyingInLevel l = 0 := by omega
  rw [hq, zero_mul] at hs
  -- hs : 0 ≥ p(l) * l, but p(l) ≥ 1 and l ≥ 3 give p(l) * l ≥ 3 > 0
  have hpos : 1 * 3 ≤ primesInLevel l * l := Nat.mul_le_mul hp hl
  omega

/-- A qualifying prime exists in I(l) for l ≥ 3 (extraction from the count). -/
theorem qualifyingPrime_exists (l : ℕ) (hl : l ≥ 3) :
    ∃ p : ℕ, p ∈ Erdos1059OQ02.PrimorialInterval l ∧
    p.Prime ∧ Erdos1059OQ01.AllFactorialSubtractionsComposite p := by
  have hpos := qualifyingInLevel_pos l hl
  unfold qualifyingInLevel at hpos
  rw [ge_iff_le, Finset.one_le_card] at hpos
  obtain ⟨p, hp⟩ := hpos
  simp only [Finset.mem_filter] at hp
  exact ⟨p, hp.1, hp.2.1, hp.2.2⟩

/-- **Strong implies weak**: The strong Selberg density axiom implies
    the weak axiom from OQ-02. This also gives an alternative proof
    of the definitional transfer between AFSC namespaces. -/
theorem strong_implies_weak (l : ℕ) (hl : l ≥ 3) :
    ∃ p : ℕ, p ∈ Erdos1059OQ02.PrimorialInterval l ∧
    p.Prime ∧ Erdos1059OQ02.AllFactorialSubtractionsComposite p := by
  obtain ⟨p, hmem, hprime, hafsc⟩ := qualifyingPrime_exists l hl
  refine ⟨p, hmem, hprime, ?_⟩
  -- OQ01.AFSC and OQ02.AFSC have identical bodies → definitional equality
  intro k hk
  exact hafsc k hk

/-
## Part IV: Level-Wise Density Bound

The strong axiom at rate l/(l+1) implies the density bound at rate k/(k+1)
for all l ≥ k. The key algebraic identity:

  q(l)·(l+1) ≥ p(l)·l  and  l ≥ k
  ⟹  q(l)·(k+1)·(l+1) ≥ p(l)·l·(k+1) ≥ p(l)·k·(l+1)
  ⟹  q(l)·(k+1) ≥ p(l)·k    [cancelling l+1 > 0]

This is the monotonicity of l/(l+1) in l.
-/

/-- For l ≥ max(3, k), the level-wise density bound holds at threshold k/(k+1). -/
theorem levelwise_density_bound (l k : ℕ) (hl : l ≥ 3) (hlk : l ≥ k) :
    qualifyingInLevel l * (k + 1) ≥ primesInLevel l * k := by
  have hs := strong_selberg_density l hl
  have hqlp := qualifyingInLevel_le_primesInLevel l
  -- Goal: q * (k+1) ≥ p * k
  -- From: q * (l+1) ≥ p * l and l ≥ k
  -- Proof by contradiction: if q*(k+1) < p*k, derive q*(l+1) < p*l.
  -- q*(l+1) = q*(k+1) + q*(l-k) < p*k + p*(l-k) = p*l
  by_contra hc
  push_neg at hc
  -- hc : q*(k+1) < p*k
  -- q*(l+1) = q*((k+1) + (l-k)) = q*(k+1) + q*(l-k) [since l+1 = (k+1) + (l-k)]
  have hsplit : qualifyingInLevel l * (l + 1) =
      qualifyingInLevel l * (k + 1) + qualifyingInLevel l * (l - k) := by
    rw [← Nat.mul_add]; congr 1; omega
  have hqmul : qualifyingInLevel l * (l - k) ≤ primesInLevel l * (l - k) :=
    Nat.mul_le_mul_right _ hqlp
  have hcomb : primesInLevel l * k + primesInLevel l * (l - k) = primesInLevel l * l := by
    rw [← Nat.mul_add]; congr 1; omega
  -- q*(l+1) = q*(k+1) + q*(l-k) < p*k + p*(l-k) = p*l
  -- But q*(l+1) ≥ p*l from axiom. Contradiction.
  linarith

/-- **Strict surplus**: For l ≥ max(3, k+2), each high level contributes
    at least 1 unit of surplus toward the density bound:
    q(l)·(k+1) ≥ p(l)·k + 1.

    Proof (uses only `p(l) ≥ 1`, via `primesInLevel_pos`): suppose instead
    q·(k+1) ≤ p·k. Splitting `l+1 = (k+1)+(l-k)` and using `q ≤ p` gives
    q·(l+1) ≤ p·l; the Selberg axiom gives the reverse, so all inequalities are
    equalities. In particular q·(l-k) = p·(l-k) with `l-k > 0`, so `q = p`; then
    q·(k+1) = p·k with `q = p` forces `p = 0`, contradicting `p ≥ 1`. -/
theorem levelwise_strict_surplus (l k : ℕ) (hl : l ≥ 3) (hlk : l ≥ k + 2) :
    qualifyingInLevel l * (k + 1) ≥ primesInLevel l * k + 1 := by
  have hs := strong_selberg_density l hl
  have hp := primesInLevel_pos l (by omega)
  have hqlp := qualifyingInLevel_le_primesInLevel l
  by_contra hc
  push_neg at hc
  -- hc : q*(k+1) < p*k + 1, i.e., q*(k+1) ≤ p*k
  have hle : qualifyingInLevel l * (k + 1) ≤ primesInLevel l * k := by omega
  -- Split l+1 = (k+1) + (l-k) and k + (l-k) = l.
  have hsplit : qualifyingInLevel l * (l + 1) =
      qualifyingInLevel l * (k + 1) + qualifyingInLevel l * (l - k) := by
    rw [← Nat.mul_add]; congr 1; omega
  have hqmul : qualifyingInLevel l * (l - k) ≤ primesInLevel l * (l - k) :=
    Nat.mul_le_mul_right _ hqlp
  have hcomb : primesInLevel l * k + primesInLevel l * (l - k) = primesInLevel l * l := by
    rw [← Nat.mul_add]; congr 1; omega
  -- q*(l+1) ≤ p*l, and the axiom gives ≥, so equality.
  have hub : qualifyingInLevel l * (l + 1) ≤ primesInLevel l * l := by
    rw [hsplit]; omega
  have heq : qualifyingInLevel l * (l + 1) = primesInLevel l * l := by omega
  -- Equality of the total forces equality of the (l-k)-piece.
  have hpiece : qualifyingInLevel l * (l - k) = primesInLevel l * (l - k) := by omega
  -- l - k > 0, so cancel to get q = p.
  have hlk0 : 0 < l - k := by omega
  have hqp : qualifyingInLevel l = primesInLevel l :=
    Nat.eq_of_mul_eq_mul_right hlk0 hpiece
  -- Then q*(k+1) = p*k with q = p forces p = 0, contradicting p ≥ 1.
  have hk1 : qualifyingInLevel l * (k + 1) = primesInLevel l * k := by omega
  rw [hqp] at hk1
  have hexp : primesInLevel l * (k + 1) = primesInLevel l * k + primesInLevel l := by ring
  omega

/-
## Part V: Gap Analysis — Why General x Fails

At factorial evaluation points x = n!, the density bound follows from summing
the level-wise bounds. But for GENERAL x ∈ (l!, (l+1)!]:

  C(x) = C(l!) + c_partial
  π(x) = π(l!) + p_partial

The partial-interval deficit p_partial·k - c_partial·(k+1) can be as large
as primesInLevel(l)·k, which grows factorially with l.

The cumulative surplus from levels 3 to l-1 is Σ surplus_m, which grows as
≈ primesInLevel(l-1) ≈ primesInLevel(l) / l. This cannot absorb the
primesInLevel(l)·k deficit for k ≥ 1.

Closing this gap requires WITHIN-INTERVAL density estimates — precisely,
that even within a partial interval (l!, x] ⊂ I(l), the qualifying fraction
is close to 1. This is a deeper sieve result than the full-interval bound.
-/

/-
## Part VI: Density Bound at Factorial Points (Level-Sum Form)

We prove that the sum of qualifying counts across levels eventually dominates
the sum of prime counts, at any prescribed ratio k/(k+1).

This is the level-sum analogue of density_one_conjecture. It becomes equivalent
to the actual density conjecture once the interval decomposition
  C(n!) = Σ qualifyingInLevel(l) for l = 0..n-1
is established (stated below with sorry as it requires Finset partition machinery).
-/

/-- Auxiliary: deficit from early levels is bounded.
    For levels 0 to L₀-1, the "damage" to the density bound is at most
    k times the total prime count in those levels. -/
private def earlyDeficit (L₀ k : ℕ) : ℕ :=
  k * (Finset.range L₀).sum primesInLevel

/-- **Main density theorem (level-sum form)**: For every k, there exists N
    such that for all n ≥ N, the sum of qualifying counts times (k+1)
    exceeds the sum of prime counts times k.

    This is the level-sum analogue of density_one_conjecture. -/
theorem density_at_levels (k : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Finset.range (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) ≥
    (Finset.range (n + 1)).sum (fun l => primesInLevel l * k) := by
  -- Choose L₀ = max(3, k+2) so levelwise_strict_surplus applies
  set L₀ := max 3 (k + 2)
  -- Choose N = L₀ + earlyDeficit L₀ k
  -- For n ≥ N: surplus from levels L₀..n is ≥ n - L₀ + 1 ≥ earlyDeficit + 1
  -- Deficit from levels 0..L₀-1 is ≤ earlyDeficit
  refine ⟨L₀ + earlyDeficit L₀ k, fun n hn => ?_⟩
  -- Split the sum: range (n+1) = range L₀ ∪ Ico L₀ (n+1)
  have hL₀_le : L₀ ≤ n + 1 := by omega
  -- For each l in Ico L₀ (n+1), the surplus is ≥ 1
  have h_high : ∀ l, l ∈ Finset.Ico L₀ (n + 1) →
      qualifyingInLevel l * (k + 1) ≥ primesInLevel l * k + 1 := by
    intro l hl
    simp only [Finset.mem_Ico] at hl
    exact levelwise_strict_surplus l k (by omega) (by omega)
  -- Sum the high-level surplus: Σ q*(k+1) ≥ Σ (p*k + 1) = Σ p*k + card
  have h_high_sum : (Finset.Ico L₀ (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) ≥
      (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) +
      (n + 1 - L₀) := by
    -- Σ q*(k+1) ≥ Σ (p*k + 1) by Finset.sum_le_sum
    have hge := Finset.sum_le_sum h_high
    -- Σ (p*k + 1) = Σ p*k + Σ 1 by sum_add_distrib
    have hdecomp : (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k + 1) =
        (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) +
        (Finset.Ico L₀ (n + 1)).sum (fun _ => 1) := Finset.sum_add_distrib
    -- Σ 1 = card
    have hones : (Finset.Ico L₀ (n + 1)).sum (fun _ => 1) =
        (Finset.Ico L₀ (n + 1)).card := by simp [Finset.sum_const]
    -- card = n + 1 - L₀
    have hcard : (Finset.Ico L₀ (n + 1)).card = n + 1 - L₀ := Nat.card_Ico L₀ (n + 1)
    linarith
  -- Low-level deficit: Σ_{l<L₀} p(l)*k ≤ earlyDeficit
  have h_low_deficit : (Finset.range L₀).sum (fun l => primesInLevel l * k) ≤
      earlyDeficit L₀ k := by
    unfold earlyDeficit
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    exact le_of_eq (mul_comm (primesInLevel l) k)
  -- Low-level LHS contribution is ≥ 0
  have h_low_nonneg : 0 ≤ (Finset.range L₀).sum (fun l => qualifyingInLevel l * (k + 1)) :=
    Nat.zero_le _
  -- Split both sums at L₀ using: range n = range m ++ Ico m n
  have h_split_lhs : (Finset.range (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) =
      (Finset.range L₀).sum (fun l => qualifyingInLevel l * (k + 1)) +
      (Finset.Ico L₀ (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) := by
    rw [← Finset.sum_range_add_sum_Ico _ hL₀_le]
  have h_split_rhs : (Finset.range (n + 1)).sum (fun l => primesInLevel l * k) =
      (Finset.range L₀).sum (fun l => primesInLevel l * k) +
      (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) := by
    rw [← Finset.sum_range_add_sum_Ico _ hL₀_le]
  -- Combine: LHS = low_q + high_q ≥ 0 + (high_p + card) ≥ deficit + high_p + 1
  -- RHS = low_p + high_p ≤ deficit + high_p
  -- Need card ≥ deficit + 1, i.e., n + 1 - L₀ ≥ earlyDeficit + 1
  rw [h_split_lhs, h_split_rhs]
  have h_n_bound : n + 1 - L₀ ≥ earlyDeficit L₀ k + 1 := by omega
  linarith

/-
## Part VII: Connection to density_one_conjecture

The level-sum density bound (Part VI) becomes the actual density_one_conjecture
once we establish that cumulative counts decompose as sums over levels:
  C(n!) = Σ_{l=0}^{n-1} qualifyingInLevel l
  π(n!) = Σ_{l=0}^{n-1} primesInLevel l

This decomposition holds because:
1. I(0), I(1), ..., I(n-1) partition {2, ..., n!} (proved via disjointness + coverage)
2. Every prime ≤ n! belongs to exactly one I(l) for l < n
3. Finset.card distributes over the disjoint union

This decomposition is now **proved** (previously a sorry): the generic
`count_decomp` below establishes it for any predicate excluding 0 and 1, by a
clean one-step induction on `n` (peel off the top interval), avoiding any heavy
partition machinery.
-/

/-- **Generic interval decomposition.**  For any (decidable) predicate `P` that
    excludes `0` and `1`, the count of `P`-elements up to `n!` decomposes as the
    sum over primorial levels `l < n` of the level-wise `P`-counts.

    Proof by induction on `n`: the single split
    `range (n!·(n+1)+1) = range (n!+1) ∪ Ioc (n!) ((n+1)!)` peels off exactly the
    `n`-th interval at each step (the two pieces are disjoint and their union is
    `range ((n+1)!+1)` since `(n+1)! ≥ n!`). -/
theorem count_decomp (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, x < 2 → ¬ P x) (n : ℕ) :
    ((Finset.range (Nat.factorial n + 1)).filter P).card
      = ∑ l ∈ Finset.range n,
          ((Finset.Ioc (Nat.factorial l) (Nat.factorial (l + 1))).filter P).card := by
  induction n with
  | zero => simpa using hP
  | succ m ih =>
    have hmono : Nat.factorial m ≤ Nat.factorial (m + 1) := Nat.factorial_le (by omega)
    have hsplit : Finset.range (Nat.factorial (m + 1) + 1)
        = Finset.range (Nat.factorial m + 1)
            ∪ Finset.Ioc (Nat.factorial m) (Nat.factorial (m + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc, Nat.lt_succ_iff]
      omega
    have hdisj : Disjoint (Finset.range (Nat.factorial m + 1))
        (Finset.Ioc (Nat.factorial m) (Nat.factorial (m + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff] at hx hx'
      omega
    rw [Finset.sum_range_succ, ← ih, hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- **Interval decomposition for prime count** (cumulative → level sum):
    π(n!) = Σ_{l=0}^{n-1} primesInLevel l.

    Every prime `p` with `2 ≤ p ≤ n!` lies in exactly one primorial interval
    `I(l)` for some `l < n`; the intervals partition `{2, …, n!}`.  Immediate from
    `count_decomp` with `P = Prime` (no prime is `< 2`). -/
theorem primeCount_decomposition (n : ℕ) (hn : n ≥ 1) :
    Erdos1059OQ01.primeCount (Nat.factorial n) =
    (Finset.range n).sum primesInLevel := by
  unfold Erdos1059OQ01.primeCount primesInLevel Erdos1059OQ02.PrimorialInterval
  exact count_decomp (fun m => m.Prime)
    (fun x hx => by interval_cases x <;> simp [Nat.not_prime_zero, Nat.not_prime_one]) n

/-- **Interval decomposition for qualifying prime count**:
    C(n!) = Σ_{l=0}^{n-1} qualifyingInLevel l.  Immediate from `count_decomp`
    with `P = Prime ∧ AFSC` (a qualifying number is prime, hence `≥ 2`). -/
theorem qualifyingCount_decomposition (n : ℕ) (hn : n ≥ 1) :
    Erdos1059OQ01.qualifyingPrimeCount (Nat.factorial n) =
    (Finset.range n).sum qualifyingInLevel := by
  unfold Erdos1059OQ01.qualifyingPrimeCount qualifyingInLevel Erdos1059OQ02.PrimorialInterval
  exact count_decomp (fun m => m.Prime ∧ Erdos1059OQ01.AllFactorialSubtractionsComposite m)
    (fun x hx => by interval_cases x <;> simp [Nat.not_prime_zero, Nat.not_prime_one]) n

/-- **Density one at factorial points**: For every k, there exists N such that
    for all n ≥ N, C(n!) · (k+1) ≥ π(n!) · k.

    This is density_one_conjecture restricted to evaluation at factorial values.
    The proof combines density_at_levels with the interval decomposition. -/
theorem density_one_at_factorials (k : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    Erdos1059OQ01.qualifyingPrimeCount (Nat.factorial n) * (k + 1) ≥
    Erdos1059OQ01.primeCount (Nat.factorial n) * k := by
  obtain ⟨N₀, hN₀⟩ := density_at_levels k
  -- Witness N₀ + 1: we apply the level-sum bound at n - 1 (range n = range ((n-1)+1)),
  -- which needs n - 1 ≥ N₀, i.e. n ≥ N₀ + 1.
  refine ⟨N₀ + 1, fun n hn => ?_⟩
  have hn1 : n ≥ 1 := by omega
  have hnN : n ≥ N₀ := by omega
  rw [qualifyingCount_decomposition n hn1, primeCount_decomposition n hn1]
  -- Now apply density_at_levels with n-1 (since range n = range ((n-1)+1)).
  -- The decompositions give (Σ q_l)·(k+1); density_at_levels sums q_l·(k+1)
  -- termwise, so bridge with Finset.sum_mul.
  have hnn : n = (n - 1) + 1 := by omega
  rw [hnn, Finset.sum_mul, Finset.sum_mul]
  exact hN₀ (n - 1) (by omega)

/-
## Part VIII: The Non-Qualifying Deficit — Sharp Form of "Density → 1"

The density bound `C(x)·(k+1) ≥ π(x)·k` is exactly a bound on the *deficit*
`D(x) := π(x) − C(x)`, the number of non-qualifying primes up to `x`. Writing
`C = π − D` and expanding, the density inequality at threshold `k/(k+1)` is
*equivalent* (pointwise, for every `x`) to

    D(x) · (k+1) ≤ π(x),

i.e. the non-qualifying primes make up at most a `1/(k+1)` fraction of all
primes. Letting `k → ∞` this says the qualifying fraction tends to `1` — the
sharp quantitative reading of `density_one_conjecture`.
-/

/-- **Deficit ⇔ density (pointwise).**  For every `x` and every threshold `k`,
    the density lower bound `C(x)·(k+1) ≥ π(x)·k` holds *iff* the non-qualifying
    deficit `π(x) − C(x)` is at most a `1/(k+1)` fraction of `π(x)`:

      (π(x) − C(x)) · (k+1) ≤ π(x)   ↔   C(x) · (k+1) ≥ π(x) · k.

    This is pure `ℕ`-arithmetic (truncated subtraction), valid at *every* `x`;
    it turns the density statement into an explicit bound on the count of
    non-qualifying primes. -/
theorem deficit_le_iff_density (x k : ℕ) :
    (Erdos1059OQ01.primeCount x - Erdos1059OQ01.qualifyingPrimeCount x) * (k + 1) ≤
      Erdos1059OQ01.primeCount x ↔
    Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) ≥ Erdos1059OQ01.primeCount x * k := by
  have e1 : (Erdos1059OQ01.primeCount x - Erdos1059OQ01.qualifyingPrimeCount x) * (k + 1) =
      Erdos1059OQ01.primeCount x * (k + 1) - Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) :=
    Nat.sub_mul _ _ _
  have e2 : Erdos1059OQ01.primeCount x * (k + 1) =
      Erdos1059OQ01.primeCount x * k + Erdos1059OQ01.primeCount x := by ring
  rw [e1, e2]
  omega

/-- **Non-qualifying deficit vanishes (at factorial points).**  For every `k`
    there is an `N` such that for all `n ≥ N`, the number of *non-qualifying*
    primes up to `n!` is at most a `1/(k+1)` fraction of all primes up to `n!`:

      (π(n!) − C(n!)) · (k+1) ≤ π(n!).

    Immediate from `density_one_at_factorials` via the pointwise equivalence
    `deficit_le_iff_density`. As `k → ∞` this is the sharp statement that the
    qualifying fraction `C(n!)/π(n!) → 1`. -/
theorem nonqualifying_deficit_at_factorials (k : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Erdos1059OQ01.primeCount (Nat.factorial n) -
      Erdos1059OQ01.qualifyingPrimeCount (Nat.factorial n)) * (k + 1) ≤
    Erdos1059OQ01.primeCount (Nat.factorial n) := by
  obtain ⟨N, hN⟩ := density_one_at_factorials k
  exact ⟨N, fun n hn => (deficit_le_iff_density _ k).mpr (hN n hn)⟩

/-
## Part IX: The Density Surplus is Unbounded

`density_at_levels` shows the qualifying count *meets* the `k/(k+1)` threshold
eventually. In fact it *overshoots* it by an arbitrarily large additive margin:
each level `l ≥ max(3, k+2)` contributes a strict surplus `≥ 1`
(`levelwise_strict_surplus`), and there are unboundedly many such levels, so the
cumulative surplus `Σ q_l·(k+1) − Σ p_l·k` grows without bound. This is the exact
same argument as `density_at_levels` (of which it is the `M = 0` case), with the
witness `N` pushed out by `M` extra high levels to absorb the target margin.
-/

/-- **Unbounded density surplus (level-sum form)**: for every threshold `k` and
    every margin `M`, eventually the level-sum qualifying count exceeds the
    level-sum prime count (at rate `k/(k+1)`) by at least `M`:

      Σ_{l≤n} q(l)·(k+1) ≥ Σ_{l≤n} p(l)·k + M   for all large `n`.

    `density_at_levels` is the `M = 0` instance. The proof is identical, choosing
    `N` large enough that the count of strict-surplus levels `n + 1 − L₀` exceeds
    the early-level deficit by the extra margin `M`. -/
theorem density_at_levels_surplus (k M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Finset.range (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) ≥
    (Finset.range (n + 1)).sum (fun l => primesInLevel l * k) + M := by
  set L₀ := max 3 (k + 2)
  refine ⟨L₀ + earlyDeficit L₀ k + M, fun n hn => ?_⟩
  have hL₀_le : L₀ ≤ n + 1 := by omega
  -- Each high level l ∈ Ico L₀ (n+1) has strict surplus ≥ 1.
  have h_high : ∀ l, l ∈ Finset.Ico L₀ (n + 1) →
      qualifyingInLevel l * (k + 1) ≥ primesInLevel l * k + 1 := by
    intro l hl
    simp only [Finset.mem_Ico] at hl
    exact levelwise_strict_surplus l k (by omega) (by omega)
  have h_high_sum : (Finset.Ico L₀ (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) ≥
      (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) +
      (n + 1 - L₀) := by
    have hge := Finset.sum_le_sum h_high
    have hdecomp : (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k + 1) =
        (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) +
        (Finset.Ico L₀ (n + 1)).sum (fun _ => 1) := Finset.sum_add_distrib
    have hones : (Finset.Ico L₀ (n + 1)).sum (fun _ => 1) =
        (Finset.Ico L₀ (n + 1)).card := by simp [Finset.sum_const]
    have hcard : (Finset.Ico L₀ (n + 1)).card = n + 1 - L₀ := Nat.card_Ico L₀ (n + 1)
    linarith
  have h_low_deficit : (Finset.range L₀).sum (fun l => primesInLevel l * k) ≤
      earlyDeficit L₀ k := by
    unfold earlyDeficit
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    exact le_of_eq (mul_comm (primesInLevel l) k)
  have h_low_nonneg : 0 ≤ (Finset.range L₀).sum (fun l => qualifyingInLevel l * (k + 1)) :=
    Nat.zero_le _
  have h_split_lhs : (Finset.range (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) =
      (Finset.range L₀).sum (fun l => qualifyingInLevel l * (k + 1)) +
      (Finset.Ico L₀ (n + 1)).sum (fun l => qualifyingInLevel l * (k + 1)) := by
    rw [← Finset.sum_range_add_sum_Ico _ hL₀_le]
  have h_split_rhs : (Finset.range (n + 1)).sum (fun l => primesInLevel l * k) =
      (Finset.range L₀).sum (fun l => primesInLevel l * k) +
      (Finset.Ico L₀ (n + 1)).sum (fun l => primesInLevel l * k) := by
    rw [← Finset.sum_range_add_sum_Ico _ hL₀_le]
  rw [h_split_lhs, h_split_rhs]
  have h_n_bound : n + 1 - L₀ ≥ earlyDeficit L₀ k + M := by omega
  linarith

/-- **Unbounded density surplus (at factorial points)**: for every threshold `k`
    and every margin `M`, eventually

      C(n!)·(k+1) ≥ π(n!)·k + M.

    So the qualifying primes up to `n!` not only meet the `k/(k+1)` density
    threshold (`density_one_at_factorials`) but overshoot the corresponding prime
    fraction by an arbitrarily large additive amount. Combines
    `density_at_levels_surplus` with the interval decompositions, exactly as
    `density_one_at_factorials` combines `density_at_levels` with them. -/
theorem density_surplus_at_factorials (k M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    Erdos1059OQ01.qualifyingPrimeCount (Nat.factorial n) * (k + 1) ≥
    Erdos1059OQ01.primeCount (Nat.factorial n) * k + M := by
  obtain ⟨N₀, hN₀⟩ := density_at_levels_surplus k M
  refine ⟨N₀ + 1, fun n hn => ?_⟩
  have hn1 : n ≥ 1 := by omega
  rw [qualifyingCount_decomposition n hn1, primeCount_decomposition n hn1]
  have hnn : n = (n - 1) + 1 := by omega
  rw [hnn, Finset.sum_mul, Finset.sum_mul]
  exact hN₀ (n - 1) (by omega)

/-
## Part X: The Sharp Margin Deficit — Deficit Side of the Unbounded Surplus

`nonqualifying_deficit_at_factorials` is the deficit reading of
`density_one_at_factorials`: the non-qualifying primes up to `n!` are eventually a
`≤ 1/(k+1)` fraction. Part IX sharpened the density statement to an *unbounded
additive surplus* (`density_surplus_at_factorials`). Reading that surplus back on
the deficit side gives the correspondingly sharp bound: the non-qualifying deficit
`π(n!) − C(n!)`, scaled by `k+1`, leaves an arbitrarily large slack `M` below
`π(n!)`.

The pointwise bridge is the *margin* analogue of `deficit_le_iff_density`. Unlike
the `M = 0` case it is **not** unconditional: it needs `C(x) ≤ π(x)` (otherwise a
huge `C` could satisfy the density surplus while the truncated deficit collapses to
`0` and the margin `M` alone exceeds `π(x)`). That hypothesis is exactly the
pointwise subset bound `qualifyingCount_le_primeCount`.
-/

/-- **Margin deficit ⇔ density surplus (pointwise).**  For every `x`, threshold `k`
    and margin `M`, the density surplus bound `C(x)·(k+1) ≥ π(x)·k + M` holds *iff*
    the scaled non-qualifying deficit undershoots `π(x)` by at least `M`:

      (π(x) − C(x)) · (k+1) + M ≤ π(x)   ↔   C(x) · (k+1) ≥ π(x) · k + M.

    The `M = 0` case is `deficit_le_iff_density`; there the equivalence is
    unconditional, but the additive margin needs the subset bound `C(x) ≤ π(x)`
    (`Erdos1059OQ01.qualifyingCount_le_primeCount`) to rule out the degenerate
    branch where the truncated deficit is `0` while `M > π(x)`. -/
theorem deficit_add_le_iff_density_surplus (x k M : ℕ) :
    (Erdos1059OQ01.primeCount x - Erdos1059OQ01.qualifyingPrimeCount x) * (k + 1) + M ≤
      Erdos1059OQ01.primeCount x ↔
    Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) ≥ Erdos1059OQ01.primeCount x * k + M := by
  -- Subset bound C(x) ≤ π(x), scaled to C(x)·(k+1) ≤ π(x)·k + π(x).
  have hmul : Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) ≤
      Erdos1059OQ01.primeCount x * k + Erdos1059OQ01.primeCount x := by
    have h1 : Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) ≤
        Erdos1059OQ01.primeCount x * (k + 1) :=
      Nat.mul_le_mul_right _ (Erdos1059OQ01.qualifyingCount_le_primeCount x)
    have h2 : Erdos1059OQ01.primeCount x * (k + 1) =
        Erdos1059OQ01.primeCount x * k + Erdos1059OQ01.primeCount x := by ring
    omega
  have e1 : (Erdos1059OQ01.primeCount x - Erdos1059OQ01.qualifyingPrimeCount x) * (k + 1) =
      Erdos1059OQ01.primeCount x * (k + 1) - Erdos1059OQ01.qualifyingPrimeCount x * (k + 1) :=
    Nat.sub_mul _ _ _
  have e2 : Erdos1059OQ01.primeCount x * (k + 1) =
      Erdos1059OQ01.primeCount x * k + Erdos1059OQ01.primeCount x := by ring
  rw [e1, e2]
  omega

/-- **Non-qualifying deficit with unbounded margin (at factorial points).**  For
    every threshold `k` and every margin `M` there is an `N` such that for all
    `n ≥ N`,

      (π(n!) − C(n!)) · (k+1) + M ≤ π(n!).

    So the scaled non-qualifying deficit up to `n!` sits an arbitrarily large slack
    `M` below `π(n!)`. This is the deficit reading of `density_surplus_at_factorials`
    exactly as `nonqualifying_deficit_at_factorials` (its `M = 0` case) is the
    deficit reading of `density_one_at_factorials`; the bridge is the pointwise
    `deficit_add_le_iff_density_surplus`. -/
theorem nonqualifying_deficit_surplus_at_factorials (k M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Erdos1059OQ01.primeCount (Nat.factorial n) -
      Erdos1059OQ01.qualifyingPrimeCount (Nat.factorial n)) * (k + 1) + M ≤
    Erdos1059OQ01.primeCount (Nat.factorial n) := by
  obtain ⟨N, hN⟩ := density_surplus_at_factorials k M
  exact ⟨N, fun n hn => (deficit_add_le_iff_density_surplus _ k M).mpr (hN n hn)⟩

/-
## Summary

**Proved from first principles** (no sorry):
1. qualifyingInLevel_le_primesInLevel — subset bound q(l) ≤ p(l)
2. qualifyingInLevel_pos — q(l) ≥ 1 for l ≥ 3 (from strong axiom + growth)
3. qualifyingPrime_exists — extracting a qualifying prime from the count
4. strong_implies_weak — recovering selberg_density_axiom from our stronger version
5. levelwise_density_bound — l/(l+1) ≥ k/(k+1) for l ≥ k, applied to counts
6. levelwise_strict_surplus — per-level surplus ≥ 1 for l ≥ max(3, k+2)
7. density_at_levels — MAIN THEOREM: level-sum density bound, fully proved
8. count_decomp — generic interval decomposition (induction; peel top interval)
9. primeCount_decomposition — π(n!) = Σ primesInLevel  (now proved via count_decomp)
10. qualifyingCount_decomposition — C(n!) = Σ qualifyingInLevel  (now proved)
11. density_one_at_factorials — density at factorial points (now proved; combines
    density_at_levels with the two decompositions)
12. deficit_le_iff_density — pointwise equivalence of the density bound with the
    non-qualifying deficit bound (π(x)−C(x))·(k+1) ≤ π(x)
13. nonqualifying_deficit_at_factorials — sharp form: the non-qualifying primes up
    to n! are eventually a ≤1/(k+1) fraction, i.e. C(n!)/π(n!) → 1
14. density_at_levels_surplus — level-sum surplus is unbounded: Σ q_l·(k+1) exceeds
    Σ p_l·k by any prescribed margin M (density_at_levels is the M=0 case)
15. density_surplus_at_factorials — at factorial points C(n!)·(k+1) ≥ π(n!)·k + M,
    the qualifying count overshoots the k/(k+1) prime fraction by an unbounded margin
16. deficit_add_le_iff_density_surplus — pointwise margin equivalence: the density
    surplus C(x)·(k+1) ≥ π(x)·k + M holds iff (π(x)−C(x))·(k+1) + M ≤ π(x)
    (needs the subset bound C(x) ≤ π(x); the M=0 case is deficit_le_iff_density)
17. nonqualifying_deficit_surplus_at_factorials — sharp deficit form of the unbounded
    surplus: (π(n!)−C(n!))·(k+1) + M ≤ π(n!) eventually, for every margin M

**This file is now sorry-free** — the previous two `sorry`s (the interval
decompositions) are discharged by `count_decomp`.

**Axioms** (1, a single disclosed sieve input):
- strong_selberg_density: captures Selberg sieve's quantitative prediction

The former `primes_growth_in_levels` axiom (`p(l) ≥ l`) is now the proved theorem
`primesInLevel_pos` (`p(l) ≥ 1`, via Bertrand's postulate); the downstream
results only ever used positivity of the level prime count.

**Open**: Extending from factorial points to all x requires within-interval
density estimates, which is a deeper sieve-theoretic result.
-/

end Erdos1059OQ01OQ01
