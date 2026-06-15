/-
  Extremal characterization for Erdős #1179 oq-02 (power-of-two groups).
  Date: 2026-06-15 (S5)
  Research: erdos-1179-oq-02 (researcher-4)

  Companion to:
    * `Erdos1179OQ02.lean`       — lower bound  g_ε(N) ≥ log₂N
      (`clog_le_card_of_epsUniform`, per-subset, hypothesis-free), and
    * `Erdos1179OQ02Upper.lean`  — a unique-representation set is exactly
      `0`-uniform of size `⌈log₂N⌉` (`epsUniform_zero_of_unique_repr`,
      `unique_repr_card_eq_clog`).

  Those two files give BOTH the lower bound and the forward direction
  "unique representations ⟹ minimal 0-uniform set" on the
  unique-representation family.  This file supplies the **converse**, i.e. the
  extremal-rigidity statement:

      if `A` is `0`-uniform AND already meets the lower bound
      `|A| = ⌈log₂N⌉`, then every group element has a UNIQUE subset-sum
      representation (`reprCount A g = 1` for all `g`).

  Mathematical content.  `0`-uniformity forces every count to equal the
  expected count `μ = 2^|A| / N` exactly, hence all counts are equal to a single
  natural number `c`, and `N · c = 2^|A|` (parent `total_reprCount`).  Thus
  `N ∣ 2^|A|`, so `N = 2^j` and `⌈log₂N⌉ = j`; the minimality hypothesis
  `|A| = ⌈log₂N⌉` then gives `|A| = j`, whence `2^j · c = 2^j` and `c = 1`.

  Combined with `epsUniform_zero_of_unique_repr` this is a full EQUIVALENCE on
  minimum-size sets:

      |A| = ⌈log₂N⌉  ⟹  ( IsEpsUniform A 0  ↔  ∀ g, reprCount A g = 1 ).

  Consequence for oq-02: on the power-of-two family the conjectured additive
  constant is *exactly* `0`, and the optimum is attained ONLY by
  unique-representation (basis-type) sets — there is no slack at the extreme.
  This does not address general `N` or the with-high-probability random setting,
  which remain the genuine open content of oq-02.

  No axioms, no `sorry`.  Depends on `total_reprCount` (parent) and the sibling
  lower/upper lemmas; uses only `Nat.dvd_prime_pow`, `Nat.clog_pow`,
  `Nat.eq_of_mul_eq_mul_left` from Mathlib.

  NOTE: build-pending — written under a Docker blackout (host `lake`/Docker
  unavailable).  NOT registered in `Proofs.lean`; a post-blackout session should
  confirm via `./proofs/scripts/docker-build.sh Proofs.Erdos1179OQ02Extremal`
  before registering.  Mathlib bearers name-checked @ pinned rev 2df2f01:
  `Nat.clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x` (Data/Nat/Log.lean:453,
  same lemma the Upper file already relies on); `Nat.dvd_prime_pow`;
  `Nat.eq_of_mul_eq_mul_left`.
-/

import Proofs.Erdos1179Problem
import Proofs.Erdos1179OQ02
import Proofs.Erdos1179OQ02Upper
import Mathlib

namespace Erdos1179

open Finset

/-- **Extremal rigidity (converse).**  If `A` is `0`-uniform and meets the lower
bound `|A| = ⌈log₂N⌉`, then every group element has a *unique* subset-sum
representation.

The `0`-uniformity collapses all representation counts to one natural number
`c = 2^|A| / N`; the minimality `|A| = ⌈log₂N⌉` then forces `c = 1`. -/
theorem unique_repr_of_epsUniform_zero_clog {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (hunif : IsEpsUniform A 0)
    (hcard : A.card = Nat.clog 2 (Fintype.card G)) :
    ∀ g, reprCount A g = 1 := by
  -- ε = 0 forces every count to equal the expected count μ exactly.
  have heq : ∀ g, (reprCount A g : ℝ)
      = expectedReprCount A.card (Fintype.card G) := by
    intro g
    have h := hunif g
    rw [zero_mul] at h
    have h0 : |(reprCount A g : ℝ)
        - expectedReprCount A.card (Fintype.card G)| = 0 :=
      le_antisymm h (abs_nonneg _)
    have := abs_eq_zero.mp h0
    linarith
  -- Hence all counts coincide with c := reprCount A 0.
  have hconst : ∀ g, reprCount A g = reprCount A (0 : G) := by
    intro g
    have : (reprCount A g : ℝ) = (reprCount A (0 : G) : ℝ) := by
      rw [heq g, heq 0]
    exact_mod_cast this
  -- The counts sum to 2 ^ |A| (parent) and also to N * c.
  have hsum : Fintype.card G * reprCount A (0 : G) = 2 ^ A.card := by
    have key : ∑ g : G, reprCount A g = ∑ _g : G, reprCount A (0 : G) :=
      Finset.sum_congr rfl fun g _ => hconst g
    have hT := total_reprCount A
    rw [key] at hT
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hT
  -- N ∣ 2 ^ |A|, so N = 2 ^ j; clog forces j = |A|, so c = 1.
  have hdvd : Fintype.card G ∣ 2 ^ A.card := ⟨_, hsum.symm⟩
  obtain ⟨j, _, hNj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hclog : Nat.clog 2 (Fintype.card G) = j := by
    rw [hNj, Nat.clog_pow 2 j (by norm_num)]
  have hAj : A.card = j := by rw [hcard, hclog]
  have hc1 : reprCount A (0 : G) = 1 := by
    rw [hNj, hAj] at hsum
    have hmul : 2 ^ j * reprCount A (0 : G) = 2 ^ j * 1 := by
      rw [mul_one]; exact hsum
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) j) hmul
  intro g
  rw [hconst g]
  exact hc1

/-- **Admissibility of the order `N` for exact `0`-uniformity.**  If *any* finset
`A` is `0`-uniform, then the group order `N = |G|` must be a power of two,
`N = 2^j` with `j ≤ |A|`.  (No minimality hypothesis: this holds for every
`0`-uniform set, of any size.)

`0`-uniformity collapses all representation counts to one natural number `c`, so
`N · c = 2^|A|` (parent `total_reprCount`), giving `N ∣ 2^|A|` and hence
`N = 2^j` by `Nat.dvd_prime_pow`.  This is the structural core that the converse
`unique_repr_of_epsUniform_zero_clog` specialises once minimality is added. -/
theorem card_pow_two_of_epsUniform_zero {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (hunif : IsEpsUniform A 0) :
    ∃ j ≤ A.card, Fintype.card G = 2 ^ j := by
  -- ε = 0 forces every count to equal the expected count μ exactly.
  have heq : ∀ g, (reprCount A g : ℝ)
      = expectedReprCount A.card (Fintype.card G) := by
    intro g
    have h := hunif g
    rw [zero_mul] at h
    have h0 : |(reprCount A g : ℝ)
        - expectedReprCount A.card (Fintype.card G)| = 0 :=
      le_antisymm h (abs_nonneg _)
    have := abs_eq_zero.mp h0
    linarith
  -- Hence all counts coincide with c := reprCount A 0.
  have hconst : ∀ g, reprCount A g = reprCount A (0 : G) := by
    intro g
    have : (reprCount A g : ℝ) = (reprCount A (0 : G) : ℝ) := by
      rw [heq g, heq 0]
    exact_mod_cast this
  -- The counts sum to 2 ^ |A| (parent) and also to N * c.
  have hsum : Fintype.card G * reprCount A (0 : G) = 2 ^ A.card := by
    have key : ∑ g : G, reprCount A g = ∑ _g : G, reprCount A (0 : G) :=
      Finset.sum_congr rfl fun g _ => hconst g
    have hT := total_reprCount A
    rw [key] at hT
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hT
  -- N ∣ 2 ^ |A|, so N = 2 ^ j with j ≤ |A| (Nat.dvd_prime_pow, prime 2).
  have hdvd : Fintype.card G ∣ 2 ^ A.card := ⟨_, hsum.symm⟩
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd

/-- **No exact `0`-uniform set when the order is not a power of two.**  If
`N = |G|` is not a power of two, then *no* finset is `0`-uniform.  This is the
contrapositive of `card_pow_two_of_epsUniform_zero`, and it completes the
dichotomy for oq-02: an exactly `ε = 0` subset-sum representation is attainable
iff `N` is a power of two.  For every other `N` the optimal additive constant is
strictly positive (no set is exactly uniform), in contrast to the constant `0`
achieved on the power-of-two family by `epsUniform_zero_of_unique_repr`. -/
theorem not_epsUniform_zero_of_not_pow_two {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G)
    (hN : ∀ j, Fintype.card G ≠ 2 ^ j) :
    ¬ IsEpsUniform A 0 := by
  intro hunif
  obtain ⟨j, _, hNj⟩ := card_pow_two_of_epsUniform_zero A hunif
  exact hN j hNj

/-- **Extremal equivalence on minimum-size sets.**  When `|A| = ⌈log₂N⌉`, the
set `A` is `0`-uniform iff it gives every group element a unique subset-sum
representation.  Forward direction is `unique_repr_of_epsUniform_zero_clog`;
backward is the sibling `epsUniform_zero_of_unique_repr`. -/
theorem epsUniform_zero_iff_unique_repr_of_clog {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G)
    (hcard : A.card = Nat.clog 2 (Fintype.card G)) :
    IsEpsUniform A 0 ↔ ∀ g, reprCount A g = 1 :=
  ⟨fun hunif => unique_repr_of_epsUniform_zero_clog A hunif hcard,
   fun h => epsUniform_zero_of_unique_repr A h⟩

/-- **Optimality of unique-representation sets.**  A unique-representation set is
a minimum-cardinality `ε`-uniform set (for every `ε < 1`): no `ε`-uniform set
can be strictly smaller.  This is the explicit statement that the conjectured
oq-02 additive constant is attained — indeed it is `0` — on this family.

`|A| = ⌈log₂N⌉` (`unique_repr_card_eq_clog`) and `|B| ≥ ⌈log₂N⌉`
(`clog_le_card_of_epsUniform`). -/
theorem unique_repr_card_le_of_epsUniform {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (A : Finset G) (hA : ∀ g, reprCount A g = 1)
    (B : Finset G) (ε : ℝ) (hε : ε < 1) (hB : IsEpsUniform B ε) :
    A.card ≤ B.card := by
  rw [unique_repr_card_eq_clog A hA]
  exact clog_le_card_of_epsUniform B ε hε hB

end Erdos1179
