import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Erdős 1064 (OQ-03): the double totient iterate  φ(n)  vs  φ(n − φ(n − φ(n)))

## Background

Erdős #1064 concerns the single cototient step  c(n) = n − φ(n).  The parent
problem asks whether  φ(n) > φ(n − φ(n))  for almost all n (true, density 1,
Luca–Pomerance) while the reverse inequality still holds infinitely often.

This open question OQ-03 asks what happens for the **higher iterate**

  D(n)  :=  n − φ(n − φ(n)),

i.e. we compare  φ(n)  against  φ(D(n)) = φ(n − φ(n − φ(n))).

## What this file establishes (all machine-checked, no axioms)

1. **Collapse on primes.**  For *every* prime p we have  D(p) = p − 1
   exactly.  Indeed φ(p) = p − 1, so n − φ(n) = 1, φ(1) = 1, and
   D(p) = p − φ(1) = p − 1.

2. **Forward inequality on the whole family of odd primes.**  For every
   prime p ≥ 3,
        φ(D(p)) = φ(p − 1)  <  p − 1 = φ(p),
   so the "expected" direction  φ(n) > φ(D(n))  holds on an infinite family.
   The single exceptional prime is p = 2, where equality holds (D(2) = 1).

3. **The reverse inequality genuinely occurs.**  The smallest witness is
   n = 39: there D(39) = 31 is prime, φ(39) = 24 < 30 = φ(31) = φ(D(39)).
   So  φ(n) < φ(D(n))  for infinitely-often-observed n; concretely at n = 39.

The reverse cases empirically cluster where D(n) lands on a prime (31, 47, 73,
97, 113, …), making φ(D(n)) = D(n) − 1 large; a full "infinitely often"
statement remains the OPEN part of this question.
-/

open Nat

namespace Erdos1064OQ03

/-- The double cototient iterate  `D(n) = n − φ(n − φ(n))`. -/
def dblIter (n : ℕ) : ℕ := n - Nat.totient (n - Nat.totient n)

/-- **Collapse on primes.**  For every prime `p`, the double iterate satisfies
    `D(p) = p − 1`.  (φ(p) = p−1 ⟹ p − φ(p) = 1 ⟹ φ(1) = 1 ⟹ D(p) = p−1.) -/
theorem dblIter_prime {p : ℕ} (hp : p.Prime) : dblIter p = p - 1 := by
  unfold dblIter
  rw [Nat.totient_prime hp]
  have h1 : p - (p - 1) = 1 := by have := hp.two_le; omega
  rw [h1, Nat.totient_one]

/-- **Forward inequality on odd primes.**  For every prime `p ≥ 3`,
    `φ(D(p)) < φ(p)`, i.e. `φ(n) > φ(n − φ(n − φ(n)))` holds throughout the
    infinite family of odd primes. -/
theorem totient_dblIter_lt_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Nat.totient (dblIter p) < Nat.totient p := by
  rw [dblIter_prime hp, Nat.totient_prime hp]
  exact Nat.totient_lt (p - 1) (by omega)

/-- Sharp boundary: at the even prime `p = 2` the forward inequality degenerates
    to equality, `D(2) = 1` and `φ(D(2)) = φ(2)`. -/
theorem totient_dblIter_eq_two : Nat.totient (dblIter 2) = Nat.totient 2 := by
  have : dblIter 2 = 1 := dblIter_prime (by norm_num)
  rw [this, Nat.totient_one, Nat.totient_prime (by norm_num)]

-- ----------------------------------------------------------------------------
-- Concrete totient values used for the reverse witness (via factorisation,
-- avoiding kernel evaluation of `gcd` inside `decide`).
-- ----------------------------------------------------------------------------

/-- `φ(39) = 24`  (39 = 3·13, distinct primes). -/
theorem totient_39 : Nat.totient 39 = 24 := by
  rw [show (39 : ℕ) = 3 * 13 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(15) = 8`  (15 = 3·5, distinct primes). -/
theorem totient_15 : Nat.totient 15 = 8 := by
  rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(31) = 30`  (31 is prime). -/
theorem totient_31 : Nat.totient 31 = 30 := by
  rw [Nat.totient_prime (by norm_num)]

/-- The double iterate of 39 lands on the prime 31:  `D(39) = 31`. -/
theorem dblIter_39 : dblIter 39 = 31 := by
  unfold dblIter
  rw [totient_39, show (39 : ℕ) - 24 = 15 from rfl, totient_15]

/-- **The reverse inequality occurs.**  At `n = 39` the double iterate reverses
    the expected direction: `φ(39) = 24 < 30 = φ(D(39))`, since `D(39) = 31` is
    prime.  This exhibits a concrete member of the (conjecturally infinite)
    family of reversal points. -/
theorem reverse_at_39 : Nat.totient 39 < Nat.totient (dblIter 39) := by
  rw [dblIter_39, totient_39, totient_31]
  decide

/-- Summary corollary: the forward inequality `φ(n) > φ(D(n))` is **not**
    universal — it fails at `n = 39` — yet holds on the entire infinite family
    of odd primes.  Hence the higher-iterate analogue of Erdős 1064 exhibits
    the same both-directions behaviour as the single step. -/
theorem forward_not_universal :
    (∀ p : ℕ, p.Prime → 3 ≤ p → Nat.totient (dblIter p) < Nat.totient p) ∧
    (∃ n : ℕ, Nat.totient n < Nat.totient (dblIter n)) :=
  ⟨fun _ hp hp3 => totient_dblIter_lt_of_prime hp hp3, ⟨39, reverse_at_39⟩⟩

-- ----------------------------------------------------------------------------
-- Structural mechanism of the reversal:  when `D(n)` lands on a prime `q`, the
-- three-way comparison `φ(n)  vs  φ(D(n))` collapses to a single size test,
-- because `φ(q) = q − 1`.  This *explains* the empirical clustering of reversals
-- on prime landings — a structural theorem that subsumes the individual
-- numerical witnesses rather than enumerating them.
-- ----------------------------------------------------------------------------

/-- **Reversal criterion on prime landings.**  Whenever the double iterate lands
    on a prime, the reversal `φ(n) < φ(D(n))` is *equivalent* to the clean size
    condition `φ(n) + 1 < D(n)`.  (Since `φ(D(n)) = D(n) − 1`.)  This is the
    exact mechanism behind the reversal clustering: a prime landing makes
    `φ(D(n))` as large as possible, so reversal is governed purely by how large
    the landing value `D(n)` is relative to `φ(n)`. -/
theorem reversal_iff_of_dblIter_prime {n : ℕ} (hq : (dblIter n).Prime) :
    Nat.totient n < Nat.totient (dblIter n) ↔ Nat.totient n + 1 < dblIter n := by
  rw [Nat.totient_prime hq]
  have := hq.two_le
  omega

/-- **Sufficient condition for reversal.**  If `D(n)` is prime and exceeds
    `φ(n) + 1`, then `n` is a reversal point.  A one-line consequence of
    `reversal_iff_of_dblIter_prime` that packages the "prime landing + large
    landing value" pattern into a directly usable form. -/
theorem reverse_of_dblIter_prime {n : ℕ} (hq : (dblIter n).Prime)
    (hsize : Nat.totient n + 1 < dblIter n) :
    Nat.totient n < Nat.totient (dblIter n) :=
  (reversal_iff_of_dblIter_prime hq).mpr hsize

/-- The `n = 39` witness re-derived structurally: `D(39) = 31` is prime and
    `φ(39) + 1 = 25 < 31`, so the criterion fires. -/
theorem reverse_at_39' : Nat.totient 39 < Nat.totient (dblIter 39) :=
  reverse_of_dblIter_prime (by rw [dblIter_39]; norm_num)
    (by rw [totient_39, dblIter_39]; decide)

-- ----------------------------------------------------------------------------
-- A SECOND reversal family:  reversal is *not* confined to prime landings.
-- At `n = 42` the double iterate lands on the **composite** value
-- `D(42) = 34 = 2·17`, yet the reversal `φ(42) < φ(D(42))` still holds.
-- This shows the reversal phenomenon extends beyond the `D(n) prime` family,
-- refining the earlier empirical observation that reversals "cluster" on primes.
-- ----------------------------------------------------------------------------

/-- `φ(42) = 12`  (42 = 2·21, φ(21) = φ(3·7) = 12). -/
theorem totient_42 : Nat.totient 42 = 12 := by
  rw [show (42 : ℕ) = 2 * 21 from rfl, Nat.totient_mul (by decide),
      show (21 : ℕ) = 3 * 7 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]

/-- `φ(30) = 8`  (30 = 2·15, φ(15) = 8). -/
theorem totient_30 : Nat.totient 30 = 8 := by
  rw [show (30 : ℕ) = 2 * 15 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), totient_15]

/-- `φ(34) = 16`  (34 = 2·17, distinct primes). -/
theorem totient_34 : Nat.totient 34 = 16 := by
  rw [show (34 : ℕ) = 2 * 17 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- The double iterate of 42 lands on the **composite** value 34:  `D(42) = 34`
    with `34 = 2 · 17`. -/
theorem dblIter_42 : dblIter 42 = 34 := by
  unfold dblIter
  rw [totient_42, show (42 : ℕ) - 12 = 30 from rfl, totient_30]

/-- `D(42) = 34` is **not** prime — witnessing that the landing value need not be
    prime for a reversal to occur. -/
theorem dblIter_42_not_prime : ¬ (dblIter 42).Prime := by
  rw [dblIter_42]; decide

/-- **A composite-landing reversal.**  At `n = 42` the double iterate reverses
    the expected direction, `φ(42) = 12 < 16 = φ(D(42))`, even though
    `D(42) = 34` is composite.  So the reversal family is strictly larger than
    the prime-landing family. -/
theorem reverse_at_42 : Nat.totient 42 < Nat.totient (dblIter 42) := by
  rw [dblIter_42, totient_42, totient_34]; decide

/-- **The reversal phenomenon is not confined to prime landings.**  There is a
    reversal point `n` whose double iterate `D(n)` is composite: concretely
    `n = 42`, where `D(42) = 34 = 2·17` and `φ(42) < φ(34)`. -/
theorem reversal_with_composite_landing :
    ∃ n : ℕ, ¬ (dblIter n).Prime ∧ Nat.totient n < Nat.totient (dblIter n) :=
  ⟨42, dblIter_42_not_prime, reverse_at_42⟩

-- ----------------------------------------------------------------------------
-- INFINITELY MANY reversals:  the explicit family  n = 21·2^(k+1).
--
-- This resolves the reversal (infinitely-often) direction of OQ-03 outright,
-- with no density input, by generalising the composite-landing witness n = 42
-- (the k = 0 case) into an infinite family.  For every k the double iterate
-- lands on  D(21·2^(k+1)) = 17·2^(k+1), and
--
--     φ(21·2^(k+1)) = 12·2^k   <   16·2^k = φ(17·2^(k+1)) = φ(D(n)),
--
-- so the reverse inequality  φ(n) < φ(D(n))  holds throughout an infinite,
-- injectively-parametrised family.  The mechanism mirrors the single-step
-- family n = 15·2^(k+1) of the parent problem (Erdős 1064), but pushed through
-- one extra cototient step:
--
--     21·2^(k+1)  --−φ-->  15·2^(k+1)  --−φ-->  17·2^(k+1),
--
-- where the first cototient step 21·2^(k+1) − φ(·) = 15·2^(k+1) is exactly the
-- entry point of the parent family, and the second step lifts the odd part
-- 15 ↦ 17, raising the totient past φ(n).
-- ----------------------------------------------------------------------------

/-- The reversal set  `{n | φ(n) < φ(D(n))}`  of OQ-03. -/
def ReversalSet : Set ℕ := {n : ℕ | Nat.totient n < Nat.totient (dblIter n)}

/-- **The double iterate collapses the family `21·2^(k+1)` onto `17·2^(k+1)`.**
    For every `k`, `D(21·2^(k+1)) = 17·2^(k+1)`.  (First cototient step lands on
    `15·2^(k+1)`, the parent family's member; the second lifts `15 ↦ 17`.) -/
theorem dblIter_family (k : ℕ) : dblIter (21 * 2 ^ (k + 1)) = 17 * 2 ^ (k + 1) := by
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have cop21 : Nat.Coprime 21 (2 ^ (k + 1)) :=
    (show Nat.Coprime 21 2 by norm_num).pow_right (k + 1)
  have cop15 : Nat.Coprime 15 (2 ^ (k + 1)) :=
    (show Nat.Coprime 15 2 by norm_num).pow_right (k + 1)
  have h21 : Nat.totient 21 = 12 := by
    rw [show (21 : ℕ) = 3 * 7 from rfl, Nat.totient_mul (by decide),
        Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  -- φ(n) = 12·2^k
  have hφn : Nat.totient (21 * 2 ^ (k + 1)) = 12 * 2 ^ k := by
    rw [Nat.totient_mul cop21, h21, hp2]
  -- n − φ(n) = 15·2^(k+1)
  have hsub1 : 21 * 2 ^ (k + 1) - 12 * 2 ^ k = 15 * 2 ^ (k + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2]; omega
  -- φ(15·2^(k+1)) = 8·2^k
  have hφsub : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop15, totient_15, hp2]
  -- D(n) = n − φ(n − φ(n)) = 17·2^(k+1)
  unfold dblIter
  rw [hφn, hsub1, hφsub]
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h2]; omega

/-- **Reversal on the entire family `21·2^(k+1)`.**  For every `k`,
    `φ(21·2^(k+1)) = 12·2^k < 16·2^k = φ(D(21·2^(k+1)))`, so each member is a
    reversal point.  In particular `n = 42` (k = 0) and `n = 84` (k = 1) recover
    the earlier numerical witnesses. -/
theorem mem_ReversalSet_family (k : ℕ) : 21 * 2 ^ (k + 1) ∈ ReversalSet := by
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have cop21 : Nat.Coprime 21 (2 ^ (k + 1)) :=
    (show Nat.Coprime 21 2 by norm_num).pow_right (k + 1)
  have cop17 : Nat.Coprime 17 (2 ^ (k + 1)) :=
    (show Nat.Coprime 17 2 by norm_num).pow_right (k + 1)
  have h21 : Nat.totient 21 = 12 := by
    rw [show (21 : ℕ) = 3 * 7 from rfl, Nat.totient_mul (by decide),
        Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]
  have hφn : Nat.totient (21 * 2 ^ (k + 1)) = 12 * 2 ^ k := by
    rw [Nat.totient_mul cop21, h21, hp2]
  have hφD : Nat.totient (17 * 2 ^ (k + 1)) = 16 * 2 ^ k := by
    rw [Nat.totient_mul cop17, Nat.totient_prime (by norm_num), hp2]
  show Nat.totient (21 * 2 ^ (k + 1)) < Nat.totient (dblIter (21 * 2 ^ (k + 1)))
  rw [dblIter_family, hφn, hφD]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

/-- The map `k ↦ 21·2^(k+1)` is injective. -/
theorem family_injective : Function.Injective (fun k : ℕ => 21 * 2 ^ (k + 1)) := by
  intro a b hab
  simp only at hab
  have h2 : (2 : ℕ) ^ (a + 1) = 2 ^ (b + 1) := Nat.eq_of_mul_eq_mul_left (by norm_num) hab
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

/-- **The reversal `φ(n) < φ(D(n))` holds infinitely often.**  This resolves the
    open (infinitely-often) direction of OQ-03 for the double iterate: the
    reversal set `{n | φ(n) < φ(D(n))}` is infinite, exhibited by the explicit
    injective family `n = 21·2^(k+1)`.  No density machinery is required. -/
theorem reversal_infinitely_many : ReversalSet.Infinite :=
  Set.infinite_of_injective_forall_mem family_injective mem_ReversalSet_family

/-- **Summary (OQ-03, both directions realised infinitely).**  Both the forward
    inequality `φ(n) > φ(D(n))` (on the infinite family of odd primes) and the
    reverse inequality `φ(n) < φ(D(n))` (on the infinite family `21·2^(k+1)`)
    hold on explicit infinite families.  So, exactly as for the single-step
    Erdős 1064, the higher-iterate comparison genuinely goes both ways —
    infinitely often in each direction. -/
theorem oq03_both_directions_infinite :
    {p : ℕ | p.Prime ∧ 3 ≤ p}.Infinite ∧ ReversalSet.Infinite := by
  refine ⟨?_, reversal_infinitely_many⟩
  -- the odd primes are infinite
  have : {p : ℕ | p.Prime ∧ 3 ≤ p} = {p : ℕ | p.Prime} \ {2} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hp3⟩; exact ⟨hp, by omega⟩
    · rintro ⟨hp, hp2⟩; exact ⟨hp, by have := hp.two_le; omega⟩
  rw [this]
  exact Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)

-- ===========================================================================
-- EQUALITY family:  φ(n) = φ(D(n)) holds infinitely often, via  n = 15·2^(k+1).
--
-- The higher-iterate comparison is genuinely THREE-WAY (>, =, <), not a clean
-- dichotomy: alongside the forward (odd-prime) and reversal (21·2^(k+1))
-- families, the diagonal `φ(n) = φ(D(n))` is realised on its own explicit
-- infinite family.  For n = 15·2^(k+1) the double iterate collapses to
-- D(n) = 5·2^(k+2), and both n and D(n) carry the SAME totient value 8·2^k:
--
--   φ(15·2^(k+1)) = 8·2^k;                       (15 = 3·5, φ(15) = 8)
--   n − φ(n) = 11·2^(k+1),  φ(11·2^(k+1)) = 10·2^k;
--   D(n) = 15·2^(k+1) − 10·2^k = 20·2^k = 5·2^(k+2);
--   φ(5·2^(k+2)) = 4·2^(k+1) = 8·2^k = φ(n).
--
-- This turns the earlier empirical observation ("equality is common, 35 of the
-- n in [2,200)") into a proved infinite branch, and — with the two inequality
-- families — pins down all three cases as occurring infinitely often.
-- ===========================================================================

/-- The equality locus `{n | φ(n) = φ(D(n))}` for the double iterate. -/
def EqualitySet : Set ℕ := {n : ℕ | Nat.totient n = Nat.totient (dblIter n)}

/-- **The double iterate collapses the family `15·2^(k+1)` onto `5·2^(k+2)`.**
    For every `k`, `D(15·2^(k+1)) = 5·2^(k+2)`.  (First cototient step lands on
    `11·2^(k+1)`; the second step recombines to the pure power-of-two–times-`5`
    form `20·2^k`.) -/
theorem dblIter_eq_family (k : ℕ) : dblIter (15 * 2 ^ (k + 1)) = 5 * 2 ^ (k + 2) := by
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have cop15 : Nat.Coprime 15 (2 ^ (k + 1)) :=
    (show Nat.Coprime 15 2 by norm_num).pow_right (k + 1)
  have cop11 : Nat.Coprime 11 (2 ^ (k + 1)) :=
    (show Nat.Coprime 11 2 by norm_num).pow_right (k + 1)
  -- φ(n) = 8·2^k
  have hφn : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop15, totient_15, hp2]
  -- n − φ(n) = 11·2^(k+1)
  have hsub1 : 15 * 2 ^ (k + 1) - 8 * 2 ^ k = 11 * 2 ^ (k + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [h2]; omega
  -- φ(11·2^(k+1)) = 10·2^k
  have hφsub : Nat.totient (11 * 2 ^ (k + 1)) = 10 * 2 ^ k := by
    rw [Nat.totient_mul cop11, Nat.totient_prime (by norm_num), hp2]
  -- D(n) = n − φ(n − φ(n)) = 5·2^(k+2)
  unfold dblIter
  rw [hφn, hsub1, hφsub]
  have h2 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  have h2' : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h2, h2']; omega

/-- **Equality on the entire family `15·2^(k+1)`.**  For every `k`,
    `φ(15·2^(k+1)) = 8·2^k = φ(D(15·2^(k+1)))`, so each member sits exactly on
    the diagonal `φ(n) = φ(D(n))`. -/
theorem mem_EqualitySet_family (k : ℕ) : 15 * 2 ^ (k + 1) ∈ EqualitySet := by
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have hp2' : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 1))]; simp
  have cop15 : Nat.Coprime 15 (2 ^ (k + 1)) :=
    (show Nat.Coprime 15 2 by norm_num).pow_right (k + 1)
  have cop5 : Nat.Coprime 5 (2 ^ (k + 2)) :=
    (show Nat.Coprime 5 2 by norm_num).pow_right (k + 2)
  have hφn : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    rw [Nat.totient_mul cop15, totient_15, hp2]
  have hφD : Nat.totient (5 * 2 ^ (k + 2)) = 4 * 2 ^ (k + 1) := by
    rw [Nat.totient_mul cop5, Nat.totient_prime (by norm_num), hp2']
  show Nat.totient (15 * 2 ^ (k + 1)) = Nat.totient (dblIter (15 * 2 ^ (k + 1)))
  rw [dblIter_eq_family, hφn, hφD]
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h2]; ring

/-- The map `k ↦ 15·2^(k+1)` is injective. -/
theorem eq_family_injective : Function.Injective (fun k : ℕ => 15 * 2 ^ (k + 1)) := by
  intro a b hab
  simp only at hab
  have h2 : (2 : ℕ) ^ (a + 1) = 2 ^ (b + 1) := Nat.eq_of_mul_eq_mul_left (by norm_num) hab
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

/-- **Equality `φ(n) = φ(D(n))` holds infinitely often.**  The diagonal locus
    `{n | φ(n) = φ(D(n))}` is infinite, exhibited by the explicit injective
    family `n = 15·2^(k+1)`.  No density machinery is required. -/
theorem equality_infinitely_many : EqualitySet.Infinite :=
  Set.infinite_of_injective_forall_mem eq_family_injective mem_EqualitySet_family

/-- **Summary (OQ-03, all three cases realised infinitely).**  The higher-iterate
    comparison `φ(n)` vs `φ(D(n))` is genuinely three-way: the strict forward
    inequality (odd primes), the strict reversal (`21·2^(k+1)`), and exact
    equality (`15·2^(k+1)`) each hold on an explicit infinite family.  So, unlike
    a clean dichotomy, all of `>`, `=`, `<` occur infinitely often. -/
theorem oq03_three_way_infinite :
    {p : ℕ | p.Prime ∧ 3 ≤ p}.Infinite ∧ ReversalSet.Infinite ∧ EqualitySet.Infinite :=
  ⟨oq03_both_directions_infinite.1, reversal_infinitely_many, equality_infinitely_many⟩

end Erdos1064OQ03
