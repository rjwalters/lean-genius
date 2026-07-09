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

-- ===========================================================================
-- FORWARD family on COMPOSITES:  φ(n) > φ(D(n)) on the powers of two n = 2^(k+3).
--
-- So far the forward direction `φ(n) > φ(D(n))` was exhibited only on the
-- infinite family of odd PRIMES, whereas the reversal (`21·2^(k+1)`) and
-- equality (`15·2^(k+1)`) directions each already run over an infinite
-- COMPOSITE family.  This closes that asymmetry: the forward inequality is not
-- confined to primes either — it holds throughout the infinite composite family
-- of pure powers of two.  For n = 2^(k+3) the double iterate collapses to
-- D(n) = 3·2^(k+1):
--
--   φ(2^(k+3)) = 2^(k+2);
--   n − φ(n) = 2^(k+2),  φ(2^(k+2)) = 2^(k+1);
--   D(n) = 2^(k+3) − 2^(k+1) = 3·2^(k+1);
--   φ(3·2^(k+1)) = 2·2^k = 2^(k+1)  <  2^(k+2) = φ(n).
--
-- Thus each of the three relations `>`, `=`, `<` is now realised on an explicit
-- infinite family of COMPOSITE integers, matching the structural picture.
-- ===========================================================================

/-- The forward locus `{n | φ(D(n)) < φ(n)}` for the double iterate. -/
def ForwardSet : Set ℕ := {n : ℕ | Nat.totient (dblIter n) < Nat.totient n}

/-- **The double iterate collapses the power-of-two family `2^(k+3)` onto
    `3·2^(k+1)`.**  For every `k`, `D(2^(k+3)) = 3·2^(k+1)`.  (First cototient
    step lands on `2^(k+2)`; the second subtracts `2^(k+1)`, leaving `3·2^(k+1)`.)
    -/
theorem dblIter_pow2 (k : ℕ) : dblIter (2 ^ (k + 3)) = 3 * 2 ^ (k + 1) := by
  have e1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e2 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  have e3 : (2 : ℕ) ^ (k + 3) = 8 * 2 ^ k := by rw [pow_succ, pow_succ, pow_succ]; ring
  have hp3 : Nat.totient (2 ^ (k + 3)) = 2 ^ (k + 2) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 2))]; simp
  have hp2' : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 1))]; simp
  unfold dblIter
  rw [hp3]
  have hsub : 2 ^ (k + 3) - 2 ^ (k + 2) = 2 ^ (k + 2) := by omega
  rw [hsub, hp2']
  omega

/-- **Forward inequality on the entire power-of-two family `2^(k+3)`.**  For every
    `k`, `φ(D(2^(k+3))) = 2^(k+1) < 2^(k+2) = φ(2^(k+3))`, so each member lies in
    the forward locus. -/
theorem mem_ForwardSet_pow2 (k : ℕ) : 2 ^ (k + 3) ∈ ForwardSet := by
  have e2 : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
  have hp3 : Nat.totient (2 ^ (k + 3)) = 2 ^ (k + 2) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 2))]; simp
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have cop3 : Nat.Coprime 3 (2 ^ (k + 1)) :=
    (show Nat.Coprime 3 2 by norm_num).pow_right (k + 1)
  have hφD : Nat.totient (3 * 2 ^ (k + 1)) = 2 * 2 ^ k := by
    rw [Nat.totient_mul cop3, Nat.totient_prime (by norm_num), hp2]
  show Nat.totient (dblIter (2 ^ (k + 3))) < Nat.totient (2 ^ (k + 3))
  rw [dblIter_pow2, hφD, hp3, e2]
  omega

/-- `2^(k+3)` is composite (divisible by 2 and at least 8). -/
theorem not_prime_pow2 (k : ℕ) : ¬ (2 ^ (k + 3)).Prime := by
  intro h
  have hdvd : (2 : ℕ) ∣ 2 ^ (k + 3) := dvd_pow_self 2 (by omega)
  rcases h.eq_one_or_self_of_dvd 2 hdvd with h1 | h1
  · norm_num at h1
  · have h8 : (8 : ℕ) ≤ 2 ^ (k + 3) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- The map `k ↦ 2^(k+3)` is injective. -/
theorem pow2_family_injective : Function.Injective (fun k : ℕ => 2 ^ (k + 3)) := by
  intro a b hab
  simp only at hab
  have := Nat.pow_right_injective (le_refl 2) hab
  omega

/-- **The forward inequality `φ(n) > φ(D(n))` holds infinitely often.**  The
    forward locus `{n | φ(D(n)) < φ(n)}` is infinite, exhibited by the explicit
    injective power-of-two family `n = 2^(k+3)`. -/
theorem forward_infinitely_many : ForwardSet.Infinite :=
  Set.infinite_of_injective_forall_mem pow2_family_injective mem_ForwardSet_pow2

/-- **The forward inequality is not confined to primes.**  There are infinitely
    many *composite* `n` with `φ(n) > φ(D(n))`: the powers of two `n = 2^(k+3)`.
    This mirrors `reversal_with_composite_landing` for the forward direction and
    completes the symmetry — each of `>`, `=`, `<` now runs over an infinite
    family of composite integers. -/
theorem forward_not_confined_to_primes :
    {n : ℕ | ¬ n.Prime ∧ n ∈ ForwardSet}.Infinite :=
  Set.infinite_of_injective_forall_mem pow2_family_injective
    (fun k => ⟨not_prime_pow2 k, mem_ForwardSet_pow2 k⟩)

-- ===========================================================================
-- GENERAL TRANSPORT LEMMA:  one mechanism behind all of the families above.
--
-- Every explicit family in this file — 15·2^(k+1) (equality), 21·2^(k+1)
-- (reversal), and the power-of-two forward family — is a special case of a
-- single structural fact.  For an odd seed `a` whose first cototient step has
-- 2-adic valuation exactly one — i.e. `2a − φ(a) = 2b` with `b` again odd — the
-- double iterate transports the whole family `a·2^(k+1)` onto `(2a − φ(b))·2^k`,
-- uniformly in `k`:
--
--     D(a·2^(k+1)) = (2a − φ(b))·2^k.
--
-- The odd data `(a, b)` carries everything; the power of two is inert and merely
-- scales.  Because the landing constant `C = 2a − φ(b)` is INDEPENDENT of `k`,
-- the three-way sign of `φ(n) − φ(D(n))` is constant along each family — which is
-- exactly why every family realises a single one of `>`, `=`, `<` for all `k`.
-- The lemma is also GENERATIVE: feeding it new odd seeds yields brand-new
-- infinite families in each regime (below, `a = 5` and `a = 13`).
-- ===========================================================================

/-- **General transport lemma.**  Let `a`, `b` be odd with `2a − φ(a) = 2b`
    (the first cototient step has 2-adic valuation exactly one).  Then for every
    `k` the double iterate transports the family `a·2^(k+1)` onto the value
    `(2a − φ(b))·2^k`.  Each explicit family of this file is an instance:
    `a = 15, b = 11`; `a = 21, b = 15`; etc. -/
theorem dblIter_transport {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (hstep : 2 * a - Nat.totient a = 2 * b) (k : ℕ) :
    dblIter (a * 2 ^ (k + 1)) = (2 * a - Nat.totient b) * 2 ^ k := by
  -- odd ⇒ coprime to every power of two
  have oddCop : ∀ c : ℕ, Odd c → Nat.Coprime c (2 ^ (k + 1)) := by
    intro c hc
    have h2 : ¬ (2 ∣ c) := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      have := Nat.odd_iff.mp hc
      omega
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm.pow_right (k + 1)
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have copa := oddCop a ha
  have copb := oddCop b hb
  have hm1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e_n : a * 2 ^ (k + 1) = 2 * a * 2 ^ k := by rw [hm1]; ring
  -- φ(n) = φ(a)·2^k
  have hφn : Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k := by
    rw [Nat.totient_mul copa, hp2]
  -- first cototient step lands on b·2^(k+1)
  have step1 : a * 2 ^ (k + 1) - Nat.totient a * 2 ^ k = b * 2 ^ (k + 1) := by
    rw [e_n, hm1,
        show (2 : ℕ) * a * 2 ^ k = (2 * a) * 2 ^ k from by ring,
        show b * (2 * 2 ^ k) = (2 * b) * 2 ^ k from by ring,
        ← Nat.sub_mul, hstep]
  -- φ(b·2^(k+1)) = φ(b)·2^k
  have hφb : Nat.totient (b * 2 ^ (k + 1)) = Nat.totient b * 2 ^ k := by
    rw [Nat.totient_mul copb, hp2]
  unfold dblIter
  rw [hφn, step1, hφb, e_n,
      show (2 : ℕ) * a * 2 ^ k = (2 * a) * 2 ^ k from by ring, ← Nat.sub_mul]

-- Concrete totient values for the seeds (via factorisation, NOT kernel `decide`
-- on `Nat.totient`, which would blow the stack — see the note near `totient_15`).
theorem totient_5 : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)
theorem totient_13 : Nat.totient 13 = 12 := Nat.totient_prime (by norm_num)
theorem totient_21 : Nat.totient 21 = 12 := by
  rw [show (21 : ℕ) = 3 * 7 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- The existing reversal family `21·2^(k+1)` is an instance of transport:
    `D(21·2^(k+1)) = 34·2^k = 17·2^(k+1)` (cf. `dblIter_family`). -/
example (k : ℕ) : dblIter (21 * 2 ^ (k + 1)) = 34 * 2 ^ k := by
  have h := dblIter_transport (a := 21) (b := 15)
    (by decide) (by decide) (by rw [totient_21]) k
  rw [h]; norm_num [totient_15]

/-- The existing equality family `15·2^(k+1)` is an instance of transport:
    `D(15·2^(k+1)) = 20·2^k = 5·2^(k+2)` (cf. `dblIter_eq_family`). -/
example (k : ℕ) : dblIter (15 * 2 ^ (k + 1)) = 20 * 2 ^ k := by
  have h := dblIter_transport (a := 15) (b := 11)
    (by decide) (by decide) (by rw [totient_15]) k
  rw [h]; norm_num [Nat.totient_prime (show Nat.Prime 11 by norm_num)]

-- --- NEW families obtained by feeding the transport lemma fresh odd seeds ---

/-- **New equality family `5·2^(k+1)` (seed `a = 5`, `b = 3`).**  Transport gives
    `D(5·2^(k+1)) = (2·5 − φ(3))·2^k = 8·2^k = 2^(k+3)`, and
    `φ(5·2^(k+1)) = 4·2^k = 2^(k+2) = φ(2^(k+3))`, so every member lies exactly on
    the equality diagonal.  This is a smaller equality family than `15·2^(k+1)`,
    generated purely from the transport mechanism. -/
theorem mem_EqualitySet_five (k : ℕ) : 5 * 2 ^ (k + 1) ∈ EqualitySet := by
  have hD : dblIter (5 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
    have h := dblIter_transport (a := 5) (b := 3)
      (by decide) (by decide) (by rw [totient_5]) k
    rw [h]; norm_num [Nat.totient_prime (show Nat.Prime 3 by norm_num)]
  show Nat.totient (5 * 2 ^ (k + 1)) = Nat.totient (dblIter (5 * 2 ^ (k + 1)))
  rw [hD]
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have cop5 : Nat.Coprime 5 (2 ^ (k + 1)) :=
    (show Nat.Coprime 5 2 by norm_num).pow_right (k + 1)
  have hφn : Nat.totient (5 * 2 ^ (k + 1)) = 4 * 2 ^ k := by
    rw [Nat.totient_mul cop5, Nat.totient_prime (by norm_num), hp2]
  have h8 : (8 : ℕ) * 2 ^ k = 2 ^ (k + 3) := by rw [pow_add]; ring
  have hφD : Nat.totient (8 * 2 ^ k) = 4 * 2 ^ k := by
    rw [h8, Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k + 3)]
    rw [show k + 3 - 1 = k + 2 from by omega, show (2 : ℕ) - 1 = 1 from rfl,
        mul_one, pow_add]
    ring
  rw [hφn, hφD]

/-- **New forward family `13·2^(k+1)` (seed `a = 13`, `b = 7`).**  Transport gives
    `D(13·2^(k+1)) = (2·13 − φ(7))·2^k = 20·2^k = 5·2^(k+2)`, and
    `φ(13·2^(k+1)) = 12·2^k > 8·2^k = φ(5·2^(k+2)) = φ(D(n))`, so every member is a
    forward point.  This is a composite forward family distinct from the earlier
    power-of-two family, again generated from the transport mechanism. -/
theorem mem_ForwardSet_thirteen (k : ℕ) : 13 * 2 ^ (k + 1) ∈ ForwardSet := by
  have hD : dblIter (13 * 2 ^ (k + 1)) = 20 * 2 ^ k := by
    have h := dblIter_transport (a := 13) (b := 7)
      (by decide) (by decide) (by rw [totient_13]) k
    rw [h]; norm_num [Nat.totient_prime (show Nat.Prime 7 by norm_num)]
  show Nat.totient (dblIter (13 * 2 ^ (k + 1))) < Nat.totient (13 * 2 ^ (k + 1))
  rw [hD]
  have hp2 : Nat.totient (2 ^ (k + 1)) = 2 ^ k := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]; simp
  have hp2' : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos (k + 1))]; simp
  have cop13 : Nat.Coprime 13 (2 ^ (k + 1)) :=
    (show Nat.Coprime 13 2 by norm_num).pow_right (k + 1)
  have cop5 : Nat.Coprime 5 (2 ^ (k + 2)) :=
    (show Nat.Coprime 5 2 by norm_num).pow_right (k + 2)
  have hφn : Nat.totient (13 * 2 ^ (k + 1)) = 12 * 2 ^ k := by
    rw [Nat.totient_mul cop13, Nat.totient_prime (by norm_num), hp2]
  have h20 : (20 : ℕ) * 2 ^ k = 5 * 2 ^ (k + 2) := by rw [pow_add]; ring
  have hφD : Nat.totient (20 * 2 ^ k) = 8 * 2 ^ k := by
    rw [h20, Nat.totient_mul cop5, Nat.totient_prime (by norm_num), hp2', pow_succ]
    ring
  rw [hφn, hφD]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

/-- **Generativity of the transport lemma.**  Beyond the original three seeds
    (15, 21, powers of two), transport yields further explicit infinite families
    in each regime.  Two new ones: `a = 5` places every `5·2^(k+1)` on the
    equality diagonal, and `a = 13` places every `13·2^(k+1)` in the forward
    region — neither coinciding with the earlier families. -/
theorem transport_new_seeds :
    (∀ k, 5 * 2 ^ (k + 1) ∈ EqualitySet) ∧ (∀ k, 13 * 2 ^ (k + 1) ∈ ForwardSet) :=
  ⟨mem_EqualitySet_five, mem_ForwardSet_thirteen⟩

-- ===========================================================================
-- THE k-INDEPENDENT THREE-WAY CRITERION
-- ---------------------------------------------------------------------------
-- The transport lemma places `D(a·2^(k+1)) = C·2^k` with `C = 2a − φ(b)`
-- constant in `k`.  To read off the sign of `φ(n) − φ(D(n))` one must also know
-- `φ(D(n))`, which depends on the 2-adic valuation of `C`.  Writing the landing
-- constant as `C = e·2^t` with `e` odd and `t ≥ 1` (it is always even, being a
-- difference of an even `2a` and the even `φ(b)` for `b ≥ 3`, or `e = 1` at the
-- bottom), BOTH totients factor through the inert `2^k`:
--
--       φ(n)    = φ(a) · 2^k,
--       φ(D(n)) = φ(e) · 2^(t−1) · 2^k.
--
-- Hence the three-way comparison `φ(n) ⋛ φ(D(n))` is, for EVERY `k`, decided by
-- the single `k`-free inequality `φ(a) ⋛ φ(e)·2^(t−1)` on the odd data
-- `(a, e, t)`.  This is the criterion promised by the transport programme: the
-- regime of a whole family is a finite computation on three odd numbers, with
-- the power of two carrying no information.  The five explicit families of this
-- file are read off instantly (see the corollaries after the criterion).
-- ===========================================================================

/-- **k-independent double-iterate totient values.**  With the transport data
    `a, b` odd, `2a − φ(a) = 2b`, and the 2-adic decomposition of the landing
    constant `C = 2a − φ(b) = e·2^t` (`e` odd, `t ≥ 1`), both totients along the
    family `n = a·2^(k+1)` factor through a common `2^k`:
    `φ(n) = φ(a)·2^k` and `φ(D(n)) = φ(e)·2^(t−1)·2^k`.  All `k`-dependence is
    the inert factor `2^k`. -/
theorem dblIter_totient_values {a b e t : ℕ} (ha : Odd a) (hb : Odd b)
    (he : Odd e) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 * b)
    (hC : 2 * a - Nat.totient b = e * 2 ^ t) (k : ℕ) :
    Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k ∧
    Nat.totient (dblIter (a * 2 ^ (k + 1)))
      = Nat.totient e * 2 ^ (t - 1) * 2 ^ k := by
  -- odd ⇒ coprime to every power of two
  have oddCop : ∀ (c m : ℕ), Odd c → Nat.Coprime c (2 ^ m) := by
    intro c m hc
    have h2 : ¬ (2 ∣ c) := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      have := Nat.odd_iff.mp hc; omega
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm.pow_right m
  have hp2 : ∀ m : ℕ, Nat.totient (2 ^ (m + 1)) = 2 ^ m := by
    intro m; rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]; simp
  -- φ(n) = φ(a)·2^k
  have hφn : Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k := by
    rw [Nat.totient_mul (oddCop a (k + 1) ha), hp2 k]
  refine ⟨hφn, ?_⟩
  -- D(n) = e·2^(t+k)
  have hD : dblIter (a * 2 ^ (k + 1)) = e * 2 ^ (t + k) := by
    rw [dblIter_transport ha hb hstep k, hC, pow_add]; ring
  -- φ(2^(t+k)) = 2^(t+k−1)  (t+k ≥ 1 since t ≥ 1)
  have hφe2 : Nat.totient (2 ^ (t + k)) = 2 ^ (t + k - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, t + k = m + 1 := ⟨t + k - 1, by omega⟩
    rw [hm, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]
    simp
  rw [hD, Nat.totient_mul (oddCop e (t + k) he), hφe2]
  -- 2^(t+k−1) = 2^(t−1)·2^k
  have hexp : t + k - 1 = (t - 1) + k := by omega
  rw [hexp, pow_add, ← mul_assoc]

/-- **Three-way criterion — reversal branch.**  `φ(n) < φ(D(n))` for `n = a·2^(k+1)`
    iff the `k`-free inequality `φ(a) < φ(e)·2^(t−1)` holds. -/
theorem dblIter_reversal_iff {a b e t : ℕ} (ha : Odd a) (hb : Odd b)
    (he : Odd e) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 * b)
    (hC : 2 * a - Nat.totient b = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ ReversalSet
      ↔ Nat.totient a < Nat.totient e * 2 ^ (t - 1) := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values ha hb he ht hstep hC k
  show Nat.totient (a * 2 ^ (k + 1))
      < Nat.totient (dblIter (a * 2 ^ (k + 1))) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  · intro h; exact mul_lt_mul_of_pos_right h hpos

/-- **Three-way criterion — equality branch.**  `φ(n) = φ(D(n))` for `n = a·2^(k+1)`
    iff the `k`-free equality `φ(a) = φ(e)·2^(t−1)` holds. -/
theorem dblIter_equality_iff {a b e t : ℕ} (ha : Odd a) (hb : Odd b)
    (he : Odd e) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 * b)
    (hC : 2 * a - Nat.totient b = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ EqualitySet
      ↔ Nat.totient a = Nat.totient e * 2 ^ (t - 1) := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values ha hb he ht hstep hC k
  show Nat.totient (a * 2 ^ (k + 1))
      = Nat.totient (dblIter (a * 2 ^ (k + 1))) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact Nat.eq_of_mul_eq_mul_right hpos h
  · intro h; rw [h]

/-- **Three-way criterion — forward branch.**  `φ(D(n)) < φ(n)` for `n = a·2^(k+1)`
    iff the `k`-free inequality `φ(e)·2^(t−1) < φ(a)` holds. -/
theorem dblIter_forward_iff {a b e t : ℕ} (ha : Odd a) (hb : Odd b)
    (he : Odd e) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 * b)
    (hC : 2 * a - Nat.totient b = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ ForwardSet
      ↔ Nat.totient e * 2 ^ (t - 1) < Nat.totient a := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values ha hb he ht hstep hC k
  show Nat.totient (dblIter (a * 2 ^ (k + 1)))
      < Nat.totient (a * 2 ^ (k + 1)) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  · intro h; exact mul_lt_mul_of_pos_right h hpos

-- --- The criterion reads off all five families uniformly (no per-k work) ---

theorem totient_17 : Nat.totient 17 = 16 := Nat.totient_prime (by norm_num)

/-- Reversal family `21·2^(k+1)`: odd data `a = 21, e = 17, t = 1`, and
    `φ(21) = 12 < 16 = φ(17)·2^0`, so the criterion returns "reversal" for all `k`
    at once — recovering `mem_ReversalSet_family` from the sign inequality. -/
theorem reversal_via_criterion (k : ℕ) : (21 * 2 ^ (k + 1)) ∈ ReversalSet := by
  rw [dblIter_reversal_iff (a := 21) (b := 15) (e := 17) (t := 1)
        (by decide) (by decide) (by decide) (by norm_num)
        (by norm_num [totient_21]) (by norm_num [totient_15]) k]
  norm_num [totient_21, totient_17]

/-- Equality family `15·2^(k+1)`: odd data `a = 15, e = 5, t = 2`, and
    `φ(15) = 8 = 4·2 = φ(5)·2^1`, so the criterion returns "equality" for all `k`. -/
theorem equality_via_criterion (k : ℕ) : (15 * 2 ^ (k + 1)) ∈ EqualitySet := by
  rw [dblIter_equality_iff (a := 15) (b := 11) (e := 5) (t := 2)
        (by decide) (by decide) (by decide) (by norm_num)
        (by norm_num [totient_15])
        (by norm_num [Nat.totient_prime (show Nat.Prime 11 by norm_num)]) k]
  norm_num [totient_15, totient_5]

/-- Forward family `13·2^(k+1)`: odd data `a = 13, e = 5, t = 2`, and
    `φ(5)·2^1 = 8 < 12 = φ(13)`, so the criterion returns "forward" for all `k`. -/
theorem forward_via_criterion (k : ℕ) : (13 * 2 ^ (k + 1)) ∈ ForwardSet := by
  rw [dblIter_forward_iff (a := 13) (b := 7) (e := 5) (t := 2)
        (by decide) (by decide) (by decide) (by norm_num)
        (by norm_num [totient_13])
        (by norm_num [Nat.totient_prime (show Nat.Prime 7 by norm_num)]) k]
  norm_num [totient_13, totient_5]

/-- **The criterion is a complete `k`-free classifier for transport families.**
    All three explicit regimes are decided uniformly by the odd data `(a, e, t)`,
    with the power of two `2^k` carrying no information. -/
theorem threeway_criterion_classifies :
    (∀ k, (21 * 2 ^ (k + 1)) ∈ ReversalSet) ∧
    (∀ k, (15 * 2 ^ (k + 1)) ∈ EqualitySet) ∧
    (∀ k, (13 * 2 ^ (k + 1)) ∈ ForwardSet) :=
  ⟨reversal_via_criterion, equality_via_criterion, forward_via_criterion⟩

-- ===========================================================================
-- A SECOND REVERSAL SEED: the reversal seed set is not the singleton `{21}`
-- ---------------------------------------------------------------------------
-- The criterion makes the per-seed reversal test `φ(a) < φ(e)·2^(t−1)` a finite
-- computation on odd data, so we can hunt for reversal seeds beyond `a = 21`.
-- The next one is `a = 55`: `2·55 − φ(55) = 70 = 2·35` (so `b = 35`), the landing
-- constant `2·55 − φ(35) = 86 = 43·2^1` (so `e = 43`, `t = 1`), and
-- `φ(55) = 40 < 42 = φ(43)·2^0`.  Hence `55·2^(k+1)` is a SECOND infinite reversal
-- family, disjoint from `21·2^(k+1)` — the reversal phenomenon is not tied to a
-- single seed.
-- ===========================================================================

theorem totient_55 : Nat.totient 55 = 40 := by decide
theorem totient_35 : Nat.totient 35 = 24 := by decide
theorem totient_43 : Nat.totient 43 = 42 := Nat.totient_prime (by norm_num)

/-- **Second reversal family `55·2^(k+1)`:** odd data `a = 55, b = 35, e = 43, t = 1`,
    and `φ(55) = 40 < 42 = φ(43)·2^0`, so the criterion returns "reversal" for all `k`.
    This is a genuinely new infinite reversal family, distinct from `21·2^(k+1)`. -/
theorem reversal_via_criterion_55 (k : ℕ) : (55 * 2 ^ (k + 1)) ∈ ReversalSet := by
  rw [dblIter_reversal_iff (a := 55) (b := 35) (e := 43) (t := 1)
        (by decide) (by decide) (by decide) (by norm_num)
        (by norm_num [totient_55]) (by norm_num [totient_35]) k]
  norm_num [totient_55, totient_43]

/-- **The reversal seed set contains at least two distinct odd seeds.**  Both
    `21·2^(k+1)` and `55·2^(k+1)` reverse for every `k`, and the seeds `21 ≠ 55`
    are distinct odd numbers.  So `ReversalSet` is not exhausted by the single
    Researcher-3 family `21·2^(k+1)`; reversal seeds form a genuinely larger set,
    the smallest two being `21` and `55`. -/
theorem two_distinct_reversal_families :
    (∀ k, (21 * 2 ^ (k + 1)) ∈ ReversalSet) ∧
    (∀ k, (55 * 2 ^ (k + 1)) ∈ ReversalSet) ∧ (21 : ℕ) ≠ 55 :=
  ⟨reversal_via_criterion, reversal_via_criterion_55, by decide⟩

-- ===========================================================================
-- A COMPUTABLE DECISION PROCEDURE FOR TRANSPORT FAMILIES
-- ---------------------------------------------------------------------------
-- The `k`-free criterion above still asks the caller to *supply* the odd data
-- `(b, e, t)` describing the family.  Here we make the extraction AUTOMATIC:
-- from the single odd seed `a` we COMPUTE, by ordinary `Nat` arithmetic,
--     b = (2a − φ(a))/2,   C = 2a − φ(b),   t = v₂(C),   e = C / 2^t,
-- and package the entire three-way regime of the family `a·2^(k+1)` as one
-- decidable `Ordering`-valued function
--     classify a  =  compare  φ(a)  (φ(e)·2^(t−1)).
-- The only inputs are decidable facts about `a` alone — that the first cototient
-- step has 2-adic valuation exactly one (`Odd (bSeed a)`) and that the landing
-- constant is nonzero and even.  Membership of the whole family in each regime is
-- thereby reduced to a finite computation on `a`, with no per-`k` work and no
-- hand-supplied `(e, t)`.  This is the decision procedure promised by the
-- transport programme; the reversal seeds `21`, `55` are then read off by
-- evaluating `classify`.
-- ===========================================================================

/-- Doubled first cototient step `2a − φ(a)` (equal to `2·bSeed a` on valid seeds). -/
def coStep (a : ℕ) : ℕ := 2 * a - Nat.totient a

/-- The intermediate odd seed `b = (2a − φ(a))/2`. -/
def bSeed (a : ℕ) : ℕ := coStep a / 2

/-- The landing constant `C = 2a − φ(b)`; transport gives `D(a·2^(k+1)) = C·2^k`. -/
def landC (a : ℕ) : ℕ := 2 * a - Nat.totient (bSeed a)

/-- 2-adic valuation `t` of the landing constant, writing `C = e·2^t` with `e` odd. -/
def landT (a : ℕ) : ℕ := (landC a).factorization 2

/-- Odd part `e` of the landing constant, `C = e·2^t`. -/
def landE (a : ℕ) : ℕ := ordCompl[2] (landC a)

/-- **The computable three-way classifier.**  Compares `φ(a)` with `φ(e)·2^(t−1)`
    and returns `.lt` (reversal), `.eq` (equality) or `.gt` (forward). -/
def classify (a : ℕ) : Ordering :=
  compareOfLessAndEq (Nat.totient a) (Nat.totient (landE a) * 2 ^ (landT a - 1))

/-- `compareOfLessAndEq` returns `.lt` exactly on the strict-less relation. -/
theorem coLE_lt {x y : ℕ} : compareOfLessAndEq x y = Ordering.lt ↔ x < y :=
  Batteries.compareOfLessAndEq_eq_lt

/-- `compareOfLessAndEq` returns `.eq` exactly on equality. -/
theorem coLE_eq {x y : ℕ} : compareOfLessAndEq x y = Ordering.eq ↔ x = y := by
  unfold compareOfLessAndEq; split_ifs with h1 h2 <;> (simp_all; try omega)

/-- `compareOfLessAndEq` returns `.gt` exactly on the strict-greater relation. -/
theorem coLE_gt {x y : ℕ} : compareOfLessAndEq x y = Ordering.gt ↔ y < x := by
  unfold compareOfLessAndEq; split_ifs with h1 h2 <;> (simp_all; try omega)

/-- **Extraction is faithful.**  Under the decidable side-conditions on `a`
    (first cototient step even with odd quotient, landing constant nonzero and
    even) the computed data `(bSeed a, landE a, landT a)` satisfies exactly the
    hypotheses required by the `k`-free transport criterion. -/
theorem classify_data {a : ℕ} (hstep : 2 ∣ coStep a) (hC0 : landC a ≠ 0)
    (hCe : 2 ∣ landC a) :
    Odd (landE a) ∧ 1 ≤ landT a ∧
      2 * a - Nat.totient a = 2 * bSeed a ∧
      2 * a - Nat.totient (bSeed a) = landE a * 2 ^ landT a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `e = ordCompl[2] C` is odd: a prime never divides the complementary part
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1
      (Nat.not_dvd_ordCompl Nat.prime_two hC0))
  · -- `t = v₂(C) ≥ 1` since `2 ∣ C ≠ 0`
    exact Nat.prime_two.factorization_pos_of_dvd hC0 hCe
  · -- `2a − φ(a) = 2·bSeed a` because the step is even
    show 2 * a - Nat.totient a = 2 * bSeed a
    have h2 : coStep a = 2 * bSeed a := by
      simp only [bSeed]; exact (Nat.mul_div_cancel' hstep).symm
    exact h2
  · -- `C = e·2^t` is the ordProj/ordCompl split of the landing constant
    show landC a = landE a * 2 ^ landT a
    rw [mul_comm]
    exact (Nat.ordProj_mul_ordCompl_eq_self (landC a) 2).symm

/-- **Decision procedure — reversal branch.**  For any odd seed `a` whose first
    cototient step has 2-adic valuation one and whose landing constant is nonzero
    and even, the *whole* family `a·2^(k+1)` is a reversal family iff the
    computable classifier returns `.lt`. -/
theorem mem_ReversalSet_iff_classify {a : ℕ} (ha : Odd a) (hstep : 2 ∣ coStep a)
    (hb : Odd (bSeed a)) (hC0 : landC a ≠ 0) (hCe : 2 ∣ landC a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ ReversalSet ↔ classify a = Ordering.lt := by
  obtain ⟨he, ht, hst, hC⟩ := classify_data hstep hC0 hCe
  unfold classify
  rw [coLE_lt]
  exact dblIter_reversal_iff ha hb he ht hst hC k

/-- **Decision procedure — equality branch.**  `a·2^(k+1)` lies on the equality
    diagonal for all `k` iff `classify a = .eq`. -/
theorem mem_EqualitySet_iff_classify {a : ℕ} (ha : Odd a) (hstep : 2 ∣ coStep a)
    (hb : Odd (bSeed a)) (hC0 : landC a ≠ 0) (hCe : 2 ∣ landC a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ EqualitySet ↔ classify a = Ordering.eq := by
  obtain ⟨he, ht, hst, hC⟩ := classify_data hstep hC0 hCe
  unfold classify
  rw [coLE_eq]
  exact dblIter_equality_iff ha hb he ht hst hC k

/-- **Decision procedure — forward branch.**  `a·2^(k+1)` is a forward family for
    all `k` iff `classify a = .gt`. -/
theorem mem_ForwardSet_iff_classify {a : ℕ} (ha : Odd a) (hstep : 2 ∣ coStep a)
    (hb : Odd (bSeed a)) (hC0 : landC a ≠ 0) (hCe : 2 ∣ landC a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ ForwardSet ↔ classify a = Ordering.gt := by
  obtain ⟨he, ht, hst, hC⟩ := classify_data hstep hC0 hCe
  unfold classify
  rw [coLE_gt]
  exact dblIter_forward_iff ha hb he ht hst hC k

-- --- Evaluating the classifier at concrete seeds (no `native_decide`) ---

/-- Helper: if the landing constant factors as `C = e·2^t` with `e` odd and
    `t ≥ 1`, then the computed valuation/odd-part are exactly `t` and `e`. -/
theorem landT_landE_of {a e t : ℕ} (he : Odd e)
    (h : landC a = e * 2 ^ t) : landT a = t ∧ landE a = e := by
  have he0 : e ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.1 he) (by decide)
  have hT : landT a = t := by
    unfold landT
    rw [h, Nat.factorization_mul he0 (pow_ne_zero t (by norm_num)), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 he)),
        Nat.factorization_pow_self Nat.prime_two, zero_add]
  refine ⟨hT, ?_⟩
  show landC a / 2 ^ landT a = e
  rw [hT, h, Nat.mul_div_assoc e (dvd_refl (2 ^ t)), Nat.div_self (pow_pos (by norm_num) t),
      mul_one]

theorem totient_11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)
theorem totient_7 : Nat.totient 7 = 6 := Nat.totient_prime (by norm_num)

/-- The classifier evaluated at `a = 21` returns `.lt` (reversal), computing
    `b = 15`, `C = 34 = 17·2^1`, `t = 1`, `e = 17`, and `φ(21) = 12 < 16 = φ(17)`. -/
theorem classify_21 : classify 21 = Ordering.lt := by
  have hb : bSeed 21 = 15 := by unfold bSeed coStep; norm_num [totient_21]
  have hC : landC 21 = 34 := by unfold landC; norm_num [hb, totient_15]
  obtain ⟨hT, hE⟩ := landT_landE_of (a := 21) (e := 17) (t := 1)
    (by decide) (by norm_num [hC])
  unfold classify
  rw [hE, hT, totient_21, totient_17]
  decide

/-- The classifier evaluated at `a = 15` returns `.eq` (equality diagonal):
    `b = 11`, `C = 20 = 5·2^2`, `t = 2`, `e = 5`, and `φ(15) = 8 = 4·2 = φ(5)·2^1`. -/
theorem classify_15 : classify 15 = Ordering.eq := by
  have hb : bSeed 15 = 11 := by unfold bSeed coStep; norm_num [totient_15]
  have hC : landC 15 = 20 := by unfold landC; norm_num [hb, totient_11]
  obtain ⟨hT, hE⟩ := landT_landE_of (a := 15) (e := 5) (t := 2)
    (by decide) (by norm_num [hC])
  unfold classify
  rw [hE, hT, totient_15, totient_5]
  decide

/-- The classifier evaluated at `a = 13` returns `.gt` (forward):
    `b = 7`, `C = 20 = 5·2^2`, `t = 2`, `e = 5`, and `φ(5)·2^1 = 8 < 12 = φ(13)`. -/
theorem classify_13 : classify 13 = Ordering.gt := by
  have hb : bSeed 13 = 7 := by unfold bSeed coStep; norm_num [totient_13]
  have hC : landC 13 = 20 := by unfold landC; norm_num [hb, totient_7]
  obtain ⟨hT, hE⟩ := landT_landE_of (a := 13) (e := 5) (t := 2)
    (by decide) (by norm_num [hC])
  unfold classify
  rw [hE, hT, totient_13, totient_5]
  decide

/-- **The decision procedure decides all three regimes.**  Running the single
    computable classifier on the seeds `21`, `15`, `13` (with all side-conditions
    discharged by `decide`) reproduces the reversal, equality and forward families
    with no hand-supplied `(e, t)` data — the extraction is fully automatic. -/
theorem decision_procedure_classifies :
    (∀ k, (21 * 2 ^ (k + 1)) ∈ ReversalSet) ∧
    (∀ k, (15 * 2 ^ (k + 1)) ∈ EqualitySet) ∧
    (∀ k, (13 * 2 ^ (k + 1)) ∈ ForwardSet) := by
  have hb21 : bSeed 21 = 15 := by unfold bSeed coStep; norm_num [totient_21]
  have hb15 : bSeed 15 = 11 := by unfold bSeed coStep; norm_num [totient_15]
  have hb13 : bSeed 13 = 7 := by unfold bSeed coStep; norm_num [totient_13]
  have hC21 : landC 21 = 34 := by unfold landC; norm_num [hb21, totient_15]
  have hC15 : landC 15 = 20 := by unfold landC; norm_num [hb15, totient_11]
  have hC13 : landC 13 = 20 := by unfold landC; norm_num [hb13, totient_7]
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [mem_ReversalSet_iff_classify (a := 21) (by decide)
        (by unfold coStep; norm_num [totient_21]) (by rw [hb21]; decide)
        (by rw [hC21]; decide) (by rw [hC21]; decide) k]
    exact classify_21
  · rw [mem_EqualitySet_iff_classify (a := 15) (by decide)
        (by unfold coStep; norm_num [totient_15]) (by rw [hb15]; decide)
        (by rw [hC15]; decide) (by rw [hC15]; decide) k]
    exact classify_15
  · rw [mem_ForwardSet_iff_classify (a := 13) (by decide)
        (by unfold coStep; norm_num [totient_13]) (by rw [hb13]; decide)
        (by rw [hC13]; decide) (by rw [hC13]; decide) k]
    exact classify_13
-- ===========================================================================
-- THE EXCLUDED CASE  v₂(2a − φ(a)) > 1  — GENERAL TRANSPORT AND CRITERION
-- ---------------------------------------------------------------------------
-- The transport lemma `dblIter_transport` and the three-way criterion above all
-- require `2a − φ(a) = 2·b` with `b` odd, i.e. the first cototient step has
-- 2-adic valuation EXACTLY `1`.  This excludes every seed with
-- `v₂(2a − φ(a)) ≥ 2` (the smallest being `a = 3, 7, 9, 11, 27, …`).  We remove
-- that restriction.
--
-- Write the first step as `2a − φ(a) = 2^s · b` with `b` odd and `s ≥ 1`.  Then
-- along `n = a·2^(k+1)`:
--   • `n − φ(n) = (2a − φ(a))·2^k = b·2^(k+s)` has valuation `k + s`, so
--   • `φ(n − φ(n)) = φ(b)·2^(k+s−1)`, whence
--   • `D(n) = a·2^(k+1) − φ(b)·2^(k+s−1) = (2a − φ(b)·2^(s−1))·2^k`.
-- So the landing constant is `C = 2a − φ(b)·2^(s−1)` (for `s = 1` this is the old
-- `2a − φ(b)`, recovering `dblIter_transport`).  Decomposing `C = e·2^t` (`e`
-- odd, `t ≥ 1`) the criterion again reads off the regime from `φ(a) ⋛ φ(e)·2^(t−1)`.
--
-- A structural surprise the general criterion makes visible: among the excluded
-- seeds `a < 120` only the EQUALITY and FORWARD regimes occur — no excluded seed
-- reverses.  We realise both regimes explicitly (`a = 3, 9` equality; `a = 7, 27`
-- forward), giving genuinely new infinite families outside the reach of the
-- `s = 1` criterion.
-- ===========================================================================

/-- **General transport (arbitrary first-step 2-adic valuation).**  Drops the
    `v₂(2a − φ(a)) = 1` restriction of `dblIter_transport`: with `a, b` odd,
    `s ≥ 1`, and the first cototient step `2a − φ(a) = 2^s · b`, the double
    iterate along `n = a·2^(k+1)` is `D(n) = (2a − φ(b)·2^(s−1)) · 2^k`.
    For `s = 1` this is exactly `dblIter_transport`. -/
theorem dblIter_transport_general {a b s : ℕ} (ha : Odd a) (hb : Odd b) (hs : 1 ≤ s)
    (hstep : 2 * a - Nat.totient a = 2 ^ s * b) (k : ℕ) :
    dblIter (a * 2 ^ (k + 1)) = (2 * a - Nat.totient b * 2 ^ (s - 1)) * 2 ^ k := by
  -- odd ⇒ coprime to every power of two
  have oddCop : ∀ (c m : ℕ), Odd c → Nat.Coprime c (2 ^ m) := by
    intro c m hc
    have h2 : ¬ (2 ∣ c) := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      have := Nat.odd_iff.mp hc; omega
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm.pow_right m
  have hp2 : ∀ m : ℕ, Nat.totient (2 ^ (m + 1)) = 2 ^ m := by
    intro m; rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]; simp
  -- φ(n) = φ(a)·2^k
  have hφn : Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k := by
    rw [Nat.totient_mul (oddCop a (k + 1) ha), hp2 k]
  -- first cototient step lands on b·2^(k+s)  (valuation k+s, not k+1)
  have step1 : a * 2 ^ (k + 1) - Nat.totient a * 2 ^ k = b * 2 ^ (k + s) := by
    have e1 : a * 2 ^ (k + 1) = (2 * a) * 2 ^ k := by rw [pow_succ]; ring
    rw [e1, ← Nat.sub_mul, hstep, pow_add]; ring
  -- φ(2^(k+s)) = 2^(k+s−1)  (k+s ≥ 1 since s ≥ 1)
  have hφ2ks : Nat.totient (2 ^ (k + s)) = 2 ^ (k + s - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, k + s = m + 1 := ⟨k + s - 1, by omega⟩
    rw [hm, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]; simp
  have hφstep : Nat.totient (b * 2 ^ (k + s)) = Nat.totient b * 2 ^ (k + s - 1) := by
    rw [Nat.totient_mul (oddCop b (k + s) hb), hφ2ks]
  unfold dblIter
  rw [hφn, step1, hφstep]
  -- a·2^(k+1) − φ(b)·2^(k+s−1) = (2a − φ(b)·2^(s−1))·2^k
  have e1 : a * 2 ^ (k + 1) = (2 * a) * 2 ^ k := by rw [pow_succ]; ring
  have e2 : Nat.totient b * 2 ^ (k + s - 1)
      = (Nat.totient b * 2 ^ (s - 1)) * 2 ^ k := by
    rw [show k + s - 1 = (s - 1) + k from by omega, pow_add]; ring
  rw [e1, e2, ← Nat.sub_mul]

/-- The `s = 1` restriction `dblIter_transport` is the special case of the general
    lemma: with `2a − φ(a) = 2·b = 2^1·b`, the landing `2a − φ(b)·2^0 = 2a − φ(b)`. -/
theorem dblIter_transport_of_general {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (hstep : 2 * a - Nat.totient a = 2 * b) (k : ℕ) :
    dblIter (a * 2 ^ (k + 1)) = (2 * a - Nat.totient b) * 2 ^ k := by
  have h := dblIter_transport_general ha hb (le_refl 1)
    (by rw [pow_one]; exact hstep) k
  simpa using h

/-- **k-independent totient values, general first-step valuation.**  With
    `2a − φ(a) = 2^s·b` (`s ≥ 1`, `b` odd) and the landing constant
    `C = 2a − φ(b)·2^(s−1) = e·2^t` (`e` odd, `t ≥ 1`), both totients along
    `n = a·2^(k+1)` factor through a common `2^k`:
    `φ(n) = φ(a)·2^k` and `φ(D(n)) = φ(e)·2^(t−1)·2^k`. -/
theorem dblIter_totient_values_general {a b e s t : ℕ}
    (ha : Odd a) (hb : Odd b) (he : Odd e) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 ^ s * b)
    (hC : 2 * a - Nat.totient b * 2 ^ (s - 1) = e * 2 ^ t) (k : ℕ) :
    Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k ∧
    Nat.totient (dblIter (a * 2 ^ (k + 1)))
      = Nat.totient e * 2 ^ (t - 1) * 2 ^ k := by
  have oddCop : ∀ (c m : ℕ), Odd c → Nat.Coprime c (2 ^ m) := by
    intro c m hc
    have h2 : ¬ (2 ∣ c) := by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      have := Nat.odd_iff.mp hc; omega
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm.pow_right m
  have hp2 : ∀ m : ℕ, Nat.totient (2 ^ (m + 1)) = 2 ^ m := by
    intro m; rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]; simp
  have hφn : Nat.totient (a * 2 ^ (k + 1)) = Nat.totient a * 2 ^ k := by
    rw [Nat.totient_mul (oddCop a (k + 1) ha), hp2 k]
  refine ⟨hφn, ?_⟩
  have hD : dblIter (a * 2 ^ (k + 1)) = e * 2 ^ (t + k) := by
    rw [dblIter_transport_general ha hb hs hstep k, hC, pow_add]; ring
  have hφe2 : Nat.totient (2 ^ (t + k)) = 2 ^ (t + k - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, t + k = m + 1 := ⟨t + k - 1, by omega⟩
    rw [hm, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]; simp
  rw [hD, Nat.totient_mul (oddCop e (t + k) he), hφe2]
  rw [show t + k - 1 = (t - 1) + k from by omega, pow_add, ← mul_assoc]

/-- **General reversal criterion** (excluded case `v₂(2a − φ(a)) ≥ 1` arbitrary):
    `φ(n) < φ(D(n))` for `n = a·2^(k+1)` iff `φ(a) < φ(e)·2^(t−1)`. -/
theorem dblIter_reversal_iff_general {a b e s t : ℕ}
    (ha : Odd a) (hb : Odd b) (he : Odd e) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 ^ s * b)
    (hC : 2 * a - Nat.totient b * 2 ^ (s - 1) = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ ReversalSet
      ↔ Nat.totient a < Nat.totient e * 2 ^ (t - 1) := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values_general ha hb he hs ht hstep hC k
  show Nat.totient (a * 2 ^ (k + 1))
      < Nat.totient (dblIter (a * 2 ^ (k + 1))) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  · intro h; exact mul_lt_mul_of_pos_right h hpos

/-- **General equality criterion.**  `φ(n) = φ(D(n))` for `n = a·2^(k+1)` iff
    `φ(a) = φ(e)·2^(t−1)`. -/
theorem dblIter_equality_iff_general {a b e s t : ℕ}
    (ha : Odd a) (hb : Odd b) (he : Odd e) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 ^ s * b)
    (hC : 2 * a - Nat.totient b * 2 ^ (s - 1) = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ EqualitySet
      ↔ Nat.totient a = Nat.totient e * 2 ^ (t - 1) := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values_general ha hb he hs ht hstep hC k
  show Nat.totient (a * 2 ^ (k + 1))
      = Nat.totient (dblIter (a * 2 ^ (k + 1))) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact Nat.eq_of_mul_eq_mul_right hpos h
  · intro h; rw [h]

/-- **General forward criterion.**  `φ(D(n)) < φ(n)` for `n = a·2^(k+1)` iff
    `φ(e)·2^(t−1) < φ(a)`. -/
theorem dblIter_forward_iff_general {a b e s t : ℕ}
    (ha : Odd a) (hb : Odd b) (he : Odd e) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hstep : 2 * a - Nat.totient a = 2 ^ s * b)
    (hC : 2 * a - Nat.totient b * 2 ^ (s - 1) = e * 2 ^ t) (k : ℕ) :
    (a * 2 ^ (k + 1)) ∈ ForwardSet
      ↔ Nat.totient e * 2 ^ (t - 1) < Nat.totient a := by
  obtain ⟨h1, h2⟩ := dblIter_totient_values_general ha hb he hs ht hstep hC k
  show Nat.totient (dblIter (a * 2 ^ (k + 1)))
      < Nat.totient (a * 2 ^ (k + 1)) ↔ _
  rw [h1, h2]
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · intro h; exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  · intro h; exact mul_lt_mul_of_pos_right h hpos

-- --- Concrete new families from EXCLUDED seeds (v₂(2a − φ(a)) ≥ 2) ---

theorem totient_3 : Nat.totient 3 = 2 := Nat.totient_prime (by norm_num)
-- (`totient_7` is already proved above in the transport-families section.)
theorem totient_9 : Nat.totient 9 = 6 := by decide
theorem totient_27 : Nat.totient 27 = 18 := by decide

/-- **Excluded equality family `3·2^(k+1)` (`s = 2`, `b = e = 1`, `t = 2`).**
    Here `2·3 − φ(3) = 4 = 2^2·1` (valuation `2`, outside the `s = 1` criterion),
    the landing constant is `2·3 − φ(1)·2^1 = 4 = 1·2^2`, and `φ(3) = 2 = φ(1)·2^1`,
    so every member lies on the equality diagonal.  This is the bottom `e = 1`
    excluded family. -/
theorem mem_EqualitySet_three (k : ℕ) : 3 * 2 ^ (k + 1) ∈ EqualitySet := by
  rw [dblIter_equality_iff_general (a := 3) (b := 1) (e := 1) (s := 2) (t := 2)
        (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
        (by norm_num [totient_3]) (by norm_num [Nat.totient_one]) k]
  norm_num [totient_3, Nat.totient_one]

/-- **Excluded equality family `9·2^(k+1)` (`s = 2`, `b = 3`, `e = 7`, `t = 1`).**
    `2·9 − φ(9) = 12 = 2^2·3` (valuation `2`), landing `2·9 − φ(3)·2^1 = 14 = 7·2^1`,
    and `φ(9) = 6 = 6·2^0 = φ(7)·2^0`, so `9·2^(k+1)` is an equality family the
    original `s = 1` criterion cannot express. -/
theorem mem_EqualitySet_nine (k : ℕ) : 9 * 2 ^ (k + 1) ∈ EqualitySet := by
  rw [dblIter_equality_iff_general (a := 9) (b := 3) (e := 7) (s := 2) (t := 1)
        (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
        (by norm_num [totient_9]) (by norm_num [totient_3]) k]
  norm_num [totient_9, totient_7]

/-- **Excluded forward family `7·2^(k+1)` (`s = 3`, `b = 1`, `e = 5`, `t = 1`).**
    A higher-valuation demonstrator: `2·7 − φ(7) = 8 = 2^3·1` (valuation `3`),
    landing `2·7 − φ(1)·2^2 = 10 = 5·2^1`, and `φ(5)·2^0 = 4 < 6 = φ(7)`, so every
    member is a forward point. -/
theorem mem_ForwardSet_seven (k : ℕ) : 7 * 2 ^ (k + 1) ∈ ForwardSet := by
  rw [dblIter_forward_iff_general (a := 7) (b := 1) (e := 5) (s := 3) (t := 1)
        (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
        (by norm_num [totient_7]) (by norm_num [Nat.totient_one]) k]
  norm_num [totient_7, totient_5]

/-- **Excluded forward family `27·2^(k+1)` (`s = 2`, `b = 9`, `e = 21`, `t = 1`).**
    `2·27 − φ(27) = 36 = 2^2·9` (valuation `2`), landing `2·27 − φ(9)·2^1 = 42 = 21·2^1`,
    and `φ(21)·2^0 = 12 < 18 = φ(27)`, so `27·2^(k+1)` is a forward family outside
    the `s = 1` criterion. -/
theorem mem_ForwardSet_twentyseven (k : ℕ) : 27 * 2 ^ (k + 1) ∈ ForwardSet := by
  rw [dblIter_forward_iff_general (a := 27) (b := 9) (e := 21) (s := 2) (t := 1)
        (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
        (by norm_num [totient_27]) (by norm_num [totient_9]) k]
  norm_num [totient_27, totient_21]

/-- **The excluded case realises both the equality and forward regimes.**  The
    seeds `3, 9` (equality) and `7, 27` (forward) all have `v₂(2a − φ(a)) ≥ 2`, so
    they lie entirely outside the reach of the `s = 1` criterion
    (`dblIter_*_iff`); the general criterion classifies them uniformly.  No
    excluded seed `a < 120` reverses — among `v₂(2a − φ(a)) ≥ 2` only equality and
    forward occur — so this pair of witnesses covers every excluded regime found. -/
theorem excluded_seeds_realize_equality_and_forward :
    (∀ k, 3 * 2 ^ (k + 1) ∈ EqualitySet) ∧
    (∀ k, 9 * 2 ^ (k + 1) ∈ EqualitySet) ∧
    (∀ k, 7 * 2 ^ (k + 1) ∈ ForwardSet) ∧
    (∀ k, 27 * 2 ^ (k + 1) ∈ ForwardSet) :=
  ⟨mem_EqualitySet_three, mem_EqualitySet_nine,
   mem_ForwardSet_seven, mem_ForwardSet_twentyseven⟩

-- ===========================================================================
-- THE SMALLEST ODD REVERSAL SEED IS 21
-- ---------------------------------------------------------------------------
-- Now that `classify` is a genuine computable function on the single odd seed,
-- we can settle a structural question the per-`k` families left open: *which*
-- odd seed is the smallest whose transport family `a·2^(k+1)` reverses.  A seed
-- `a` is admissible for the classifier ("valid") exactly when the transport
-- hypotheses hold: `a` odd, the first cototient step `2a−φ(a)` has 2-adic
-- valuation one (`bSeed a` odd), and the landing constant is nonzero and even.
-- Sweeping the odd valid seeds below 21 shows only `5, 13, 15, 17` are valid,
-- and they classify as `eq, gt, eq, gt` — none reverse — whereas `classify 21`
-- is `.lt`.  Hence 21 is the least odd reversal seed.  The whole sweep stays
-- kernel-`decide`-only (no `native_decide`, no `factorization` reduction): the
-- validity test uses only `φ`, and the four surviving seeds are evaluated
-- through the `landT_landE_of` rewriting helper.
-- ===========================================================================

/-- A seed `a` is *valid* for the transport classifier when it is odd, its first
    cototient step `2a − φ(a)` has 2-adic valuation exactly one (equivalently
    `bSeed a` is odd), and its landing constant is nonzero and even.  These are
    precisely the side-conditions under which `classify a` faithfully decides the
    regime of the family `a·2^(k+1)`. -/
def ValidSeed (a : ℕ) : Prop :=
  Odd a ∧ 2 ∣ coStep a ∧ Odd (bSeed a) ∧ landC a ≠ 0 ∧ 2 ∣ landC a

instance : DecidablePred ValidSeed := fun a => by unfold ValidSeed; infer_instance

/-- `classify 5 = .eq`: `b = 3`, `C = 8 = 1·2^3`, `t = 3`, `e = 1`, and
    `φ(5) = 4 = 1·2^2 = φ(1)·2^(t−1)`. -/
theorem classify_5 : classify 5 = Ordering.eq := by
  have hb : bSeed 5 = 3 := by unfold bSeed coStep; norm_num [totient_5]
  have hC : landC 5 = 8 := by unfold landC; norm_num [hb, totient_3]
  obtain ⟨hT, hE⟩ := landT_landE_of (a := 5) (e := 1) (t := 3)
    (by decide) (by norm_num [hC])
  unfold classify
  rw [hE, hT, totient_5, Nat.totient_one]
  decide

/-- `classify 17 = .gt`: `b = 9`, `C = 28 = 7·2^2`, `t = 2`, `e = 7`, and
    `φ(7)·2^(t−1) = 6·2 = 12 < 16 = φ(17)`. -/
theorem classify_17 : classify 17 = Ordering.gt := by
  have hb : bSeed 17 = 9 := by unfold bSeed coStep; norm_num [totient_17]
  have hC : landC 17 = 28 := by unfold landC; norm_num [hb, totient_9]
  obtain ⟨hT, hE⟩ := landT_landE_of (a := 17) (e := 7) (t := 2)
    (by decide) (by norm_num [hC])
  unfold classify
  rw [hE, hT, totient_17, totient_7]
  decide

/-- **21 is the smallest odd reversal seed (classifier form).**  `classify 21`
    is `.lt`, while every valid seed `a < 21` is classified `.eq` or `.gt`.  The
    only valid seeds below 21 are `5, 13, 15, 17`; all invalid `a < 21` fail the
    validity test decidably (the sweep only touches `φ`, never `factorization`). -/
theorem twentyone_least_reversal_seed :
    classify 21 = Ordering.lt ∧
    ∀ a, a < 21 → ValidSeed a → classify a ≠ Ordering.lt := by
  refine ⟨classify_21, fun a ha hv => ?_⟩
  interval_cases a <;>
    try (exact absurd hv (by decide))
  · rw [classify_5]; decide
  · rw [classify_13]; decide
  · rw [classify_15]; decide
  · rw [classify_17]; decide

/-- **21 is the smallest odd reversal seed (family form).**  The family
    `21·2^(k+1)` reverses for every `k`, while for every valid odd seed `a < 21`
    and every `k` the family `a·2^(k+1)` does *not* reverse.  This is the
    structural sharpening promised once the per-seed test became computable:
    among transport-admissible odd seeds, 21 is the least whose family lands in
    the reversal regime `φ(D(n)) > φ(n)`. -/
theorem least_reversal_seed_families :
    (∀ k, 21 * 2 ^ (k + 1) ∈ ReversalSet) ∧
    ∀ a, a < 21 → ValidSeed a → ∀ k, a * 2 ^ (k + 1) ∉ ReversalSet := by
  refine ⟨decision_procedure_classifies.1, fun a ha hv k => ?_⟩
  obtain ⟨ha_odd, hstep, hb, hC0, hCe⟩ := hv
  rw [mem_ReversalSet_iff_classify ha_odd hstep hb hC0 hCe k]
  exact twentyone_least_reversal_seed.2 a ha ⟨ha_odd, hstep, hb, hC0, hCe⟩
-- ===========================================================================
-- A TOTAL DECIDABLE CLASSIFIER FOR EVERY ODD SEED
--
-- The general criterion `dblIter_*_iff_general` decides the regime of the family
-- `n = a·2^(k+1)` from data `(s, b, t, e)` that must be *supplied* by hand for
-- each seed.  Here we make that data COMPUTABLE: `seedS/seedB/seedC/seedT/seedE`
-- extract `(s, b, t, e)` from `a` by two 2-adic valuations, and `classifySeed a`
-- reads off the regime.  `seed_spec` proves the extracted data satisfies every
-- hypothesis of the general criterion for arbitrary odd `a ≥ 3`, so the three
-- `classifySeed_*_iff` corollaries turn the whole trichotomy into a single
-- decision procedure — the reversal seed set is `{a | classifySeed a = .lt}`.
-- ===========================================================================

/-- First-step 2-adic valuation `s = v₂(2a − φ(a))`. -/
def seedS (a : ℕ) : ℕ := (2 * a - Nat.totient a).factorization 2

/-- Odd part `b` of the first cototient step: `2a − φ(a) = 2^s · b`. -/
def seedB (a : ℕ) : ℕ := (2 * a - Nat.totient a) / 2 ^ seedS a

/-- Landing constant `C = 2a − φ(b)·2^(s−1)` (the double iterate `D(a·2^(k+1))`
    equals `C·2^k`). -/
def seedC (a : ℕ) : ℕ := 2 * a - Nat.totient (seedB a) * 2 ^ (seedS a - 1)

/-- Second 2-adic valuation `t = v₂(C)`. -/
def seedT (a : ℕ) : ℕ := (seedC a).factorization 2

/-- Odd part `e` of the landing constant: `C = 2^t · e`. -/
def seedE (a : ℕ) : ℕ := seedC a / 2 ^ seedT a

/-- **Total classifier.**  Compares `φ(a)` with `φ(e)·2^(t−1)`; for every odd
    `a ≥ 3` this decides which regime the whole family `n = a·2^(k+1)` lands in:
    `lt` = reversal `φ(n) < φ(D(n))`, `eq` = equality, `gt` = forward. -/
def classifySeed (a : ℕ) : Ordering :=
  compare (Nat.totient a) (Nat.totient (seedE a) * 2 ^ (seedT a - 1))

/-- **Correctness of the extraction.**  For odd `a ≥ 3` the computed data
    `(seedS a, seedB a, seedT a, seedE a)` satisfies every hypothesis of the
    general transport criterion: `b, e` are odd, `s, t ≥ 1`, and the two defining
    2-adic factorisations hold.  (Oddness of `a` is not needed here — it enters
    only through the family's coprimality in the criterion below.) -/
theorem seed_spec {a : ℕ} (ha3 : 3 ≤ a) :
    Odd (seedB a) ∧ Odd (seedE a) ∧ 1 ≤ seedS a ∧ 1 ≤ seedT a ∧
    2 * a - Nat.totient a = 2 ^ seedS a * seedB a ∧
    2 * a - Nat.totient (seedB a) * 2 ^ (seedS a - 1) = seedE a * 2 ^ seedT a := by
  simp only [seedS, seedB, seedC, seedT, seedE]
  have ha1 : 1 < a := by omega
  have hφa_lt : Nat.totient a < a := Nat.totient_lt a ha1
  obtain ⟨j, hj⟩ := Nat.totient_even (show 2 < a by omega)
  have hφa_pos : 0 < Nat.totient a := Nat.totient_pos.mpr (by omega)
  set m := 2 * a - Nat.totient a with hm
  have hm_ne : m ≠ 0 := by omega
  have hm_dvd : 2 ∣ m := ⟨a - j, by omega⟩
  set s := m.factorization 2 with hs
  set b := m / 2 ^ s with hb
  have hs1 : 1 ≤ s := by
    have h := Nat.prime_two.factorization_pos_of_dvd hm_ne hm_dvd
    rw [← hs] at h; omega
  -- 2^s · b = m  and  b odd, both from the 2-adic decomposition of m
  have hsb : 2 ^ s * b = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hob : Odd b := by
    have hnd : ¬ 2 ∣ b := Nat.not_dvd_ordCompl Nat.prime_two hm_ne
    exact Nat.odd_iff.mpr (by omega)
  -- 2^s = 2·2^(s−1) so b·2^(s−1) is exactly m/2
  have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
    conv_lhs => rw [show s = (s - 1) + 1 from by omega, pow_succ]
    ring
  have hbpow : 2 * (b * 2 ^ (s - 1)) = m := by rw [← hsb, h2s]; ring
  have hmul_le : Nat.totient b * 2 ^ (s - 1) ≤ b * 2 ^ (s - 1) := by
    gcongr
    exact Nat.totient_le b
  have hterm_le : Nat.totient b * 2 ^ (s - 1) ≤ a - 1 := by omega
  -- the landing term is even (hence C is even, with v₂ ≥ 1)
  have hterm_dvd : 2 ∣ Nat.totient b * 2 ^ (s - 1) := by
    rcases hs1.lt_or_eq with hs_gt | hs_eq
    · exact (dvd_pow_self 2 (show s - 1 ≠ 0 by omega)).mul_left _
    · -- s = 1: then b ≠ 1 (else m = 2 contradicts a ≥ 3), so b ≥ 3 and φ(b) is even
      have hb_ne1 : b ≠ 1 := by
        intro hb1
        have hval : (2 : ℕ) ^ s * b = 2 := by rw [← hs_eq, hb1]; norm_num
        rw [hsb] at hval; omega
      have hb3 : 2 < b := by rcases hob with ⟨i, hi⟩; omega
      rw [← hs_eq]
      simpa using (Nat.totient_even hb3).two_dvd
  set C := 2 * a - Nat.totient b * 2 ^ (s - 1) with hC
  have hC_ne : C ≠ 0 := by omega
  have hC_dvd : 2 ∣ C := by omega
  set t := C.factorization 2 with ht
  set e := C / 2 ^ t with he
  have ht1 : 1 ≤ t := by
    have h := Nat.prime_two.factorization_pos_of_dvd hC_ne hC_dvd
    rw [← ht] at h; omega
  have hst : 2 ^ t * e = C := Nat.ordProj_mul_ordCompl_eq_self C 2
  have hoe : Odd e := by
    have hnd : ¬ 2 ∣ e := Nat.not_dvd_ordCompl Nat.prime_two hC_ne
    exact Nat.odd_iff.mpr (by omega)
  have hCeq : C = e * 2 ^ t := by rw [← hst]; ring
  exact ⟨hob, hoe, hs1, ht1, hsb.symm, hCeq⟩

/-- **The classifier decides reversal.**  For odd `a ≥ 3`, `φ(n) < φ(D(n))` along
    `n = a·2^(k+1)` iff `classifySeed a = .lt`. -/
theorem classifySeed_lt_iff {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ ReversalSet ↔ classifySeed a = Ordering.lt := by
  obtain ⟨hob, hoe, hs1, ht1, hstep, hCeq⟩ := seed_spec ha3
  rw [dblIter_reversal_iff_general ha hob hoe hs1 ht1 hstep hCeq k]
  exact compare_lt_iff_lt.symm

/-- **The classifier decides equality.** -/
theorem classifySeed_eq_iff {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ EqualitySet ↔ classifySeed a = Ordering.eq := by
  obtain ⟨hob, hoe, hs1, ht1, hstep, hCeq⟩ := seed_spec ha3
  rw [dblIter_equality_iff_general ha hob hoe hs1 ht1 hstep hCeq k]
  exact compare_eq_iff_eq.symm

/-- **The classifier decides the forward regime.** -/
theorem classifySeed_gt_iff {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) (k : ℕ) :
    a * 2 ^ (k + 1) ∈ ForwardSet ↔ classifySeed a = Ordering.gt := by
  obtain ⟨hob, hoe, hs1, ht1, hstep, hCeq⟩ := seed_spec ha3
  rw [dblIter_forward_iff_general ha hob hoe hs1 ht1 hstep hCeq k]
  exact compare_gt_iff_gt.symm

/-- **Total trichotomy.**  For every odd `a ≥ 3` the computable `classifySeed a`
    correctly decides the regime of the whole family `n = a·2^(k+1)` — a single
    decision procedure covering all seeds, `k`-free and with no restriction on the
    first-step 2-adic valuation.  In particular the reversal seed set is the
    decidable predicate `{a | classifySeed a = Ordering.lt}`. -/
theorem classifySeed_classifies {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) (k : ℕ) :
    (a * 2 ^ (k + 1) ∈ ReversalSet ↔ classifySeed a = Ordering.lt) ∧
    (a * 2 ^ (k + 1) ∈ EqualitySet ↔ classifySeed a = Ordering.eq) ∧
    (a * 2 ^ (k + 1) ∈ ForwardSet ↔ classifySeed a = Ordering.gt) :=
  ⟨classifySeed_lt_iff ha ha3 k, classifySeed_eq_iff ha ha3 k, classifySeed_gt_iff ha ha3 k⟩

-- ===========================================================================
-- SMALLEST REVERSING ODD SEED:  a = 21
-- ---------------------------------------------------------------------------
-- The classifier `classifySeed` is a total computable function, so the reversal
-- seed set `{odd a ≥ 3 | classifySeed a = .lt}` is a genuine decidable predicate.
-- Here we settle its least element: `21` is the smallest odd seed whose family
-- `21·2^(k+1)` reverses (`φ(n) < φ(D(n))` for all `k`); every odd seed
-- `3 ≤ a < 21` classifies to `.eq` or `.gt`, so generates no reversal.  This is a
-- finite `decide`-sweep enabled entirely by the computability of `classifySeed`
-- (no `native_decide`: the two 2-adic valuations are evaluated through the
-- factorisation-split helper below, so the whole result is kernel-checked).
-- ---------------------------------------------------------------------------

/-- **Factorisation split.**  If `n = c·2^u` with `c` odd then the 2-adic
    valuation `n.factorization 2` is exactly `u` and the odd part
    `n / 2^(n.factorization 2)` is exactly `c`.  This is the computable content
    of `seedS/seedB` (applied to `2a − φ(a)`) and of `seedT/seedE` (applied to
    the landing constant `seedC a`). -/
theorem factor_two_split {n c u : ℕ} (hc : Odd c) (h : n = c * 2 ^ u) :
    n.factorization 2 = u ∧ n / 2 ^ (n.factorization 2) = c := by
  have hc0 : c ≠ 0 := by rintro rfl; exact absurd (Nat.odd_iff.1 hc) (by decide)
  have hT : n.factorization 2 = u := by
    rw [h, Nat.factorization_mul hc0 (pow_ne_zero u (by norm_num)), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hc)),
        Nat.factorization_pow_self Nat.prime_two, zero_add]
  refine ⟨hT, ?_⟩
  rw [hT, h, Nat.mul_div_assoc c (dvd_refl (2 ^ u)), Nat.div_self (pow_pos (by norm_num) u),
      mul_one]

/-- **Evaluating `classifySeed` at a concrete seed.**  Given the two 2-adic
    factorisations `2a − φ(a) = b·2^s` (with `b` odd) and the landing split
    `2a − φ(b)·2^(s−1) = e·2^t` (with `e` odd), the classifier reduces to the
    single comparison `φ(a) ⋛ φ(e)·2^(t−1)`.  All extraction steps are discharged
    by `factor_two_split`. -/
theorem classifySeed_val {a s b t e : ℕ} (hob : Odd b) (hoe : Odd e)
    (hstep : 2 * a - Nat.totient a = b * 2 ^ s)
    (hCval : 2 * a - Nat.totient b * 2 ^ (s - 1) = e * 2 ^ t) :
    classifySeed a = compare (Nat.totient a) (Nat.totient e * 2 ^ (t - 1)) := by
  have hS : seedS a = s := (factor_two_split hob hstep).1
  have hB : seedB a = b := (factor_two_split hob hstep).2
  have hSC : seedC a = e * 2 ^ t := by
    show 2 * a - Nat.totient (seedB a) * 2 ^ (seedS a - 1) = e * 2 ^ t
    rw [hB, hS]; exact hCval
  have hT : seedT a = t := (factor_two_split hoe hSC).1
  have hE : seedE a = e := (factor_two_split hoe hSC).2
  show compare (Nat.totient a) (Nat.totient (seedE a) * 2 ^ (seedT a - 1))
      = compare (Nat.totient a) (Nat.totient e * 2 ^ (t - 1))
  rw [hE, hT]

theorem totient_19 : Nat.totient 19 = 18 := Nat.totient_prime (by norm_num)

-- The nine odd seeds `3 ≤ a < 21`: each classifies to `.eq` or `.gt`, never `.lt`.
theorem classifySeed_3 : classifySeed 3 = Ordering.eq := by
  rw [classifySeed_val (s := 2) (b := 1) (t := 2) (e := 1) (by decide) (by decide)
      (by norm_num [totient_3]) (by norm_num [Nat.totient_one])]
  rw [totient_3, Nat.totient_one]; decide

theorem classifySeed_5 : classifySeed 5 = Ordering.eq := by
  rw [classifySeed_val (s := 1) (b := 3) (t := 3) (e := 1) (by decide) (by decide)
      (by norm_num [totient_5]) (by norm_num [totient_3])]
  rw [totient_5, Nat.totient_one]; decide

theorem classifySeed_7 : classifySeed 7 = Ordering.gt := by
  rw [classifySeed_val (s := 3) (b := 1) (t := 1) (e := 5) (by decide) (by decide)
      (by norm_num [totient_7]) (by norm_num [Nat.totient_one])]
  rw [totient_7, totient_5]; decide

theorem classifySeed_9 : classifySeed 9 = Ordering.eq := by
  rw [classifySeed_val (s := 2) (b := 3) (t := 1) (e := 7) (by decide) (by decide)
      (by norm_num [totient_9]) (by norm_num [totient_3])]
  rw [totient_9, totient_7]; decide

theorem classifySeed_11 : classifySeed 11 = Ordering.gt := by
  rw [classifySeed_val (s := 2) (b := 3) (t := 1) (e := 9) (by decide) (by decide)
      (by norm_num [totient_11]) (by norm_num [totient_3])]
  rw [totient_11, totient_9]; decide

theorem classifySeed_13 : classifySeed 13 = Ordering.gt := by
  rw [classifySeed_val (s := 1) (b := 7) (t := 2) (e := 5) (by decide) (by decide)
      (by norm_num [totient_13]) (by norm_num [totient_7])]
  rw [totient_13, totient_5]; decide

theorem classifySeed_15 : classifySeed 15 = Ordering.eq := by
  rw [classifySeed_val (s := 1) (b := 11) (t := 2) (e := 5) (by decide) (by decide)
      (by norm_num [totient_15]) (by norm_num [totient_11])]
  rw [totient_15, totient_5]; decide

theorem classifySeed_17 : classifySeed 17 = Ordering.gt := by
  rw [classifySeed_val (s := 1) (b := 9) (t := 2) (e := 7) (by decide) (by decide)
      (by norm_num [totient_17]) (by norm_num [totient_9])]
  rw [totient_17, totient_7]; decide

theorem classifySeed_19 : classifySeed 19 = Ordering.gt := by
  rw [classifySeed_val (s := 2) (b := 5) (t := 1) (e := 15) (by decide) (by decide)
      (by norm_num [totient_19]) (by norm_num [totient_5])]
  rw [totient_19, totient_15]; decide

/-- The smallest reversing seed, `a = 21`: `b = 15`, `C = 34 = 17·2`, `t = 1`,
    `e = 17`, and `φ(21) = 12 < 16 = φ(17)·2^0`. -/
theorem classifySeed_21' : classifySeed 21 = Ordering.lt := by
  rw [classifySeed_val (s := 1) (b := 15) (t := 1) (e := 17) (by decide) (by decide)
      (by norm_num [totient_21]) (by norm_num [totient_15])]
  rw [totient_21, totient_17]; decide

/-- **`21` is the smallest odd reversing seed.**  The family `21·2^(k+1)` reverses
    (`φ(n) < φ(D(n))`) for every `k`, while for every odd `a` with `3 ≤ a < 21`
    the family `a·2^(k+1)` never reverses.  Equivalently, `21` is the least element
    of the decidable reversal seed set `{odd a ≥ 3 | classifySeed a = .lt}`.  The
    proof is a finite `decide`-sweep over the nine odd seeds `3,5,…,19`, each
    classified to `.eq`/`.gt` through the computable `classifySeed`. -/
theorem twentyone_smallest_reversing_seed :
    (∀ k, 21 * 2 ^ (k + 1) ∈ ReversalSet) ∧
    (∀ a, Odd a → 3 ≤ a → a < 21 → ∀ k, a * 2 ^ (k + 1) ∉ ReversalSet) := by
  refine ⟨fun k => (classifySeed_lt_iff (by decide) (by norm_num) k).mpr classifySeed_21',
    fun a ha h3 hlt k => ?_⟩
  rw [classifySeed_lt_iff ha h3 k]
  interval_cases a <;>
    first
      | exact absurd ha (by decide)
      | (rw [classifySeed_3]; decide)
      | (rw [classifySeed_5]; decide)
      | (rw [classifySeed_7]; decide)
      | (rw [classifySeed_9]; decide)
      | (rw [classifySeed_11]; decide)
      | (rw [classifySeed_13]; decide)
      | (rw [classifySeed_15]; decide)
      | (rw [classifySeed_17]; decide)
      | (rw [classifySeed_19]; decide)

-- ---------------------------------------------------------------------------
-- CLOSED-FORM CONGRUENCE FOR THE FIRST-STEP VALUATION REGIME
-- ---------------------------------------------------------------------------
-- The seed classifier splits odd seeds by `seedS a = v₂(2a − φ(a))`: the value
-- `seedS a = 1` is the *transport-admissible* regime handled by the whole
-- `dblIter_transport` machinery, while `seedS a ≥ 2` is the *excluded* regime
-- (seeds 3,7,9,11,19,27,… — a = p^k with p ≡ 3 mod 4).  Prior work computed
-- `seedS a` by an explicit 2-adic factorisation.  Here we give a closed-form
-- *congruence* criterion: the regime is read directly off `φ(a) mod 4`.
--
--   a odd, a ≥ 3  ⟹  ( seedS a = 1  ↔  4 ∣ φ(a) )    and
--                    ( seedS a ≥ 2  ↔  φ(a) ≡ 2 mod 4 ).
--
-- Reason: `a` odd ⟹ `2a ≡ 2 (mod 4)`, and `φ(a)` is even for `a ≥ 3`, so
-- `4 ∣ (2a − φ(a)) ↔ φ(a) ≡ 2 (mod 4)`; the left side is `2 ≤ seedS a` by
-- `Nat.Prime.pow_dvd_iff_le_factorization`.  (Empirically — brute-checked for
-- odd a < 20000 — the excluded seeds `φ(a) ≡ 2 mod 4` are exactly the prime
-- powers `p^k` with `p ≡ 3 mod 4`; that prime-power form is not formalised
-- here.)  This closed form settles the regime without any valuation search.
-- ---------------------------------------------------------------------------

/-- **Excluded-regime congruence.**  For every odd `a ≥ 3`, the first cototient
    step `2a − φ(a)` has 2-adic valuation `≥ 2` (the regime *outside* the
    `seedS a = 1` transport machinery) exactly when `φ(a) ≡ 2 (mod 4)`.  Since
    `a` is odd, `2a ≡ 2 (mod 4)`, so `4 ∣ (2a − φ(a)) ↔ φ(a) ≡ 2 (mod 4)`, and
    `4 ∣ (2a − φ(a))` is `2 ≤ (2a − φ(a)).factorization 2 = seedS a`. -/
theorem seedS_ge_two_iff_totient_mod_four {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) :
    2 ≤ seedS a ↔ Nat.totient a % 4 = 2 := by
  have hφlt : Nat.totient a < a := Nat.totient_lt a (by omega)
  have hodd : a % 2 = 1 := Nat.odd_iff.1 ha
  have hev : Nat.totient a % 2 = 0 := Nat.even_iff.1 (Nat.totient_even (by omega))
  have hne : 2 * a - Nat.totient a ≠ 0 := by omega
  have hdvd : (2 : ℕ) ^ 2 ∣ (2 * a - Nat.totient a) ↔ 2 ≤ seedS a :=
    Nat.prime_two.pow_dvd_iff_le_factorization hne
  rw [← hdvd, show (2 : ℕ) ^ 2 = 4 from rfl]
  omega

/-- **Transport-admissible congruence.**  For every odd `a ≥ 3`, the seed lies
    in the transport-admissible regime `seedS a = 1` (first-step valuation
    exactly one) exactly when `4 ∣ φ(a)`.  This is the negation of
    `seedS_ge_two_iff_totient_mod_four` using `1 ≤ seedS a` and `Even (φ a)`. -/
theorem seedS_eq_one_iff_four_dvd_totient {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) :
    seedS a = 1 ↔ 4 ∣ Nat.totient a := by
  have hs1 : 1 ≤ seedS a := (seed_spec ha3).2.2.1
  have hev : Nat.totient a % 2 = 0 := Nat.even_iff.1 (Nat.totient_even (by omega))
  have key := seedS_ge_two_iff_totient_mod_four ha ha3
  constructor
  · intro h1
    have hnot : ¬ (Nat.totient a % 4 = 2) := fun hc => by
      have : 2 ≤ seedS a := key.2 hc; omega
    omega
  · intro h4
    have hnot4 : ¬ (Nat.totient a % 4 = 2) := by omega
    have hlt2 : ¬ (2 ≤ seedS a) := fun hc => hnot4 (key.1 hc)
    omega

/-- Sanity check of the congruence criterion at the smallest reversing seed:
    `φ(21) = 12` is divisible by `4`, so `seedS 21 = 1` — the transport regime,
    consistent with `classifySeed_21'` using first-step valuation `s = 1`. -/
theorem seedS_21_eq_one : seedS 21 = 1 :=
  (seedS_eq_one_iff_four_dvd_totient (by decide) (by norm_num)).2 (by norm_num [totient_21])

/-- Sanity check at an excluded seed: `φ(3) = 2 ≡ 2 (mod 4)`, so `seedS 3 ≥ 2`
    — outside the transport machinery, consistent with `classifySeed_3` using
    first-step valuation `s = 2`. -/
theorem seedS_three_ge_two : 2 ≤ seedS 3 :=
  (seedS_ge_two_iff_totient_mod_four (by decide) (by norm_num)).2 (by norm_num [totient_3])

-- ---------------------------------------------------------------------------
-- STRUCTURAL CHARACTERISATION OF THE EXCLUDED REGIME
-- ---------------------------------------------------------------------------
-- The congruence criterion `seedS_ge_two_iff_totient_mod_four` reduces the
-- excluded regime (first-step valuation `≥ 2`) to `φ(a) ≡ 2 (mod 4)`.  The
-- prior code comment noted — empirically, odd `a < 20000` — that these seeds
-- are *exactly* the prime powers `p^k` of primes `p ≡ 3 (mod 4)`.  We now prove
-- that classification unconditionally.
--
-- Proof idea (standard 2-adic count).  `φ` is multiplicative on coprime factors,
-- and for `a ≥ 3` each factor `φ(p^e)` (p odd prime) is even.  Hence:
--   • if `a` has ≥ 2 distinct prime factors, split `a = p^e · m` (coprime),
--     both `φ(p^e)` and `φ(m)` even, so `4 ∣ φ(a)`, i.e. `φ(a) % 4 ≠ 2`;
--   • so `φ(a) % 4 = 2` forces `a` to be a prime power `p^k`, where
--     `φ(p^k) = p^(k-1)(p-1)` with `p^(k-1)` odd, so `φ(a) ≡ 2 (mod 4)` iff
--     `v₂(p-1) = 1` iff `p ≡ 3 (mod 4)`.
-- ---------------------------------------------------------------------------

/-- **Excluded regime = prime powers of primes ≡ 3 (mod 4).**
For every odd `a ≥ 3`, `φ(a) ≡ 2 (mod 4)` (equivalently `seedS a ≥ 2`, the
regime *outside* the `seedS a = 1` transport machinery) holds exactly when `a`
is a prime power `p^k` of a prime `p ≡ 3 (mod 4)`.  Combined with
`seedS_ge_two_iff_totient_mod_four`, this pins down the excluded seed set
`{3,7,9,11,19,23,27,…}` completely: it is `{ p^k : p prime, p ≡ 3 mod 4, k ≥ 1 }`. -/
theorem totient_mod_four_eq_two_iff_prime_pow_three_mod_four
    {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) :
    Nat.totient a % 4 = 2 ↔
      ∃ p k, p.Prime ∧ p % 4 = 3 ∧ 0 < k ∧ a = p ^ k := by
  have ha0 : a ≠ 0 := by omega
  have ha1 : a ≠ 1 := by omega
  have haodd : a % 2 = 1 := Nat.odd_iff.1 ha
  constructor
  · intro hφ
    -- Step 1: `a` is a prime power (else `4 ∣ φ(a)`).
    have hpp : IsPrimePow a := by
      rw [isPrimePow_iff_card_primeFactors_eq_one]
      by_contra hcard
      have hne : a.primeFactors.Nonempty := nonempty_primeFactors.2 (by omega)
      have h2 : 2 ≤ a.primeFactors.card := by
        have := Finset.card_pos.2 hne; omega
      -- smallest prime factor `p` and its `p`-part / `p`-free complement
      have hpprime : (a.minFac).Prime := minFac_prime ha1
      have hpdvd : a.minFac ∣ a := minFac_dvd a
      have hpodd : Odd (a.minFac) := by
        rcases hpprime.eq_two_or_odd' with h2' | ho
        · exfalso; rw [h2'] at hpdvd; omega
        · exact ho
      have hp3 : 3 ≤ a.minFac := by
        have := hpprime.two_le; have := Nat.odd_iff.1 hpodd; omega
      have he : 0 < a.factorization (a.minFac) :=
        hpprime.factorization_pos_of_dvd ha0 hpdvd
      -- `ordProj = p^e ≥ 3`
      have hprojge : 3 ≤ ordProj[a.minFac] a := by
        calc 3 ≤ a.minFac := hp3
          _ = a.minFac ^ 1 := (pow_one _).symm
          _ ≤ a.minFac ^ (a.factorization (a.minFac)) :=
                Nat.pow_le_pow_right (by omega) he
      -- `ordCompl` divides `a` (odd), is `≠ 1` (else `a` a prime power), so `≥ 3`
      have hcompl_dvd : ordCompl[a.minFac] a ∣ a := ordCompl_dvd a _
      have hcompl_pos : 0 < ordCompl[a.minFac] a := ordCompl_pos _ ha0
      have hcompl_odd : Odd (ordCompl[a.minFac] a) := by
        rcases Nat.even_or_odd (ordCompl[a.minFac] a) with hev | ho
        · exfalso
          have : (2 : ℕ) ∣ a := dvd_trans hev.two_dvd hcompl_dvd
          omega
        · exact ho
      have hcompl_ne : ordCompl[a.minFac] a ≠ 1 := by
        intro h1'
        have hall : a = ordProj[a.minFac] a := by
          have := ordProj_mul_ordCompl_eq_self a (a.minFac)
          rw [h1', mul_one] at this; exact this.symm
        have hpp' : IsPrimePow a :=
          ⟨a.minFac, a.factorization (a.minFac), hpprime.prime, he, hall.symm⟩
        rw [isPrimePow_iff_card_primeFactors_eq_one] at hpp'
        omega
      have hcompl_ge : 3 ≤ ordCompl[a.minFac] a := by
        obtain ⟨m, hm⟩ := hcompl_odd; omega
      -- multiplicativity: `φ(a) = φ(ordProj)·φ(ordCompl)`, both even ⟹ `4 ∣ φ(a)`
      have hcop : Nat.Coprime (ordProj[a.minFac] a) (ordCompl[a.minFac] a) :=
        (Nat.coprime_ordCompl hpprime ha0).pow_left _
      have hsplit : ordProj[a.minFac] a * ordCompl[a.minFac] a = a :=
        ordProj_mul_ordCompl_eq_self a (a.minFac)
      have hev1 : Even (Nat.totient (ordProj[a.minFac] a)) := Nat.totient_even (by omega)
      have hev2 : Even (Nat.totient (ordCompl[a.minFac] a)) := Nat.totient_even (by omega)
      have hφsplit : Nat.totient a
          = Nat.totient (ordProj[a.minFac] a) * Nat.totient (ordCompl[a.minFac] a) := by
        rw [← Nat.totient_mul hcop, hsplit]
      have h4 : 4 ∣ Nat.totient a := by
        rw [hφsplit]
        obtain ⟨x, hx⟩ := hev1
        obtain ⟨y, hy⟩ := hev2
        exact ⟨x * y, by rw [hx, hy]; ring⟩
      omega
    -- Step 2: read off the prime `p` and show `p ≡ 3 (mod 4)`.
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff a).1 hpp
    refine ⟨p, k, hp, ?_, hk, hpk.symm⟩
    have hpdvd : p ∣ a := hpk ▸ dvd_pow_self p hk.ne'
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with h2' | ho
      · exfalso; rw [h2'] at hpdvd; omega
      · exact ho
    have hpm2 : p % 2 = 1 := Nat.odd_iff.1 hpodd
    rw [← hpk, Nat.totient_prime_pow hp hk] at hφ
    by_contra hp3
    have hp1 : p % 4 = 1 := by omega
    obtain ⟨t, ht⟩ : (4 : ℕ) ∣ (p - 1) := by
      have := hp.two_le; exact Nat.dvd_of_mod_eq_zero (by omega)
    have hrw : p ^ (k - 1) * (p - 1) = 4 * (p ^ (k - 1) * t) := by rw [ht]; ring
    rw [hrw] at hφ
    omega
  · rintro ⟨p, k, hp, hp3, hk, rfl⟩
    have hp2 : 2 ≤ p := hp.two_le
    rw [Nat.totient_prime_pow hp hk]
    have hpodd : Odd p := Nat.odd_iff.2 (by omega)
    have hu : Odd (p ^ (k - 1)) := hpodd.pow
    have hpm1 : p - 1 = 2 * ((p - 1) / 2) := by omega
    have hwodd : Odd ((p - 1) / 2) := Nat.odd_iff.2 (by omega)
    have key : p ^ (k - 1) * (p - 1) = 2 * (p ^ (k - 1) * ((p - 1) / 2)) := by
      conv_lhs => rw [hpm1]
      ring
    have hzodd : (p ^ (k - 1) * ((p - 1) / 2)) % 2 = 1 := Nat.odd_iff.1 (hu.mul hwodd)
    rw [key]; omega

end Erdos1064OQ03
