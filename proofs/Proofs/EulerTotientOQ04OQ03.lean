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
-- THE PRIME-TRIPLE REVERSAL FAMILY COLLAPSES TO `{21, 55}`
-- ---------------------------------------------------------------------------
-- The two known reversal seeds `21 = 3·7` and `55 = 5·11` are both of the form
-- `a = p·(2p+1)` for the two smallest Sophie-Germain primes `p = 3, 5` (with the
-- extra property that `p+2` is also prime).  It is tempting to hope that this
-- natural infinite candidate family — odd primes `p` with `p+2` and `2p+1` also
-- prime — furnishes infinitely many reversal seeds, which would give a purely
-- elementary proof that the reversal *seed* set is infinite.  It does NOT.
--
-- For such a `p` write `a = p·(2p+1)`.  Then (all coprimalities from primality):
--     φ(a) = (p−1)·2p,
--     first cototient step  2a − φ(a) = 2p(p+2)  (2-adic valuation 1, so
--                                                  transport-admissible, b = p(p+2)),
--     φ(b) = (p−1)(p+1) = p²−1,
--     landing constant  C = 2a − φ(b) = 3p²+2p+1 = 2·e   with  e = (3p²+2p+1)/2,
--                                                  and v₂(C) = 1 (t = 1).
-- The `k`-free reversal criterion `dblIter_reversal_iff` says the family reverses
-- iff  φ(a) < φ(e)·2^(t−1) = φ(e).  But `φ(e) ≤ e − 1 = (3p²+2p−1)/2` always, and
--     (3p²+2p−1)/2 ≤ 2p(p−1)   ⟺   0 ≤ p²−6p+1   ⟺   p ≥ 6,
-- so for every `p ≥ 7` we get `φ(e) ≤ φ(a)` and the family does NOT reverse — the
-- forward/equality regime wins.  Only the two exceptional small primes `p = 3, 5`
-- (below the quadratic threshold `3+2√2 ≈ 5.83`) reverse.  Hence this family
-- yields exactly the two seeds `{21, 55}`, and the infinitude of the reversal seed
-- set (if true) is genuinely harder than exhibiting one infinite candidate family.
-- Note the crucial point: proving `φ(e) ≤ e−1` needs NO knowledge of the (wildly
-- varying) factorisation of `e`, which is precisely what makes the bound uniform.
-- ===========================================================================

/-- **The prime-triple reversal family does not reverse for `p ≥ 7`.**  For an
    odd prime `p` with `p+2` and `2p+1` also prime, the transport-admissible seed
    `a = p·(2p+1)` has `φ(a) = 2p(p−1)` and landing constant `C = 3p²+2p+1 = 2e`;
    reversal of the family `a·2^(k+1)` would require `φ(a) < φ(e)`, but
    `φ(e) ≤ e−1 ≤ φ(a)` whenever `p ≥ 7` (equivalently `p²−6p+1 ≥ 0`).  So no
    member of this natural infinite candidate family with `p ≥ 7` is a reversal
    seed; the only reversing members are the two small exceptions `p = 3` (→ 21)
    and `p = 5` (→ 55). -/
theorem prime_triple_family_not_reversal {p : ℕ}
    (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : (2 * p + 1).Prime)
    (hp7 : 7 ≤ p) (k : ℕ) :
    p * (2 * p + 1) * 2 ^ (k + 1) ∉ ReversalSet := by
  -- write the odd prime `p ≥ 7` as `p = 2j+1` with `j ≥ 3`
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  have hj3 : 3 ≤ j := by omega
  -- coprimalities from distinct primality
  have hcopa : Nat.Coprime (2 * j + 1) (2 * (2 * j + 1) + 1) :=
    (Nat.coprime_primes hp hq).mpr (by omega)
  have hcopb : Nat.Coprime (2 * j + 1) ((2 * j + 1) + 2) :=
    (Nat.coprime_primes hp hp2).mpr (by omega)
  -- φ(a) = 2j·(2·(2j+1)),  φ(b) = 2j·((2j+1)+1)
  have hφa : Nat.totient ((2 * j + 1) * (2 * (2 * j + 1) + 1))
      = 2 * j * (2 * (2 * j + 1)) := by
    rw [Nat.totient_mul hcopa, Nat.totient_prime hp, Nat.totient_prime hq,
        show (2 * j + 1) - 1 = 2 * j from by omega,
        show 2 * (2 * j + 1) + 1 - 1 = 2 * (2 * j + 1) from by omega]
  have hφb : Nat.totient ((2 * j + 1) * ((2 * j + 1) + 2))
      = 2 * j * ((2 * j + 1) + 1) := by
    rw [Nat.totient_mul hcopb, Nat.totient_prime hp, Nat.totient_prime hp2,
        show (2 * j + 1) - 1 = 2 * j from by omega,
        show (2 * j + 1) + 2 - 1 = (2 * j + 1) + 1 from by omega]
  -- oddness of the three odd data
  have ha_odd : Odd ((2 * j + 1) * (2 * (2 * j + 1) + 1)) :=
    (Nat.odd_iff.mpr (by omega)).mul (Nat.odd_iff.mpr (by omega))
  have hb_odd : Odd ((2 * j + 1) * ((2 * j + 1) + 2)) :=
    (Nat.odd_iff.mpr (by omega)).mul (Nat.odd_iff.mpr (by omega))
  have he_odd : Odd (6 * j ^ 2 + 8 * j + 3) := ⟨3 * j ^ 2 + 4 * j + 1, by ring⟩
  -- transport data:  2a − φ(a) = 2b  and  2a − φ(b) = e·2¹
  have hstep : 2 * ((2 * j + 1) * (2 * (2 * j + 1) + 1))
      - Nat.totient ((2 * j + 1) * (2 * (2 * j + 1) + 1))
      = 2 * ((2 * j + 1) * ((2 * j + 1) + 2)) := by
    rw [hφa]
    have h : 2 * ((2 * j + 1) * (2 * (2 * j + 1) + 1))
        = 2 * ((2 * j + 1) * ((2 * j + 1) + 2)) + 2 * j * (2 * (2 * j + 1)) := by ring
    omega
  have hC : 2 * ((2 * j + 1) * (2 * (2 * j + 1) + 1))
      - Nat.totient ((2 * j + 1) * ((2 * j + 1) + 2))
      = (6 * j ^ 2 + 8 * j + 3) * 2 ^ 1 := by
    rw [hφb]
    have h : 2 * ((2 * j + 1) * (2 * (2 * j + 1) + 1))
        = (6 * j ^ 2 + 8 * j + 3) * 2 ^ 1 + 2 * j * ((2 * j + 1) + 1) := by ring
    omega
  -- feed the k-free reversal criterion and refute the sign inequality
  rw [dblIter_reversal_iff ha_odd hb_odd he_odd (le_refl 1) hstep hC k]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [hφa]
  -- goal: ¬ (2j·(2·(2j+1)) < φ(6j²+8j+3));  i.e. φ(e) ≤ φ(a)
  push_neg
  have he2 : 1 < 6 * j ^ 2 + 8 * j + 3 := by nlinarith [hj3]
  have hφe : Nat.totient (6 * j ^ 2 + 8 * j + 3) < 6 * j ^ 2 + 8 * j + 3 :=
    Nat.totient_lt _ he2
  have hquad : 6 * j ^ 2 + 8 * j + 2 ≤ 2 * j * (2 * (2 * j + 1)) := by nlinarith [hj3]
  omega

/-- **The prime-triple family reverses exactly at `p ∈ {3, 5}`.**  For every odd
    prime `p` with `p+2` and `2p+1` also prime, the family `p·(2p+1)·2^(k+1)`
    lands in the reversal regime `φ(n) < φ(D(n))` iff `p = 3` (seed `21`) or
    `p = 5` (seed `55`).  The `p ≥ 7` members are ruled out by
    `prime_triple_family_not_reversal`; the two small cases are the known reversal
    families.  Thus the natural Sophie-Germain-type candidate family contributes
    exactly the two reversal seeds `21` and `55` — it does not, by itself, prove
    the reversal seed set infinite. -/
theorem prime_triple_reversal_iff {p : ℕ}
    (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : (2 * p + 1).Prime) (k : ℕ) :
    p * (2 * p + 1) * 2 ^ (k + 1) ∈ ReversalSet ↔ (p = 3 ∨ p = 5) := by
  constructor
  · intro hmem
    by_contra hne
    push_neg at hne
    obtain ⟨h3, h5⟩ := hne
    -- an odd prime with `p+2, 2p+1` prime and `p ∉ {3,5}` must be `≥ 7`
    have h2le := hp.two_le
    have hp7 : 7 ≤ p := by
      by_contra hlt
      push_neg at hlt
      interval_cases p <;> revert hp hp2 hq h3 h5 <;> decide
    exact prime_triple_family_not_reversal hp hp2 hq hp7 k hmem
  · rintro (rfl | rfl)
    · rw [show (3 : ℕ) * (2 * 3 + 1) = 21 from by norm_num]
      exact reversal_via_criterion k
    · rw [show (5 : ℕ) * (2 * 5 + 1) = 55 from by norm_num]
      exact reversal_via_criterion_55 k

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

/-- **Necessary numeric condition for reversal.**  For odd `a ≥ 3`, if the whole
    family `a·2^(k+1)` reverses (`classifySeed a = .lt`) then twice the seed's
    totient falls strictly below the landing constant: `2·φ(a) < seedC a`.  The
    classifier compares `φ(a)` with `φ(seedE a)·2^(seedT a − 1)`; since
    `seedC a = seedE a · 2^(seedT a)` (from `seed_spec`) and `φ(seedE a) ≤ seedE a`,
    the compared quantity is at most `seedC a / 2`, so reversal forces
    `2·φ(a) < seedC a`.

    This condition is *necessary but not sufficient*: the prime powers `a = 3^k`
    (which are excluded seeds, `p = 3 ≡ 3 mod 4`) all satisfy `2·φ(a) < seedC a`
    yet never reverse — brute-checked for odd `a < 80000`, no excluded seed
    reverses at all.  Closing the structural claim "no excluded seed reverses"
    therefore needs the finer ratio `φ(seedE a)/seedE a`, not merely the crude
    bound `φ(e) ≤ e` used here. -/
theorem reversal_two_totient_lt_seedC {a : ℕ} (ha3 : 3 ≤ a)
    (h : classifySeed a = Ordering.lt) : 2 * Nat.totient a < seedC a := by
  obtain ⟨_, _, _, ht1, _, hCeq⟩ := seed_spec ha3
  -- Unfold the classifier and read off the strict inequality on totients.
  simp only [classifySeed] at h
  have hlt : Nat.totient a < Nat.totient (seedE a) * 2 ^ (seedT a - 1) :=
    compare_lt_iff_lt.1 h
  -- `seedC a = seedE a * 2^(seedT a)` and `2^(seedT a) = 2 * 2^(seedT a - 1)`.
  have hC : seedC a = seedE a * 2 ^ seedT a := by unfold seedC; exact hCeq
  have h2t : 2 ^ seedT a = 2 * 2 ^ (seedT a - 1) := by
    conv_lhs => rw [show seedT a = (seedT a - 1) + 1 from by omega, pow_succ]
    ring
  have hle : Nat.totient (seedE a) ≤ seedE a := Nat.totient_le _
  calc 2 * Nat.totient a
      < 2 * (Nat.totient (seedE a) * 2 ^ (seedT a - 1)) := by omega
    _ ≤ 2 * (seedE a * 2 ^ (seedT a - 1)) := by gcongr
    _ = seedE a * 2 ^ seedT a := by rw [h2t]; ring
    _ = seedC a := hC.symm

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

-- ---------------------------------------------------------------------------
-- AN INFINITE EXCLUDED FAMILY THAT NEVER REVERSES:  a = 3^k
-- ---------------------------------------------------------------------------
-- Every seed `a = 3^k` (k ≥ 1) is an excluded prime power (p = 3 ≡ 3 mod 4, so
-- `seedS a ≥ 2` by `seedS_three_ge_two` / the prime-power characterisation).
-- Prior structural work verified, by a finite `decide` sweep, that no excluded
-- seed `a < 120` reverses.  Here we upgrade that to a genuine INFINITE family:
-- the classifier evaluates on the whole `3^k` line to `.eq` (k = 1, 2) or `.gt`
-- (k ≥ 3), never `.lt`.  Hence `3^k·2^(j+1)` never reverses for any k ≥ 1, j —
-- the first *proven* infinite non-reversing family inside the excluded regime.
--
-- Mechanism for k ≥ 3 (write `a = 3^(m+3)`):  φ(a) = 2·3^(m+2), so the first
-- cototient step is `2a − φ(a) = 4·3^(m+2)` (valuation `s = 2`, odd part
-- `b = 3^(m+2)`).  The landing constant is `C = 2a − φ(b)·2 = 14·3^(m+1) = e·2`
-- (so `t = 1`, `e = 7·3^(m+1)`), and the classifier compares
-- `φ(a) = 18·3^m` against `φ(e)·2^0 = 12·3^m`, giving `.gt`.
-- ---------------------------------------------------------------------------

/-- **The excluded family `3^(m+3)` classifies as forward (`.gt`).**  For every
    `m`, the seed `a = 3^(m+3)` has first-step data `s = 2`, `b = 3^(m+2)` and
    landing data `t = 1`, `e = 7·3^(m+1)`; the classifier compares
    `φ(a) = 18·3^m` with `φ(e) = 12·3^m`, so `classifySeed (3^(m+3)) = .gt`. -/
theorem classifySeed_three_pow_ge_three (m : ℕ) :
    classifySeed (3 ^ (m + 3)) = Ordering.gt := by
  have hp : Nat.Prime 3 := by norm_num
  have hpos : 0 < (3 : ℕ) ^ m := pow_pos (by norm_num) m
  -- powers of three reduced to multiples of `3^m`
  have e1 : (3 : ℕ) ^ (m + 1) = 3 * 3 ^ m := by ring
  have e2 : (3 : ℕ) ^ (m + 2) = 9 * 3 ^ m := by ring
  have e3 : (3 : ℕ) ^ (m + 3) = 27 * 3 ^ m := by ring
  -- totients of the seed, the odd part `b = 3^(m+2)`, and the landing part `e`
  have tφa : Nat.totient (3 ^ (m + 3)) = 3 ^ (m + 2) * 2 :=
    Nat.totient_prime_pow_succ hp (m + 2)
  have tφb : Nat.totient (3 ^ (m + 2)) = 3 ^ (m + 1) * 2 :=
    Nat.totient_prime_pow_succ hp (m + 1)
  have hcop : Nat.Coprime 7 (3 ^ (m + 1)) := (show Nat.Coprime 7 3 by decide).pow_right _
  have tφe : Nat.totient (7 * 3 ^ (m + 1)) = 12 * 3 ^ m := by
    rw [Nat.totient_mul hcop, show Nat.totient 7 = 6 from totient_7,
        show Nat.totient (3 ^ (m + 1)) = 3 ^ m * 2 from Nat.totient_prime_pow_succ hp m]
    ring
  -- odd parts
  have hob : Odd (3 ^ (m + 2)) := (show Odd 3 by decide).pow
  have hoe : Odd (7 * 3 ^ (m + 1)) := (show Odd 7 by decide).mul (show Odd 3 by decide).pow
  -- the two 2-adic extraction equations, in multiples of `3^m`
  have hstep : 2 * 3 ^ (m + 3) - Nat.totient (3 ^ (m + 3)) = 3 ^ (m + 2) * 2 ^ 2 := by
    rw [tφa, e3, e2, show (2 : ℕ) ^ 2 = 4 from by norm_num]; omega
  have hCval : 2 * 3 ^ (m + 3) - Nat.totient (3 ^ (m + 2)) * 2 ^ (2 - 1)
      = 7 * 3 ^ (m + 1) * 2 ^ 1 := by
    rw [tφb, e3, e1]; simp only [show (2 : ℕ) ^ (2 - 1) = 2 from rfl]; omega
  rw [classifySeed_val (s := 2) (b := 3 ^ (m + 2)) (t := 1) (e := 7 * 3 ^ (m + 1))
      hob hoe hstep hCval, tφa, tφe, compare_gt_iff_gt,
      show (2 : ℕ) ^ (1 - 1) = 1 from by norm_num, mul_one, e2]
  omega

/-- **The infinite excluded family `3^k` never reverses.**  For every `k ≥ 1`
    the seed `a = 3^k` — an excluded prime power (`p = 3 ≡ 3 mod 4`, so
    `seedS a ≥ 2`) — classifies to `.eq` (k = 1, 2) or `.gt` (k ≥ 3); in
    particular `classifySeed (3^k) ≠ .lt`.  This is the first *infinite*
    sub-family of the excluded regime proven never to reverse, upgrading the
    prior finite `decide` sweep over `a < 120`. -/
theorem three_pow_never_reverses {k : ℕ} (hk : 1 ≤ k) :
    classifySeed (3 ^ k) ≠ Ordering.lt := by
  rcases le_or_gt k 2 with h2 | h3
  · interval_cases k
    · rw [pow_one, classifySeed_3]; decide
    · rw [show (3 : ℕ) ^ 2 = 9 from by norm_num, classifySeed_9]; decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [classifySeed_three_pow_ge_three m]; decide

/-- **The family `3^k · 2^(j+1)` never reverses the totient inequality.**  For
    every `k ≥ 1` and `j`, `φ(n) ≥ φ(D(n))` throughout `n = 3^k·2^(j+1)`; i.e.
    no member of this infinite excluded family lies in `ReversalSet`.  Combined
    with `twentyone_smallest_reversing_seed` (smallest reversing seed `21 = 3·7`
    has `seedS = 1`), this evidences the structural conjecture that reversals
    occur only in the transport-admissible regime `seedS a = 1`. -/
theorem three_pow_family_not_reversal {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    3 ^ k * 2 ^ (j + 1) ∉ ReversalSet := by
  have ha : Odd (3 ^ k) := (show Odd 3 by decide).pow
  have ha3 : 3 ≤ 3 ^ k := by
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [classifySeed_lt_iff ha ha3 j]
  exact three_pow_never_reverses hk

-- ---------------------------------------------------------------------------
-- A GENERAL NON-REVERSAL ENGINE FOR THE EXCLUDED REGIME
-- ---------------------------------------------------------------------------
-- The single excluded family `3^k` was shown never to reverse by an explicit
-- per-seed computation.  Here we isolate the *mechanism* into a reusable engine
-- and apply it to a genuinely larger class.
--
-- Key observation.  For an excluded seed (`seedS a ≥ 2`) the classifier compares
-- `φ(a)` against `φ(e)·2^(t−1)` where the landing constant `C = seedC a` splits
-- as `e·2^t` (`e = seedE a`, `t = seedT a`).  Because `φ(e) ≤ e`,
--     φ(e)·2^(t−1) ≤ e·2^(t−1) = C/2 = a − φ(seedB a)·2^(seedS a − 2).
-- So the family `a·2^(k+1)` fails to reverse as soon as
--     a − φ(a) ≤ φ(seedB a)·2^(seedS a − 2).
-- This single inequality is the *only* seed-specific fact needed.  For the base
-- case `a = p` (a prime, so `a − φ(a) = 1`) it holds trivially, giving the whole
-- infinite class of primes `p ≡ 3 (mod 4)` at once — a class strictly larger
-- than the powers `3^k` of one fixed prime.
-- ---------------------------------------------------------------------------

/-- **General non-reversal engine (excluded regime).**  Let `a ≥ 3` be an
    excluded seed (`seedS a ≥ 2`).  If the "excess" `a − φ(a)` is bounded by
    `φ(seedB a)·2^(seedS a − 2)` then the whole family `a·2^(k+1)` never reverses:
    `classifySeed a ≠ .lt`.

    The proof uses only `φ(seedE a) ≤ seedE a`: the compared quantity
    `φ(e)·2^(t−1)` is at most `e·2^(t−1) = seedC a / 2 = a − φ(seedB a)·2^(s−2)`,
    which the hypothesis forces to be `≤ φ(a)`. -/
theorem classifySeed_ne_lt_of_excess_bound {a : ℕ} (ha3 : 3 ≤ a)
    (hs2 : 2 ≤ seedS a)
    (hbound : a - Nat.totient a ≤ Nat.totient (seedB a) * 2 ^ (seedS a - 2)) :
    classifySeed a ≠ Ordering.lt := by
  obtain ⟨_, hoe, _, ht1, _, hCeq⟩ := seed_spec ha3
  -- `hCeq : 2*a − φ(seedB a)·2^(seedS a − 1) = seedE a · 2^(seedT a)`
  have hφa_le : Nat.totient a ≤ a := Nat.totient_le a
  have hepos : seedE a ≠ 0 := by rcases hoe with ⟨m, hm⟩; omega
  have hne : seedE a * 2 ^ seedT a ≠ 0 :=
    mul_ne_zero hepos (pow_ne_zero _ (by norm_num))
  -- split the two powers of two so the whole identity is divisible by 2
  have h2t : 2 ^ seedT a = 2 * 2 ^ (seedT a - 1) := by
    conv_lhs => rw [show seedT a = (seedT a - 1) + 1 from by omega, pow_succ]
    ring
  have h2s : 2 ^ (seedS a - 1) = 2 * 2 ^ (seedS a - 2) := by
    conv_lhs => rw [show seedS a - 1 = (seedS a - 2) + 1 from by omega, pow_succ]
    ring
  have hZ : seedE a * 2 ^ seedT a = 2 * (seedE a * 2 ^ (seedT a - 1)) := by
    rw [h2t]; ring
  have hY : Nat.totient (seedB a) * 2 ^ (seedS a - 1)
      = 2 * (Nat.totient (seedB a) * 2 ^ (seedS a - 2)) := by
    rw [h2s]; ring
  -- `2a = seedE·2^t + φ(seedB)·2^(s−1)`  (nat subtraction resolves via `hne`)
  have hsum : 2 * a = seedE a * 2 ^ seedT a
      + Nat.totient (seedB a) * 2 ^ (seedS a - 1) := by omega
  -- halve: `a = seedE·2^(t−1) + φ(seedB)·2^(s−2)`
  have haXW : a = seedE a * 2 ^ (seedT a - 1)
      + Nat.totient (seedB a) * 2 ^ (seedS a - 2) := by rw [hZ, hY] at hsum; omega
  -- hence `seedE·2^(t−1) ≤ φ(a)`, using the excess bound
  have hXle : seedE a * 2 ^ (seedT a - 1) ≤ Nat.totient a := by omega
  have htot : Nat.totient (seedE a) ≤ seedE a := Nat.totient_le _
  have hle : Nat.totient (seedE a) * 2 ^ (seedT a - 1) ≤ Nat.totient a :=
    calc Nat.totient (seedE a) * 2 ^ (seedT a - 1)
        ≤ seedE a * 2 ^ (seedT a - 1) := by gcongr
      _ ≤ Nat.totient a := hXle
  -- the classifier compares `φ(a)` with a quantity `≤ φ(a)`, so it is never `.lt`
  simp only [classifySeed]
  rw [ne_eq, compare_lt_iff_lt]
  omega

/-- **Strict-increase (forward) engine.**  The `.gt` companion of
    `classifySeed_ne_lt_of_excess_bound`.  Under the *same* excess bound and the
    *extra* hypothesis that the second landing value is nontrivial (`2 ≤ seedE a`),
    the classifier is strictly `.gt`: the whole family `a·2^(k+1)` lies in the
    forward regime `φ(n) > φ(D(n))`.

    The non-strict engine only rules out `.lt`, leaving `.eq` open — and `.eq` is
    genuinely realised inside the excluded regime by the tower `3^k` (there
    `seedE = 1`, so the strict hypothesis fails and the classifier is `.eq`, cf.
    `classifySeed_3`, `classifySeed_9`).  The single strict factor
    `φ(seedE a) < seedE a` (valid exactly when `seedE a ≥ 2`) upgrades the engine's
    `φ(seedE a)·2^{t−1} ≤ φ(a)` to a strict `<`, excluding `.eq` and pinning the
    regime to `.gt`.  Together the two engines give the full trichotomy on any
    excluded seed as a function of a single arithmetic invariant `seedE a`:
    `seedE a = 1 ⟹ .eq`,  `seedE a ≥ 2 ⟹ .gt`. -/
theorem classifySeed_gt_of_excess_bound {a : ℕ} (ha3 : 3 ≤ a)
    (hs2 : 2 ≤ seedS a)
    (hbound : a - Nat.totient a ≤ Nat.totient (seedB a) * 2 ^ (seedS a - 2))
    (he2 : 2 ≤ seedE a) :
    classifySeed a = Ordering.gt := by
  obtain ⟨_, hoe, _, ht1, _, hCeq⟩ := seed_spec ha3
  have hφa_le : Nat.totient a ≤ a := Nat.totient_le a
  have hepos : seedE a ≠ 0 := by omega
  have hne : seedE a * 2 ^ seedT a ≠ 0 :=
    mul_ne_zero hepos (pow_ne_zero _ (by norm_num))
  have h2t : 2 ^ seedT a = 2 * 2 ^ (seedT a - 1) := by
    conv_lhs => rw [show seedT a = (seedT a - 1) + 1 from by omega, pow_succ]
    ring
  have h2s : 2 ^ (seedS a - 1) = 2 * 2 ^ (seedS a - 2) := by
    conv_lhs => rw [show seedS a - 1 = (seedS a - 2) + 1 from by omega, pow_succ]
    ring
  have hZ : seedE a * 2 ^ seedT a = 2 * (seedE a * 2 ^ (seedT a - 1)) := by
    rw [h2t]; ring
  have hY : Nat.totient (seedB a) * 2 ^ (seedS a - 1)
      = 2 * (Nat.totient (seedB a) * 2 ^ (seedS a - 2)) := by
    rw [h2s]; ring
  have hsum : 2 * a = seedE a * 2 ^ seedT a
      + Nat.totient (seedB a) * 2 ^ (seedS a - 1) := by omega
  have haXW : a = seedE a * 2 ^ (seedT a - 1)
      + Nat.totient (seedB a) * 2 ^ (seedS a - 2) := by rw [hZ, hY] at hsum; omega
  have hXle : seedE a * 2 ^ (seedT a - 1) ≤ Nat.totient a := by omega
  -- strict factor: `φ(seedE a) < seedE a` because `seedE a ≥ 2`
  have htot_lt : Nat.totient (seedE a) < seedE a := Nat.totient_lt _ (by omega)
  have hpow_pos : 0 < 2 ^ (seedT a - 1) := pow_pos (by norm_num) _
  have hlt : Nat.totient (seedE a) * 2 ^ (seedT a - 1) < Nat.totient a :=
    calc Nat.totient (seedE a) * 2 ^ (seedT a - 1)
        < seedE a * 2 ^ (seedT a - 1) := mul_lt_mul_of_pos_right htot_lt hpow_pos
      _ ≤ Nat.totient a := hXle
  -- the classifier compares `φ(a)` with a strictly smaller quantity, so it is `.gt`
  simp only [classifySeed]
  rw [compare_gt_iff_gt]
  exact hlt

/-- **Reduction of the excluded-prime forward regime to a single invariant.**
    For a prime `p ≡ 3 (mod 4)` the excess is minimal (`p − φ(p) = 1`), so the
    excess bound of the strict engine always holds; hence `classifySeed p = .gt`
    is equivalent to the arithmetic fact `2 ≤ seedE p` (the odd part of the second
    landing constant is nontrivial).  This isolates the *exact* remaining
    obstruction to completing the excluded-regime trichotomy: every prime
    `p ≡ 3 (mod 4)` is either `.eq` (only `p = 3`, where `seedE 3 = 1`) or `.gt`
    (all `p ≥ 7`, conjecturally, iff `seedE p ≥ 2`).  Combined with
    `classifySeed_prime_three_mod_four_ne_lt` (which already rules out `.lt`), the
    open question "is every excluded prime `p ≥ 7` strictly forward?" reduces to
    the single statement `seedE p ≥ 2` for such `p`. -/
theorem classifySeed_prime_three_mod_four_gt_of_seedE
    {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (he2 : 2 ≤ seedE p) :
    classifySeed p = Ordering.gt := by
  have hp3' : 3 ≤ p := by omega
  have hodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hφp : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hs2 : 2 ≤ seedS p :=
    (seedS_ge_two_iff_totient_mod_four hodd hp3').2 (by rw [hφp]; omega)
  have hbpos : 0 < seedB p := by rcases (seed_spec hp3').1 with ⟨m, hm⟩; omega
  have hbound : p - Nat.totient p ≤ Nat.totient (seedB p) * 2 ^ (seedS p - 2) := by
    have h1 : 1 ≤ Nat.totient (seedB p) * 2 ^ (seedS p - 2) :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (Nat.totient_pos.mpr hbpos).ne' (pow_ne_zero _ (by norm_num)))
    rw [hφp]; omega
  exact classifySeed_gt_of_excess_bound hp3' hs2 hbound he2

/-- **No prime seed `p ≡ 3 (mod 4)` reverses.**  Every prime `p ≡ 3 (mod 4)` is
    an excluded seed (`seedS p ≥ 2`), and `p − φ(p) = 1`, so the general engine
    applies immediately: `classifySeed p ≠ .lt`.  This exhibits an infinite class
    of non-reversing excluded seeds — the primes `3, 7, 11, 19, 23, 31, …` —
    strictly larger than the single-prime tower `3^k`. -/
theorem classifySeed_prime_three_mod_four_ne_lt
    {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) :
    classifySeed p ≠ Ordering.lt := by
  have hp3' : 3 ≤ p := by omega
  have hodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hφp : Nat.totient p = p - 1 := Nat.totient_prime hp
  have hs2 : 2 ≤ seedS p :=
    (seedS_ge_two_iff_totient_mod_four hodd hp3').2 (by rw [hφp]; omega)
  -- excess `p − φ(p) = 1 ≤ φ(seedB p)·2^(seedS p − 2)`
  have hbpos : 0 < seedB p := by rcases (seed_spec hp3').1 with ⟨m, hm⟩; omega
  have hbound : p - Nat.totient p ≤ Nat.totient (seedB p) * 2 ^ (seedS p - 2) := by
    have h1 : 1 ≤ Nat.totient (seedB p) * 2 ^ (seedS p - 2) :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (Nat.totient_pos.mpr hbpos).ne' (pow_ne_zero _ (by norm_num)))
    rw [hφp]; omega
  exact classifySeed_ne_lt_of_excess_bound hp3' hs2 hbound

/-- **The family `p·2^(k+1)` never reverses, for every prime `p ≡ 3 (mod 4)`.**
    No member of this infinite family of excluded seeds lies in `ReversalSet`.
    Together with `three_pow_family_not_reversal` (the tower `3^k`) this widens
    the class of proven non-reversing excluded seeds to *all* primes `≡ 3 mod 4`,
    evidencing the structural conjecture that reversals occur only in the
    transport-admissible regime `seedS a = 1`. -/
theorem prime_three_mod_four_family_not_reversal
    {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    p * 2 ^ (k + 1) ∉ ReversalSet := by
  have hp3' : 3 ≤ p := by omega
  have hodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [classifySeed_lt_iff hodd hp3' k]
  exact classifySeed_prime_three_mod_four_ne_lt hp hp3

-- ---------------------------------------------------------------------------
-- THE FULL EXCLUDED PRIME-POWER FAMILY:  a = p^k,  p ≡ 3 (mod 4)
-- ---------------------------------------------------------------------------
-- The engine `classifySeed_ne_lt_of_excess_bound` reduced non-reversal of an
-- excluded seed to the single bound  a − φ(a) ≤ φ(seedB a)·2^(seedS a − 2).
-- Two special cases were already discharged with it: the tower `3^k` (one fixed
-- prime, all exponents) and the primes `p ≡ 3 mod 4` (all such primes, exponent
-- one).  Here we cover their common generalisation — EVERY prime power `p^k`
-- with `p ≡ 3 (mod 4)` — closing the excluded prime-power case in full.
--
-- Arithmetic.  For `a = p^k` (`k = m+1`):  φ(a) = p^m·(p−1), so
--   a − φ(a) = p^m,      2a − φ(a) = p^m·(p+1).
-- Writing `p + 1 = w·2^S` with `w` odd and `S = v₂(p+1) ≥ 2` (as `p ≡ 3 mod 4`),
-- the first cototient step factorises as `2a − φ(a) = (p^m·w)·2^S`, so
--   seedS a = S,   seedB a = p^m·w   (with `p^m` and `w` coprime, `w ∣ p+1`).
-- Hence the required bound is  p^m ≤ φ(p^m)·φ(w)·2^(S−2).  It follows from the
-- two elementary facts  p^m ≤ 2·φ(p^m)  (true for any prime `p`) and
-- `2 ≤ φ(w)·2^(S−2)` (true precisely because `p > 3`: the excluded value
-- `S = 2 ∧ w = 1` forces `p + 1 = 4`, i.e. `p = 3`, which is handled separately
-- by the `3^k` tower).  So the engine applies to every `p^k`, `p ≡ 3 mod 4`.
-- ---------------------------------------------------------------------------

/-- **For any prime `p`, `p^m ≤ 2·φ(p^m)`.**  (For `m ≥ 1`, `φ(p^m) = p^{m-1}(p-1)`
    and `2(p-1) ≥ p`; for `m = 0` both sides are trivial.)  This is the seed-shape
    ingredient in the prime-power non-reversal bound. -/
theorem prime_pow_le_two_totient {p : ℕ} (hp : p.Prime) (m : ℕ) :
    p ^ m ≤ 2 * Nat.totient (p ^ m) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0; simp only [pow_zero, Nat.totient_one]; omega
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp m', pow_succ]
    have hpp : p ≤ 2 * (p - 1) := by have := hp.two_le; omega
    calc p ^ m' * p ≤ p ^ m' * (2 * (p - 1)) := mul_le_mul_left' hpp (p ^ m')
      _ = 2 * (p ^ m' * (p - 1)) := by ring

/-- **No excluded prime power `p^k` with `p ≡ 3 (mod 4)` reverses.**  For every
    prime `p ≡ 3 (mod 4)` and every `k ≥ 1` the seed `a = p^k` classifies away
    from `.lt`, so the whole family `p^k·2^(j+1)` never reverses the totient
    inequality.  This unifies and strictly extends both previously proven
    infinite non-reversing sub-families — the tower `3^k`
    (`three_pow_never_reverses`) and the primes themselves
    (`classifySeed_prime_three_mod_four_ne_lt`, the `k = 1` slice). -/
theorem classifySeed_prime_pow_three_mod_four_ne_lt {p k : ℕ}
    (hp : p.Prime) (hp3 : p % 4 = 3) (hk : 1 ≤ k) :
    classifySeed (p ^ k) ≠ Ordering.lt := by
  by_cases hp3' : p = 3
  · subst hp3'; exact three_pow_never_reverses hk
  · -- `p ≡ 3 mod 4`, `p ≠ 3`  ⟹  `p ≥ 7`
    have hp7 : 7 ≤ p := by
      have h2 := hp.two_le
      by_contra h7
      push_neg at h7
      interval_cases p <;> first
        | exact absurd hp (by decide)
        | omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hodd_p : Odd p := Nat.odd_iff.mpr (by omega)
    -- first cototient step:  2a − φ(a) = p^m·(p+1),  and  a − φ(a) = p^m
    have hφ : Nat.totient (p ^ (m + 1)) = p ^ m * (p - 1) :=
      Nat.totient_prime_pow_succ hp m
    have hsum : Nat.totient (p ^ (m + 1)) + p ^ m = p ^ (m + 1) := by
      rw [hφ, pow_succ]
      have h1 : p ^ m * (p - 1) + p ^ m = p ^ m * ((p - 1) + 1) := by ring
      rw [h1, show (p - 1) + 1 = p from by omega]
    have hexcess : p ^ (m + 1) - Nat.totient (p ^ (m + 1)) = p ^ m := by omega
    have hstep_sum : p ^ m * (p + 1) + Nat.totient (p ^ (m + 1)) = 2 * p ^ (m + 1) := by
      rw [hφ]
      have h2 : p ^ m * (p + 1) + p ^ m * (p - 1) = p ^ m * ((p + 1) + (p - 1)) := by ring
      rw [h2, show (p + 1) + (p - 1) = 2 * p from by omega, pow_succ]; ring
    have hstep_eq : 2 * p ^ (m + 1) - Nat.totient (p ^ (m + 1)) = p ^ m * (p + 1) := by omega
    -- 2-adic decomposition of `p + 1`:  `p + 1 = w·2^S`, `w` odd, `S ≥ 2`
    obtain ⟨S, w, hwodd, hS2, hpw⟩ :
        ∃ S w, Odd w ∧ 2 ≤ S ∧ p + 1 = w * 2 ^ S := by
      have hp1ne : p + 1 ≠ 0 := by omega
      refine ⟨(p + 1).factorization 2, (p + 1) / 2 ^ ((p + 1).factorization 2), ?_, ?_, ?_⟩
      · have hnd : ¬ (2 : ℕ) ∣ (p + 1) / 2 ^ ((p + 1).factorization 2) :=
          Nat.not_dvd_ordCompl Nat.prime_two hp1ne
        exact Nat.odd_iff.mpr (by omega)
      · have h4 : (2 : ℕ) ^ 2 ∣ p + 1 := by
          rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]; omega
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hp1ne).mp h4
      · rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self (p + 1) 2).symm
    -- factorised first step  ⟹  seedS a = S,  seedB a = p^m·w
    have hbodd : Odd (p ^ m * w) := (hodd_p.pow).mul hwodd
    have hEq : 2 * p ^ (m + 1) - Nat.totient (p ^ (m + 1)) = (p ^ m * w) * 2 ^ S := by
      rw [hstep_eq, hpw]; ring
    have hSval : seedS (p ^ (m + 1)) = S := by
      unfold seedS; exact (factor_two_split hbodd hEq).1
    have hBval : seedB (p ^ (m + 1)) = p ^ m * w := by
      unfold seedB seedS; exact (factor_two_split hbodd hEq).2
    -- totient of the odd part splits (p^m and w are coprime, since w ∣ p+1)
    have hcps : Nat.Coprime p (p + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
    have hwdvd : w ∣ p + 1 := ⟨2 ^ S, hpw⟩
    have hcop_pw : Nat.Coprime (p ^ m) w :=
      Nat.Coprime.pow_left m (Nat.Coprime.coprime_dvd_right hwdvd hcps)
    have hφpw : Nat.totient (p ^ m * w) = Nat.totient (p ^ m) * Nat.totient w :=
      Nat.totient_mul hcop_pw
    -- fact 2:  2 ≤ φ(w)·2^(S−2)   (uses `p ≥ 7`, i.e. ¬(S = 2 ∧ w = 1))
    have hQ2 : 2 ≤ Nat.totient w * 2 ^ (S - 2) := by
      rcases Nat.lt_or_ge S 3 with hS3 | hS3
      · have hSeq : S = 2 := by omega
        have hw3 : 3 ≤ w := by
          have h4w : p + 1 = w * 4 := by rw [hpw, hSeq]; norm_num
          rcases hwodd with ⟨i, hi⟩; omega
        have hev : Even (Nat.totient w) := Nat.totient_even (by omega)
        have hpos : 0 < Nat.totient w := Nat.totient_pos.mpr (by omega)
        obtain ⟨j, hj⟩ := hev
        rw [hSeq]; simp only [show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one]; omega
      · have h2pow : (2 : ℕ) ≤ 2 ^ (S - 2) := by
          calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ (S - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hwpos : 0 < Nat.totient w :=
          Nat.totient_pos.mpr (by rcases hwodd with ⟨i, hi⟩; omega)
        have hw1 : 1 ≤ Nat.totient w := hwpos
        calc (2 : ℕ) ≤ 2 ^ (S - 2) := h2pow
          _ = 1 * 2 ^ (S - 2) := (one_mul _).symm
          _ ≤ Nat.totient w * 2 ^ (S - 2) := mul_le_mul_right' hw1 (2 ^ (S - 2))
    -- assemble the engine's excess bound  p^m ≤ φ(p^m)·φ(w)·2^(S−2)  and conclude
    have hbound : p ^ (m + 1) - Nat.totient (p ^ (m + 1)) ≤
        Nat.totient (seedB (p ^ (m + 1))) * 2 ^ (seedS (p ^ (m + 1)) - 2) := by
      rw [hexcess, hBval, hSval, hφpw]
      calc p ^ m ≤ 2 * Nat.totient (p ^ m) := prime_pow_le_two_totient hp m
        _ = Nat.totient (p ^ m) * 2 := by ring
        _ ≤ Nat.totient (p ^ m) * (Nat.totient w * 2 ^ (S - 2)) :=
              mul_le_mul_left' hQ2 (Nat.totient (p ^ m))
        _ = Nat.totient (p ^ m) * Nat.totient w * 2 ^ (S - 2) := by ring
    have hpge : p ≤ p ^ (m + 1) := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have ha3 : 3 ≤ p ^ (m + 1) := le_trans (by omega) hpge
    have hs2 : 2 ≤ seedS (p ^ (m + 1)) := by rw [hSval]; exact hS2
    exact classifySeed_ne_lt_of_excess_bound ha3 hs2 hbound

/-- **The family `p^k·2^(j+1)` never reverses, for every prime `p ≡ 3 (mod 4)`
    and `k ≥ 1`.**  No member of this infinite two-parameter family of excluded
    seeds lies in `ReversalSet`.  This is the full excluded prime-power case: it
    contains both `three_pow_family_not_reversal` (`p = 3`) and
    `prime_three_mod_four_family_not_reversal` (`k = 1`) as slices, giving further
    evidence for the structural conjecture that reversals occur only in the
    transport-admissible regime `seedS a = 1`. -/
theorem prime_pow_three_mod_four_family_not_reversal {p k : ℕ}
    (hp : p.Prime) (hp3 : p % 4 = 3) (hk : 1 ≤ k) (j : ℕ) :
    p ^ k * 2 ^ (j + 1) ∉ ReversalSet := by
  have hodd : Odd (p ^ k) := (Nat.odd_iff.mpr (show p % 2 = 1 by omega)).pow
  have hpge : p ≤ p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by have := hp.two_le; omega) hk
  have ha3 : 3 ≤ p ^ k := le_trans (by omega) hpge
  rw [classifySeed_lt_iff hodd ha3 j]
  exact classifySeed_prime_pow_three_mod_four_ne_lt hp hp3 hk

-- ---------------------------------------------------------------------------
-- CAPSTONE:  THE EXCLUDED REGIME NEVER REVERSES  (structural conjecture proven)
-- ---------------------------------------------------------------------------
-- The excluded seeds are *exactly* the prime powers `p^k` with `p ≡ 3 (mod 4)`:
--   `seedS a ≥ 2  ⟺  φ(a) ≡ 2 (mod 4)`   (`seedS_ge_two_iff_totient_mod_four`)
--   `φ(a) ≡ 2 (mod 4)  ⟺  a = p^k, p ≡ 3 mod 4`
--                                (`totient_mod_four_eq_two_iff_prime_pow_three_mod_four`).
-- Having just shown that *every* such prime power never reverses, we obtain the
-- full structural dichotomy that all prior sessions were circling: no excluded
-- seed reverses, equivalently every reversing seed is transport-admissible
-- (`seedS a = 1`).  This turns the long-standing structural CONJECTURE into a
-- THEOREM (the analytically-hard density-1 forward direction is the only part of
-- Erdős 1064 OQ-03 that stays open).
-- ---------------------------------------------------------------------------

/-- **No excluded seed reverses.**  Every odd `a ≥ 3` with `seedS a ≥ 2` (the
    excluded regime, where the first cototient step has 2-adic valuation `≥ 2`)
    classifies away from `.lt`.  Proof: such `a` is a prime power `p^k` with
    `p ≡ 3 (mod 4)` (`seedS_ge_two_iff_totient_mod_four` composed with
    `totient_mod_four_eq_two_iff_prime_pow_three_mod_four`), and every such power
    never reverses (`classifySeed_prime_pow_three_mod_four_ne_lt`). -/
theorem excluded_seed_never_reverses {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (hexcl : 2 ≤ seedS a) : classifySeed a ≠ Ordering.lt := by
  have hφ4 : Nat.totient a % 4 = 2 := (seedS_ge_two_iff_totient_mod_four ha ha3).1 hexcl
  obtain ⟨p, k, hp, hp3, hk, rfl⟩ :=
    (totient_mod_four_eq_two_iff_prime_pow_three_mod_four ha ha3).1 hφ4
  exact classifySeed_prime_pow_three_mod_four_ne_lt hp hp3 hk

/-- **Every reversing seed is transport-admissible (`seedS a = 1`).**  The
    contrapositive of `excluded_seed_never_reverses`: if the family `a·2^(k+1)`
    reverses (`classifySeed a = .lt`) then the first cototient step of `a` has
    2-adic valuation exactly one.  This is the previously-conjectural structural
    characterisation of the reversal regime, now proven. -/
theorem reversal_seed_transport_admissible {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (h : classifySeed a = Ordering.lt) : seedS a = 1 := by
  have hs1 : 1 ≤ seedS a := (seed_spec ha3).2.2.1
  by_contra hne
  exact excluded_seed_never_reverses ha ha3 (by omega) h

/-- **`ReversalSet` form of the structural dichotomy.**  Any member
    `n = a·2^(k+1)` of `ReversalSet` (odd seed `a ≥ 3`) has `seedS a = 1`: every
    actual totient-inequality reversal occurs strictly inside the
    transport-admissible regime. -/
theorem reversal_mem_implies_transport_regime {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (k : ℕ) (h : a * 2 ^ (k + 1) ∈ ReversalSet) : seedS a = 1 :=
  reversal_seed_transport_admissible ha ha3 ((classifySeed_lt_iff ha ha3 k).1 h)

/-- **Concrete arithmetic necessary condition for reversal: `4 ∣ φ(a)`.**  The
    structural dichotomy `reversal_seed_transport_admissible` places every
    reversing seed in the transport-admissible regime `seedS a = 1`, and
    `seedS_eq_one_iff_four_dvd_totient` translates that abstract 2-adic condition
    into a divisibility statement purely about the classical Euler totient of the
    seed.  So a *checkable* necessary condition for the family `a·2^(k+1)` to
    reverse the totient inequality is simply `4 ∣ φ(a)`.  (Consistent with every
    known reversal seed: `φ(21)=12`, `φ(55)=40`, `φ(129)=84`, `φ(165)=80`,
    `φ(175)=120` are all divisible by `4`.) -/
theorem reversal_seed_four_dvd_totient {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (h : classifySeed a = Ordering.lt) : 4 ∣ Nat.totient a :=
  (seedS_eq_one_iff_four_dvd_totient ha ha3).1 (reversal_seed_transport_admissible ha ha3 h)

/-- **`ReversalSet` form of the `4 ∣ φ(a)` necessary condition.**  Any member
    `n = a·2^(k+1)` of `ReversalSet` (odd seed `a ≥ 3`) has `4 ∣ φ(a)`: every
    actual totient-inequality reversal is supported on a seed whose totient is a
    multiple of four.  A concrete corollary of the structural dichotomy that can
    be tested by a single divisibility check on `φ(a)`. -/
theorem reversal_mem_four_dvd_totient {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (k : ℕ) (h : a * 2 ^ (k + 1) ∈ ReversalSet) : 4 ∣ Nat.totient a :=
  reversal_seed_four_dvd_totient ha ha3 ((classifySeed_lt_iff ha ha3 k).1 h)

/-- Sanity check at the smallest reversing seed `21`: `φ(21) = 12` is divisible by
    `4`, as forced by `reversal_seed_four_dvd_totient` (`classifySeed 21 = .lt`). -/
theorem reversal_four_dvd_totient_21 : 4 ∣ Nat.totient 21 :=
  reversal_seed_four_dvd_totient (by decide) (by norm_num) classifySeed_21'

-- ----------------------------------------------------------------------------
-- REVERSAL ENGINE on the transport-admissible regime (`seedS a = 1`)
-- ----------------------------------------------------------------------------
-- The excluded regime (`seedS a ≥ 2`) has two engines forcing the classifier
-- away from reversal: `classifySeed_ne_lt_of_excess_bound` (rules out `.lt`) and
-- `classifySeed_gt_of_excess_bound` (forces `.gt`).  The transport-admissible
-- regime `seedS a = 1` — where `reversal_seed_transport_admissible` proves EVERY
-- reversal lives — had no companion engine FORCING `.lt`.  We supply one on the
-- large explicit sub-regime where the second landing constant is a *prime*
-- (`seedE a` prime), turning the empirically-observed "reversals cluster on prime
-- landings" into an EXACT arithmetic criterion.

/-- **Reversal criterion on prime landings (transport-admissible regime).**  For
    an odd seed `a ≥ 3` in the transport-admissible regime `seedS a = 1` whose
    landing constant has a *prime* odd part (`seedE a` prime), the whole family
    `n = a·2^(k+1)` reverses (`classifySeed a = .lt`) **iff** the single
    seed-arithmetic inequality
    `φ(seedB a) + 2^{seedT a} < 2·(a − φ(a))` holds.

    Mechanism (`seedS a = 1`, so `2a − φ(a) = 2·seedB a` and
    `2a − φ(seedB a) = seedE a · 2^{seedT a}`).  With `e := seedE a` prime,
    `φ(e) = e − 1`, so the classifier's comparison
    `φ(a) < φ(e)·2^{t−1} = e·2^{t−1} − 2^{t−1}` and the identity
    `e·2^{t−1} = a − φ(seedB a)/2` collapse (after doubling) to
    `φ(seedB a) + 2^{seedT a} < 2·(a − φ(a))`.

    This is the missing `.lt` companion to the excluded-regime engines
    `classifySeed_ne_lt_of_excess_bound` / `classifySeed_gt_of_excess_bound`, and
    it recovers every known prime-landing reversal seed uniformly:
    `21` (`b=15,t=1,e=17`), `55` (`b=35,t=1,e=43`), `129` (`b=87,e=101`),
    `175` (`b=115,e=131`) all satisfy the criterion, while the Sophie–Germain
    equality seeds `15,33,…` (also prime-landing) *fail* it, matching their `.eq`
    regime.  The prime-landing restriction is genuine: `165` (`b=125,e=115=5·23`
    composite) reverses yet lies outside this engine — reversals are not confined
    to prime landings. -/
theorem classifySeed_lt_iff_of_seedS_one_seedE_prime {a : ℕ} (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime) :
    classifySeed a = Ordering.lt ↔
      Nat.totient (seedB a) + 2 ^ seedT a < 2 * (a - Nat.totient a) := by
  obtain ⟨hob, hoe, _, ht1, hstep, hCeq⟩ := seed_spec ha3
  -- `seedS a = 1` : first step `2a − φ(a) = 2·seedB a`, so `seedB a ≥ 3` (odd).
  have hφa_lt : Nat.totient a < a := Nat.totient_lt a (by omega)
  rw [hs1, pow_one] at hstep
  have hb2 : 2 ≤ seedB a := by omega
  have hb3 : 3 ≤ seedB a := by rcases hob with ⟨i, hi⟩; omega
  obtain ⟨jb, hjb⟩ := Nat.totient_even (show 2 < seedB a by omega)
  -- `seedS a = 1` in the landing identity : `2a − φ(seedB a) = seedE a · 2^{seedT a}`.
  rw [hs1] at hCeq
  simp only [Nat.sub_self, pow_zero, mul_one] at hCeq
  -- prime landing: `φ(seedE a) = seedE a − 1`, and the two powers of two split.
  have hepos : 0 < seedE a := hep.pos
  have hne : 0 < seedE a * 2 ^ seedT a := mul_pos hepos (pow_pos (by norm_num) _)
  have hφa_le : Nat.totient a ≤ a := Nat.totient_le a
  have hP : (2 : ℕ) ^ seedT a = 2 * 2 ^ (seedT a - 1) := by
    conv_lhs => rw [show seedT a = (seedT a - 1) + 1 from by omega, pow_succ]
    ring
  have hEPt : seedE a * 2 ^ seedT a = 2 * (seedE a * 2 ^ (seedT a - 1)) := by
    rw [hP]; ring
  have hφe : Nat.totient (seedE a) = seedE a - 1 := Nat.totient_prime hep
  have hsub : Nat.totient (seedE a) * 2 ^ (seedT a - 1)
      = seedE a * 2 ^ (seedT a - 1) - 2 ^ (seedT a - 1) := by
    rw [hφe, Nat.sub_one_mul]
  have hEPge : 2 ^ (seedT a - 1) ≤ seedE a * 2 ^ (seedT a - 1) :=
    Nat.le_mul_of_pos_left _ hepos
  -- unfold the classifier and discharge the resulting linear equivalence
  simp only [classifySeed]
  rw [compare_lt_iff_lt, hsub]
  omega

/-- **Prime-landing reversal family.**  Under the hypotheses of
    `classifySeed_lt_iff_of_seedS_one_seedE_prime` together with the criterion
    inequality, the *entire* family `n = a·2^(k+1)` lies in `ReversalSet`:
    `φ(n) < φ(D(n))` for every `k`.  This packages the criterion into an
    infinitely-often reversal statement for each qualifying seed (e.g. `a = 21`
    gives `42, 84, 168, …`; `a = 55` gives `110, 220, …`). -/
theorem prime_landing_family_reversal {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime)
    (hcrit : Nat.totient (seedB a) + 2 ^ seedT a < 2 * (a - Nat.totient a))
    (k : ℕ) : a * 2 ^ (k + 1) ∈ ReversalSet := by
  rw [classifySeed_lt_iff ha ha3 k]
  exact (classifySeed_lt_iff_of_seedS_one_seedE_prime ha3 hs1 hep).2 hcrit

/-- **Prime-landing trichotomy (the full classifier value).**  For a transport-
    admissible seed with a *prime* landing (`seedS a = 1`, `seedE a` prime), the
    entire computable classifier collapses to a single two-term comparison:
    `classifySeed a = compare (φ(seedB a) + 2^{seedT a}) (2·(a − φ(a)))`.

    This is the common refinement of `classifySeed_lt_iff_of_seedS_one_seedE_prime`
    (the `.lt` case) and its two missing companions: it decides *all three* regimes
    of the prime-landing family through one linear criterion, exactly mirroring how
    `classifySeed_classifies` decides the general family through `compare (φ a)
    (φ(seedE a)·2^{seedT a−1})`.  Reading off the three `Ordering` values gives the
    reversal / equality / forward corollaries below.

    Mechanism: with `s = 1` the two seed identities are `2a − φ(a) = 2·seedB a` and
    `2a − φ(seedB a) = seedE a·2^{seedT a}`.  Primality of `e := seedE a` gives
    `φ(e) = e − 1`, so the classifier's compared quantity
    `φ(e)·2^{t−1} = e·2^{t−1} − 2^{t−1}` equals `(a − φ(seedB a)/2) − 2^{t−1}`.
    Doubling turns the comparison `φ(a) ⋛ φ(e)·2^{t−1}` into the stated
    `(φ(seedB a) + 2^{seedT a}) ⋛ 2·(a − φ(a))` (the halves and the even totient
    `φ(seedB a)` clear exactly), and the three `compare` branches agree termwise. -/
theorem classifySeed_eq_compare_of_seedS_one_seedE_prime {a : ℕ} (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime) :
    classifySeed a
      = compare (Nat.totient (seedB a) + 2 ^ seedT a) (2 * (a - Nat.totient a)) := by
  obtain ⟨hob, hoe, _, ht1, hstep, hCeq⟩ := seed_spec ha3
  have hφa_lt : Nat.totient a < a := Nat.totient_lt a (by omega)
  rw [hs1, pow_one] at hstep
  have hb2 : 2 ≤ seedB a := by omega
  have hb3 : 3 ≤ seedB a := by rcases hob with ⟨i, hi⟩; omega
  obtain ⟨jb, hjb⟩ := Nat.totient_even (show 2 < seedB a by omega)
  rw [hs1] at hCeq
  simp only [Nat.sub_self, pow_zero, mul_one] at hCeq
  have hepos : 0 < seedE a := hep.pos
  have hne : 0 < seedE a * 2 ^ seedT a := mul_pos hepos (pow_pos (by norm_num) _)
  have hφe : Nat.totient (seedE a) = seedE a - 1 := Nat.totient_prime hep
  have hp2 : 1 ≤ (2 : ℕ) ^ (seedT a - 1) := Nat.one_le_two_pow
  have hP : (2 : ℕ) ^ seedT a = 2 * 2 ^ (seedT a - 1) := by
    conv_lhs => rw [show seedT a = (seedT a - 1) + 1 from by omega, pow_succ]
    ring
  have hEPt : seedE a * 2 ^ seedT a = 2 * (seedE a * 2 ^ (seedT a - 1)) := by
    rw [hP]; ring
  have hsub : Nat.totient (seedE a) * 2 ^ (seedT a - 1)
      = seedE a * 2 ^ (seedT a - 1) - 2 ^ (seedT a - 1) := by
    rw [hφe, Nat.sub_one_mul]
  have hEPge : 2 ^ (seedT a - 1) ≤ seedE a * 2 ^ (seedT a - 1) :=
    Nat.le_mul_of_pos_left _ hepos
  simp only [classifySeed]
  rw [hsub]
  rcases lt_trichotomy (Nat.totient a)
      (seedE a * 2 ^ (seedT a - 1) - 2 ^ (seedT a - 1)) with h | h | h
  · rw [compare_lt_iff_lt.mpr h,
        compare_lt_iff_lt.mpr (show Nat.totient (seedB a) + 2 ^ seedT a
          < 2 * (a - Nat.totient a) by omega)]
  · rw [compare_eq_iff_eq.mpr h,
        compare_eq_iff_eq.mpr (show Nat.totient (seedB a) + 2 ^ seedT a
          = 2 * (a - Nat.totient a) by omega)]
  · rw [compare_gt_iff_gt.mpr h,
        compare_gt_iff_gt.mpr (show 2 * (a - Nat.totient a)
          < Nat.totient (seedB a) + 2 ^ seedT a by omega)]

/-- **Prime-landing equality criterion** (`.eq` companion of
    `classifySeed_lt_iff_of_seedS_one_seedE_prime`).  A transport-admissible seed
    with a prime landing is classified `eq` — the whole family `a·2^(k+1)` sits in
    the equality regime `φ(n) = φ(D(n))` — iff `φ(seedB a) + 2^{seedT a}` exactly
    balances `2·(a − φ(a))`.  (The Sophie–Germain seeds `3q` are instances: there
    `seedB = 2q+1`, `seedE = q`, and both sides equal `4q`.) -/
theorem classifySeed_eq_iff_of_seedS_one_seedE_prime {a : ℕ} (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime) :
    classifySeed a = Ordering.eq ↔
      Nat.totient (seedB a) + 2 ^ seedT a = 2 * (a - Nat.totient a) := by
  rw [classifySeed_eq_compare_of_seedS_one_seedE_prime ha3 hs1 hep, compare_eq_iff_eq]

/-- **Prime-landing forward criterion** (`.gt` companion of
    `classifySeed_lt_iff_of_seedS_one_seedE_prime`).  A transport-admissible seed
    with a prime landing is classified `gt` — the whole family `a·2^(k+1)` sits in
    the forward regime `φ(D(n)) < φ(n)` — iff `2·(a − φ(a))` strictly exceeds
    `φ(seedB a) + 2^{seedT a}`.  Together with the `.lt` and `.eq` criteria this
    completely settles every prime-landing seed by a single linear inequality. -/
theorem classifySeed_gt_iff_of_seedS_one_seedE_prime {a : ℕ} (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime) :
    classifySeed a = Ordering.gt ↔
      2 * (a - Nat.totient a) < Nat.totient (seedB a) + 2 ^ seedT a := by
  rw [classifySeed_eq_compare_of_seedS_one_seedE_prime ha3 hs1 hep, compare_gt_iff_gt]

/-- **Prime-landing equality family.**  The `.eq` analogue of
    `prime_landing_family_reversal`: under the hypotheses of
    `classifySeed_eq_iff_of_seedS_one_seedE_prime` together with the balance
    equality, the *entire* family `n = a·2^(k+1)` lies in `EqualitySet`
    (`φ(n) = φ(D(n))` for every `k`).  This packages the equality criterion into an
    infinitely-often statement for each qualifying seed (e.g. every Sophie–Germain
    seed `a = 3q`, cf. `mem_EqualitySet_sophieGermain`). -/
theorem prime_landing_family_equality {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime)
    (hcrit : Nat.totient (seedB a) + 2 ^ seedT a = 2 * (a - Nat.totient a))
    (k : ℕ) : a * 2 ^ (k + 1) ∈ EqualitySet := by
  rw [classifySeed_eq_iff ha ha3 k]
  exact (classifySeed_eq_iff_of_seedS_one_seedE_prime ha3 hs1 hep).2 hcrit

/-- **Prime-landing forward family.**  The `.gt` analogue of
    `prime_landing_family_reversal`: under the hypotheses of
    `classifySeed_gt_iff_of_seedS_one_seedE_prime` together with the strict forward
    inequality, the *entire* family `n = a·2^(k+1)` lies in `ForwardSet`
    (`φ(D(n)) < φ(n)` for every `k`).  With the reversal and equality families this
    completes the packaging of the prime-landing trichotomy into infinitely-often
    membership for all three regimes. -/
theorem prime_landing_family_forward {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a)
    (hs1 : seedS a = 1) (hep : (seedE a).Prime)
    (hcrit : 2 * (a - Nat.totient a) < Nat.totient (seedB a) + 2 ^ seedT a)
    (k : ℕ) : a * 2 ^ (k + 1) ∈ ForwardSet := by
  rw [classifySeed_gt_iff ha ha3 k]
  exact (classifySeed_gt_iff_of_seedS_one_seedE_prime ha3 hs1 hep).2 hcrit

-- ----------------------------------------------------------------------------
-- A Sophie–Germain–indexed EQUALITY family: `n = 3q·2^(k+1)` with `2q+1` prime
-- ----------------------------------------------------------------------------

/-- **Sophie–Germain equality family.**  For every prime `q ≥ 5` whose associate
    `2q+1` is *also* prime (i.e. `q` a Sophie Germain prime), the seed `a = 3q`
    lands the *entire* family `n = 3q·2^(k+1)` in the equality regime:
    `φ(n) = φ(D(n))` for all `k`.

    The mechanism is a clean collapse of the general criterion.  With `a = 3q`:

    * `2a − φ(a) = 6q − 2(q−1) = 2·(2q+1)`, so `s = 1`, `b = 2q+1` (odd);
    * the landing constant is `C = 2a − φ(b) = 6q − φ(2q+1)`, and because `2q+1`
      is prime `φ(2q+1) = 2q`, hence `C = 4q = q·2²`, so `t = 2`, `e = q`;
    * the classifier then compares `φ(a) = 2(q−1)` with `φ(e)·2^{t−1} = φ(q)·2
      = (q−1)·2`, which are **equal**.

    So the totient of the double iterate exactly balances the seed's totient
    along the whole 2-power tower.  This is a genuine infinite family of *new*
    equality seeds `3q ∈ {15, 33, 69, 87, 123, 159, …}` (one per Sophie Germain
    prime), unifying the previously isolated numerical fact `classify 15 = eq`
    into a parametric statement; the smallest instance `q = 5` recovers
    `15·2^(k+1)` (`mem_EqualitySet_family`). -/
theorem mem_EqualitySet_sophieGermain {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hsg : (2 * q + 1).Prime) (k : ℕ) :
    3 * q * 2 ^ (k + 1) ∈ EqualitySet := by
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes (by norm_num) hq).mpr (by omega)
  have hφ3 : Nat.totient 3 = 2 := Nat.totient_prime (by norm_num)
  have hφ3q : Nat.totient (3 * q) = 2 * (q - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hq, hφ3]
  have hφ2q1 : Nat.totient (2 * q + 1) = 2 * q := by
    rw [Nat.totient_prime hsg]; omega
  have hodd3q : Odd (3 * q) := by
    rcases hqodd with ⟨j, hj⟩; exact ⟨3 * j + 1, by omega⟩
  have hodd2q1 : Odd (2 * q + 1) := ⟨q, by ring⟩
  have hstep : 2 * (3 * q) - Nat.totient (3 * q) = 2 ^ 1 * (2 * q + 1) := by
    have e1 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [hφ3q, e1]; omega
  have hC : 2 * (3 * q) - Nat.totient (2 * q + 1) * 2 ^ (1 - 1) = q * 2 ^ 2 := by
    have e1 : (2 : ℕ) ^ (1 - 1) = 1 := by norm_num
    have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [hφ2q1, e1, e2, mul_one]; omega
  rw [dblIter_equality_iff_general hodd3q hodd2q1 hqodd (le_refl 1) (by norm_num)
        hstep hC k, hφ3q, Nat.totient_prime hq]
  have e3 : (2 : ℕ) ^ (2 - 1) = 2 := by norm_num
  rw [e3]; ring

/-- **Classifier value on Sophie–Germain seeds.**  Specialising the equality
    family through `classifySeed_eq_iff`: every Sophie Germain seed `3q`
    (`q, 2q+1` both prime, `q ≥ 5`) is classified `eq` by the total decision
    procedure. -/
theorem classifySeed_sophieGermain_eq {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hsg : (2 * q + 1).Prime) : classifySeed (3 * q) = Ordering.eq := by
  have hodd3q : Odd (3 * q) := by
    have hqodd : Odd q := hq.odd_of_ne_two (by omega)
    rcases hqodd with ⟨j, hj⟩; exact ⟨3 * j + 1, by omega⟩
  exact (classifySeed_eq_iff hodd3q (by omega) 1).mp
    (mem_EqualitySet_sophieGermain hq hq5 hsg 1)

-- ----------------------------------------------------------------------------
-- A prime-indexed FORWARD family: `n = 5q·2^(k+1)` with `q ≡ 1 (mod 4)`,
-- `q ≥ 13`, and `3q+2` prime
-- ----------------------------------------------------------------------------

/-- **A parametric forward family.**  For every prime `q ≥ 13` with `q ≡ 1 (mod 4)`
    whose associate `3q+2` is *also* prime, the seed `a = 5q` lands the *entire*
    family `n = 5q·2^(k+1)` in the forward regime `φ(D(n)) < φ(n)` for all `k`.
    This is the forward analogue of the Sophie–Germain equality family
    `mem_EqualitySet_sophieGermain`: a single prime side-condition pins the whole
    2-power tower into one regime, giving a new infinite *candidate* family of
    forward seeds `5q ∈ {65, 85, 145, 185, …}` (one per prime `q ≡ 1 (mod 4)` with
    `3q+2` prime).

    The mechanism is again a clean collapse of the general criterion, writing
    `q = 4m+1` (so `m ≥ 3`):

    * `2a − φ(a) = 10q − 4(q−1) = 6q+4 = 2·(3q+2)`, so `s = 1`, `b = 3q+2` (odd);
    * because `3q+2` is prime, `φ(b) = 3q+1`, and the landing constant is
      `C = 2a − φ(b) = 10q − (3q+1) = 7q−1 = (14m+3)·2¹`, so `t = 1`, `e = 14m+3`
      (odd, since `7q−1 ≡ 2 (mod 4)` when `q ≡ 1`);
    * the classifier then compares `φ(e)·2^{t−1} = φ(14m+3)` with `φ(a) = 16m`.

    Crucially the forward direction needs **no** knowledge of the factorisation of
    the landing `e`: the uniform upper bound `φ(e) ≤ e−1 = 14m+2` already beats
    `φ(a) = 16m` for every `m ≥ 2` (i.e. `q ≥ 9`), so `φ(e) < φ(a)` and the family
    is forward.  This is the same "bound `φ(e) ≤ e−1` from above" device that ruled
    the reversal regime out of the prime-triple family — here it *establishes* a
    regime instead of excluding one.  The boundary case `q = 5` (`a = 25 = 5²`) is
    excluded by `q ≥ 13`; there the inequality degenerates to equality. -/
theorem mem_ForwardSet_fiveTimes {q : ℕ} (hq : q.Prime) (hq13 : 13 ≤ q)
    (hq1 : q % 4 = 1) (hb : (3 * q + 2).Prime) (k : ℕ) :
    5 * q * 2 ^ (k + 1) ∈ ForwardSet := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have hcop : Nat.Coprime 5 (4 * m + 1) :=
    (Nat.coprime_primes (by norm_num) hq).mpr (by omega)
  -- φ(a) = 16m
  have hφa : Nat.totient (5 * (4 * m + 1)) = 16 * m := by
    rw [Nat.totient_mul hcop, show Nat.totient 5 = 4 from by decide,
        Nat.totient_prime hq]; omega
  -- φ(b) = 12m+4  (b = 3q+2 = 12m+5 prime)
  have hφb : Nat.totient (3 * (4 * m + 1) + 2) = 12 * m + 4 := by
    rw [Nat.totient_prime hb]; omega
  -- oddness of the three odd data
  have ha_odd : Odd (5 * (4 * m + 1)) := Nat.odd_iff.mpr (by omega)
  have hb_odd : Odd (3 * (4 * m + 1) + 2) := Nat.odd_iff.mpr (by omega)
  have he_odd : Odd (14 * m + 3) := Nat.odd_iff.mpr (by omega)
  -- transport data:  2a − φ(a) = 2¹·b  and  2a − φ(b)·2^(s−1) = e·2¹
  have p0 : (2 : ℕ) ^ (1 - 1) = 1 := by norm_num
  have p1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have hstep : 2 * (5 * (4 * m + 1)) - Nat.totient (5 * (4 * m + 1))
      = 2 ^ 1 * (3 * (4 * m + 1) + 2) := by rw [hφa, p1]; omega
  have hC : 2 * (5 * (4 * m + 1)) - Nat.totient (3 * (4 * m + 1) + 2) * 2 ^ (1 - 1)
      = (14 * m + 3) * 2 ^ 1 := by rw [hφb, p0, p1]; omega
  -- feed the k-free forward criterion; the sign inequality needs only φ(e) ≤ e−1
  rw [dblIter_forward_iff_general ha_odd hb_odd he_odd (le_refl 1) (le_refl 1)
        hstep hC k, hφa, p0, mul_one]
  have hpe : Nat.totient (14 * m + 3) < 14 * m + 3 := Nat.totient_lt _ (by omega)
  omega

/-- **Classifier value on the forward family seeds.**  Specialising through
    `classifySeed_gt_iff`: every seed `5q` in the parametric forward family
    (`q` prime, `q ≥ 13`, `q ≡ 1 (mod 4)`, `3q+2` prime) is classified `gt` by the
    total decision procedure. -/
theorem classifySeed_fiveTimes_gt {q : ℕ} (hq : q.Prime) (hq13 : 13 ≤ q)
    (hq1 : q % 4 = 1) (hb : (3 * q + 2).Prime) : classifySeed (5 * q) = Ordering.gt := by
  have hodd : Odd (5 * q) := by
    have hqodd : Odd q := hq.odd_of_ne_two (by omega)
    rcases hqodd with ⟨j, hj⟩; exact ⟨5 * j + 2, by omega⟩
  exact (classifySeed_gt_iff hodd (by omega) 1).mp
    (mem_ForwardSet_fiveTimes hq hq13 hq1 hb 1)

-- ----------------------------------------------------------------------------
-- A prime-triple–indexed REVERSAL family: `n = (18m+3)·2^(k+1)`
-- ----------------------------------------------------------------------------

/-- **A parametric reversal family.**  For every `m ≥ 1` such that the three
    numbers `4m+1`, `6m+1`, `14m+3` are *all* prime, the seed `a = 18m+3`
    (`= 3·(6m+1)`) lands the *entire* family `n = (18m+3)·2^(k+1)` in the reversal
    regime `φ(n) < φ(D(n))` for all `k`.  This is the reversal analogue of the
    Sophie–Germain equality family `mem_EqualitySet_sophieGermain` and the
    parametric forward family `mem_ForwardSet_fiveTimes`, completing the trichotomy
    of *k*-free parametric seed families (equality / forward / **reversal**).  It
    unifies the previously isolated reversal seeds `21` (`m=1`) and `129` (`m=7`)
    into a single parametric statement; the next member is `453` (`m=25`, giving
    `4m+1=101`, `6m+1=151`, `14m+3=353` all prime).

    Mechanism (a clean collapse of the general reversal criterion
    `dblIter_reversal_iff_general`):

    * `a = 3·(6m+1)` so `φ(a) = 2·6m = 12m`;
    * `2a − φ(a) = (36m+6) − 12m = 24m+6 = 2·(12m+3)`, so `s = 1`,
      `b = 12m+3 = 3·(4m+1)` (odd) and `φ(b) = 2·4m = 8m`;
    * the landing constant is `C = 2a − φ(b) = (36m+6) − 8m = 28m+6 = (14m+3)·2¹`,
      so `t = 1`, `e = 14m+3` (odd);
    * the classifier compares `φ(e)·2^{t−1} = φ(14m+3) = 14m+2` against
      `φ(a) = 12m`, and `12m < 14m+2` holds for **every** `m`, so the family
      reverses.

    All three primality conditions are load-bearing: `6m+1` and `4m+1` give the
    clean totient values `φ(a) = 12m`, `φ(b) = 8m`, while the *reversal* itself
    needs the lower bound `φ(e) = 14m+2 > 12m`, which requires `14m+3` prime — for a
    composite landing `φ(e)` could drop below `12m` and the family would not
    reverse.  (The restriction to the semiprime landing `b = 3·(4m+1)` is why the
    other observed reversal seeds `55 = 5·11`, `175 = 5²·7` — whose seeds are of the
    form `5q`, not `3q` — lie outside this particular family; reversals are not
    confined to it.) -/
theorem mem_ReversalSet_primeTriple {m : ℕ} (hm : 1 ≤ m)
    (hp : (4 * m + 1).Prime) (hq : (6 * m + 1).Prime) (he : (14 * m + 3).Prime)
    (k : ℕ) : (18 * m + 3) * 2 ^ (k + 1) ∈ ReversalSet := by
  have hcopa : Nat.Coprime 3 (6 * m + 1) :=
    (Nat.coprime_primes (by norm_num) hq).mpr (by omega)
  have hcopb : Nat.Coprime 3 (4 * m + 1) :=
    (Nat.coprime_primes (by norm_num) hp).mpr (by omega)
  -- φ(a) = 12m  (a = 18m+3 = 3·(6m+1))
  have hφa : Nat.totient (18 * m + 3) = 12 * m := by
    rw [show 18 * m + 3 = 3 * (6 * m + 1) from by ring, Nat.totient_mul hcopa,
        show Nat.totient 3 = 2 from by decide, Nat.totient_prime hq]; omega
  -- φ(b) = 8m  (b = 12m+3 = 3·(4m+1))
  have hφb : Nat.totient (12 * m + 3) = 8 * m := by
    rw [show 12 * m + 3 = 3 * (4 * m + 1) from by ring, Nat.totient_mul hcopb,
        show Nat.totient 3 = 2 from by decide, Nat.totient_prime hp]; omega
  -- oddness of the three odd data
  have ha_odd : Odd (18 * m + 3) := Nat.odd_iff.mpr (by omega)
  have hb_odd : Odd (12 * m + 3) := Nat.odd_iff.mpr (by omega)
  have he_odd : Odd (14 * m + 3) := Nat.odd_iff.mpr (by omega)
  have p0 : (2 : ℕ) ^ (1 - 1) = 1 := by norm_num
  have p1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  -- transport data:  2a − φ(a) = 2¹·b  and  2a − φ(b)·2^(s−1) = e·2¹
  have hstep : 2 * (18 * m + 3) - Nat.totient (18 * m + 3)
      = 2 ^ 1 * (12 * m + 3) := by rw [hφa, p1]; omega
  have hC : 2 * (18 * m + 3) - Nat.totient (12 * m + 3) * 2 ^ (1 - 1)
      = (14 * m + 3) * 2 ^ 1 := by rw [hφb, p0, p1]; omega
  -- feed the k-free reversal criterion; reversal ⇔ φ(a) < φ(e)·2^(t−1) = 14m+2
  rw [dblIter_reversal_iff_general ha_odd hb_odd he_odd (le_refl 1) (le_refl 1)
        hstep hC k, hφa, p0, mul_one, Nat.totient_prime he]
  omega

/-- **Classifier value on the reversal family seeds.**  Specialising through
    `classifySeed_lt_iff`: every seed `18m+3` in the parametric reversal family
    (`m ≥ 1`, `4m+1`, `6m+1`, `14m+3` all prime) is classified `lt` by the total
    decision procedure. -/
theorem classifySeed_primeTriple_lt {m : ℕ} (hm : 1 ≤ m)
    (hp : (4 * m + 1).Prime) (hq : (6 * m + 1).Prime) (he : (14 * m + 3).Prime) :
    classifySeed (18 * m + 3) = Ordering.lt := by
  have hodd : Odd (18 * m + 3) := Nat.odd_iff.mpr (by omega)
  exact (classifySeed_lt_iff hodd (by omega) 1).mp
    (mem_ReversalSet_primeTriple hm hp hq he 1)

-- ----------------------------------------------------------------------------
-- Concrete members of the prime-triple reversal family
-- ----------------------------------------------------------------------------
-- The parametric family `mem_ReversalSet_primeTriple` / `classifySeed_primeTriple_lt`
-- names three explicit reversal seeds in its docstring — `21` (`m=1`), `129`
-- (`m=7`) and `453` (`m=25`) — but only the smallest, `21`, was previously
-- formalised (`twentyone_smallest_reversing_seed`, `classifySeed_21'`).  We
-- discharge the two higher members as verified statements, extending the file's
-- concrete classifier catalogue (`classifySeed_3 … classifySeed_21`) onto the
-- reversal family and confirming the family is non-vacuous well beyond its least
-- element.  Both are pure instantiations of the parametric theorems; the three
-- primality side-conditions of each are closed by `norm_num`.

/-- **Concrete reversal seed `129 = 3·43` (`m = 7`).**  The three associated
    numbers `4·7+1 = 29`, `6·7+1 = 43`, `14·7+3 = 101` are all prime, so the entire
    family `129·2^(k+1)` reverses (`φ(n) < φ(D(n))`). -/
theorem mem_ReversalSet_129 (k : ℕ) : 129 * 2 ^ (k + 1) ∈ ReversalSet := by
  simpa using mem_ReversalSet_primeTriple (m := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) k

/-- **Classifier value on the seed `129`.**  Total decision procedure classifies
    `129` as `lt` (reversal). -/
theorem classifySeed_129 : classifySeed 129 = Ordering.lt := by
  simpa using classifySeed_primeTriple_lt (m := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Concrete reversal seed `453 = 3·151` (`m = 25`).**  The three associated
    numbers `4·25+1 = 101`, `6·25+1 = 151`, `14·25+3 = 353` are all prime, so the
    entire family `453·2^(k+1)` reverses — the third explicitly exhibited member of
    the prime-triple reversal family, beyond `21` (`m=1`) and `129` (`m=7`). -/
theorem mem_ReversalSet_453 (k : ℕ) : 453 * 2 ^ (k + 1) ∈ ReversalSet := by
  simpa using mem_ReversalSet_primeTriple (m := 25) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) k

/-- **Classifier value on the seed `453`.**  Total decision procedure classifies
    `453` as `lt` (reversal). -/
theorem classifySeed_453 : classifySeed 453 = Ordering.lt := by
  simpa using classifySeed_primeTriple_lt (m := 25) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- ----------------------------------------------------------------------------
-- A reversal seed OUTSIDE the prime-triple (`3q`) family: `55 = 5·11`
-- ----------------------------------------------------------------------------
-- The prime-triple family `mem_ReversalSet_primeTriple` collects reversal seeds
-- of the shape `18m+3 = 3·(6m+1)`.  The next-step note asked for an *analogous
-- infinite `5q` family* capturing the observed reversal seed `55 = 5·11`.  The
-- honest finding is that **no such clean infinite family exists**: the natural
-- `5·q` analogue `a = 5·(5m+1)`, `b = 5·(3m+1)`, landing `e = 19m+5` (all three
-- of `5m+1`, `3m+1`, `19m+5` prime) collapses the general criterion
-- `dblIter_reversal_iff_general` to the reversal condition
-- `φ(a) = 20m < φ(e) = 19m+4`, i.e. `m < 4` — a *bounded* window, in contrast to
-- the `3q` family whose margin `14m+2 − 12m = 2m+2 > 0` grows without bound.
-- Since `a = 25m+5` is odd only for even `m`, the only member is `m = 2`, the seed
-- `55` itself.  So `55` is genuinely isolated as a `5·(5m+1)` reversal, not the
-- head of an infinite family; we record it as a concrete catalogue member,
-- confirming (as the prime-triple docstring already notes) that reversals are not
-- confined to the `3q` family.

/-- **Classifier value on the seed `55`.**  Transport data: `b = 35 = 5·7`
    (`2·55 − φ(55) = 70 = 35·2¹`, so `s = 1`), landing `C = 2·55 − φ(35) = 86 = 43·2¹`
    (so `t = 1`, `e = 43` prime), and the classifier compares `φ(55) = 40` against
    `φ(43)·2^0 = 42`; `40 < 42`, so the total decision procedure classifies
    `55 = 5·11` as `lt` (reversal) — a `5q`-type seed outside the prime-triple
    (`3q`) reversal family. -/
theorem classifySeed_55 : classifySeed 55 = Ordering.lt := by
  rw [classifySeed_val (s := 1) (b := 35) (t := 1) (e := 43) (by decide) (by decide)
      (by norm_num [totient_55]) (by norm_num [totient_35])]
  rw [totient_55, totient_43]; decide

/-- **Reversal family `55·2^(k+1)`, outside the `3q` prime-triple family.**  Since
    `classifySeed 55 = lt`, the whole family lies in `ReversalSet` (`φ(n) < φ(D(n))`
    for every `k`), confirming reversals are not confined to the seeds `18m+3`. -/
theorem mem_ReversalSet_55 (k : ℕ) : 55 * 2 ^ (k + 1) ∈ ReversalSet :=
  (classifySeed_lt_iff (by decide) (by norm_num) k).mpr classifySeed_55

-- ----------------------------------------------------------------------------
-- The last isolated reversal seed of the original docstring: `175 = 5²·7`
-- ----------------------------------------------------------------------------
-- The original problem cited four isolated reversal seeds `21, 55, 129, 175`.
-- The prime-triple family `mem_ReversalSet_primeTriple` machine-classifies
-- `21` (`m=1`) and `129` (`m=7`); `classifySeed_55` catalogues `55 = 5·11`.
-- The remaining seed `175 = 5²·7` has yet a third shape — neither `18m+3` nor
-- `5·(5m+1)` — so it is recorded here as a standalone catalogue member.  With it,
-- every isolated reversal seed named in the original problem is machine-verified
-- to lie in `ReversalSet`.

/-- `φ(25) = 20`  (`25 = 5²`). -/
theorem totient_25 : Nat.totient 25 = 20 := by decide

/-- `φ(115) = 88`  (`115 = 5·23`, distinct primes). -/
theorem totient_115 : Nat.totient 115 = 88 := by
  rw [show (115 : ℕ) = 5 * 23 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(175) = 120`  (`175 = 25·7`, coprime factors). -/
theorem totient_175 : Nat.totient 175 = 120 := by
  rw [show (175 : ℕ) = 25 * 7 from rfl, Nat.totient_mul (by decide), totient_25,
      Nat.totient_prime (by norm_num)]

/-- `φ(131) = 130`  (`131` is prime). -/
theorem totient_131 : Nat.totient 131 = 130 := Nat.totient_prime (by norm_num)

/-- **Classifier value on the seed `175 = 5²·7`.**  Transport data: `b = 115 = 5·23`
    (`2·175 − φ(175) = 230 = 115·2¹`, so `s = 1`), landing `C = 2·175 − φ(115) = 262 =
    131·2¹` (so `t = 1`, `e = 131` prime), and the classifier compares `φ(175) = 120`
    against `φ(131)·2^0 = 130`; `120 < 130`, so the total decision procedure classifies
    `175 = 5²·7` as `lt` (reversal) — the third distinct reversal-seed shape, outside
    both the `3q` prime-triple family and the `5·(5m+1)` seed `55`. -/
theorem classifySeed_175 : classifySeed 175 = Ordering.lt := by
  rw [classifySeed_val (s := 1) (b := 115) (t := 1) (e := 131) (by decide) (by decide)
      (by norm_num [totient_175]) (by norm_num [totient_115])]
  rw [totient_175, totient_131]; decide

/-- **Reversal family `175·2^(k+1)`.**  Since `classifySeed 175 = lt`, the whole
    family lies in `ReversalSet`; combined with `mem_ReversalSet_55` and the
    prime-triple family (`21, 129`), every isolated reversal seed named in the
    original problem statement is now machine-verified. -/
theorem mem_ReversalSet_175 (k : ℕ) : 175 * 2 ^ (k + 1) ∈ ReversalSet :=
  (classifySeed_lt_iff (by decide) (by norm_num) k).mpr classifySeed_175

end Erdos1064OQ03
