/-
Four-Square Distribution — OQ-04: the multiset-arrangement count.

Let s be a multiset of integers with |s| = m. An "arrangement" of s is a function
g : Fin m → ℤ whose multiset of values { g 0, g 1, …, g (m-1) } equals s. Count them.

Claim. The number of arrangements of s equals the multinomial coefficient

    Nat.multinomial s.toFinset (fun v => s.count v)  =  m! / ∏_{v ∈ s} (count_v s)!,

the number of distinct orderings of a length-m word over the alphabet s.toFinset in
which each letter v appears exactly (s.count v) times.

This is the sign-free combinatorial heart of the orbit-size formula in
FourSquareDistributionOQ04Decomp/Sign/Keystone: every `shape`-fiber of the genuine
4-square representation set has size  (m! / ∏count!) · 2^{#nonzero}; the 2^{#nonzero}
sign factor is already proved (Sign.lean), and this multiset-arrangement count is the
remaining factor.

The statement is independently certified for all multisets over {0,1,2} of size m ≤ 6
by research/problems/four-square-distribution-oq-04/verify_orbit_formula.py
(check_arrangement).

Answer: |arrangements s| = Nat.multinomial s.toFinset s.count.
-/
import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace StatementOnly_FourSquareDistributionOQ04

open Finset

/-- The arrangements of a multiset `s` as functions `Fin m → ℤ`: all `g` whose
multiset of values is exactly `s`. Realized as a `Finset` on the finite box
`(s.toFinset)^m`, which is lossless since every value of an arrangement of `s`
lies in `s`. -/
def arrangements {m : ℕ} (s : Multiset ℤ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => s.toFinset)).filter
    (fun g => Multiset.map g (Finset.univ : Finset (Fin m)).val = s)

/-- **The multiset-arrangement count.** The number of arrangements of a size-`m`
multiset `s` is the multinomial coefficient `Nat.multinomial s.toFinset s.count`. -/
theorem arrangement_card {m : ℕ} (s : Multiset ℤ) (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card
      = Nat.multinomial s.toFinset (fun v => s.count v) := by
  sorry

-- Proof attempt: orbit–stabilizer for the precomposition action of `Equiv.Perm (Fin m)`
-- on functions `g : Fin m → ℤ`, defined by `σ • g := g ∘ σ⁻¹`. Aristotle is free to
-- ignore this sketch; it only seeds the MCTS prior.
--
-- Membership fact (proved separately, no sorry): `g ∈ arrangements s ↔
--   Multiset.map g (Finset.univ : Finset (Fin m)).val = s`, i.e. arrangements are
--   exactly the functions whose value-multiset is `s`; the box `(s.toFinset)^m` never
--   clips one because every value of such a `g` lies in `s`.
--
-- 1. Fix one arrangement `g₀ ∈ arrangements s` (nonempty since `|s| = m`; build `g₀`
--    from any enumeration of `s`). The `Equiv.Perm (Fin m)` action by precomposition
--    preserves the value-multiset: `Multiset.map (g ∘ σ⁻¹) univ.val =
--    Multiset.map g (Multiset.map σ⁻¹ univ.val) = Multiset.map g univ.val` since `σ⁻¹`
--    permutes `univ.val`. Hence the action restricts to `arrangements s`.
-- 2. The orbit of `g₀` is *all* of `arrangements s`: if `g` has the same value-multiset
--    as `g₀`, then `g` and `g₀` agree up to a permutation of the index set (two words
--    with equal letter-multisets differ by reindexing), giving `σ` with `g = g₀ ∘ σ⁻¹`.
-- 3. The stabilizer `{σ | g₀ ∘ σ⁻¹ = g₀}` is the group of index permutations fixing the
--    fibers of `g₀`; it is isomorphic to `∏_{v ∈ s.toFinset} Equiv.Perm (g₀⁻¹ {v})`,
--    of order `∏_{v} (s.count v)!` (each fiber `g₀⁻¹ {v}` has size `s.count v`).
-- 4. `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` then gives
--    `|arrangements s| · ∏_{v} (s.count v)! = |Equiv.Perm (Fin m)| = m!`.
-- 5. `Nat.multinomial_spec s.toFinset s.count` states
--    `(∏_{v} (s.count v)!) · Nat.multinomial s.toFinset s.count =
--      (∑_{v ∈ s.toFinset} s.count v)! = (Multiset.card s)! = m!`
--    (using `Multiset.toFinset_sum_count_eq` and `hm`). Cancel `∏_{v} (s.count v)!`
--    (positive) from steps 4 and 5 to conclude `|arrangements s| = multinomial`.
-- Precedent for the factorial bookkeeping: `Mathlib.Combinatorics.Enumerative.Bell`.

end StatementOnly_FourSquareDistributionOQ04
