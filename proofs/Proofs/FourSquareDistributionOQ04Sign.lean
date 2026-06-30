import Mathlib

/-
# Four-Square Distribution — OQ-04: the sign-count half of the orbit-size lemma

## Context

`FourSquareDistributionOQ04Decomp.lean` reduces the whole open question to a single
orbit-size lemma `fiber_card_eq_contribution`: each `shape`-fiber of the
representation set has size

  (★)   `m! / ∏_v (count_v)! · 2^{#nonzero}`

This is the size of a `B_m = S_m ⋉ (ℤ/2)^m` orbit. The factor splits cleanly:

  (★) = (arrangement count `m! / ∏ count_v!`) · (sign count `2^{#nonzero}`).

This file proves the **sign-count half** in full, as standalone reusable
infrastructure, and records the precise decomposition blueprint reducing the
keystone to the single remaining arrangement-count lemma.

The sign count is the size of the fiber of the coordinatewise absolute-value map:
once the (signed) absolute values `g i = |f i|` are fixed, each coordinate `f i`
is recovered up to a sign — two choices `±g i` when `g i ≠ 0`, one choice when
`g i = 0`. Hence the fiber has size `2^{#{i : g i ≠ 0}}`.

The formula `(★)` itself was brute-force confirmed against the genuine fiber sizes
for all `m ≤ 5`, `n ≤ 12` (58 fibers, 0 mismatches); see
`research/problems/four-square-distribution-oq-04/verify_orbit_formula.py`.

Build status: PENDING (authored under a Docker + Aristotle backend outage,
both re-tested live this session). UNREGISTERED in `Proofs.lean`; the sign-count
proof uses only standard `Fintype.piFinset` / `Finset.prod` API.
-/

namespace FourSquareDistributionOQ04Sign

open Finset

/-- The sign-fiber of a target absolute-value assignment `g : Fin m → ℤ`:
all tuples `f` agreeing with `g` coordinatewise up to sign (`f i ∈ {g i, -g i}`).
For `g i = |f i|` this is exactly the set of sign-flips of a fixed representation. -/
def signFiber {m : ℕ} (g : Fin m → ℤ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset (fun i => ({g i, -g i} : Finset ℤ))

/-- The single-coordinate sign count: `{c, -c}` has two elements unless `c = 0`. -/
theorem card_pair_neg (c : ℤ) :
    ({c, -c} : Finset ℤ).card = if c = 0 then 1 else 2 := by
  by_cases h : c = 0
  · subst h; simp
  · rw [if_neg h, Finset.card_pair]
    intro hcontra
    exact h (by linarith)

/-- **Sign-count lemma (the easy half of the orbit-size formula).**
The number of sign-flips of a fixed coordinate profile `g` is `2` raised to the
number of nonzero coordinates. -/
theorem signFiber_card {m : ℕ} (g : Fin m → ℤ) :
    (signFiber g).card = 2 ^ ((univ : Finset (Fin m)).filter (fun i => g i ≠ 0)).card := by
  classical
  rw [signFiber, Fintype.card_piFinset]
  have hcard : ∀ i ∈ (univ : Finset (Fin m)),
      ({g i, -g i} : Finset ℤ).card = if g i = 0 then 1 else 2 :=
    fun i _ => card_pair_neg (g i)
  rw [Finset.prod_congr rfl hcard]
  rw [Finset.prod_ite (fun _ => (1 : ℕ)) (fun _ => (2 : ℕ))]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, ne_eq]

end FourSquareDistributionOQ04Sign

/-
## Decomposition blueprint for `fiber_card_eq_contribution` (the remaining open lemma)

With `signFiber_card` in hand, the keystone reduces to ONE standard lemma — the
multinomial arrangement count — via a fiberwise split over the absolute-value map
`absMap f = fun i => |f i|`:

1. `absFiber_eq_signFiber` :  for `f₀` a representative,
     `{f ∈ reps m n | absMap f = absMap f₀} = signFiber (absMap f₀)`,
   so each abs-profile fiber has size `2^{#nonzero}` by `signFiber_card`
   (here `#nonzero (absMap f) = #nonzero s` is constant on a shape-fiber).

2. `arrangement_card` (THE remaining open target, no obvious Mathlib lemma):
     `#{g : Fin m → ℤ | g i ≥ 0 ∀i, multiset(g) = s} = m! / ∏_v (count_v s)!`.
   This is the multiset-permutation / multinomial coefficient count. Candidate
   Mathlib leads to search in a build session: `Finset.card_... ` for the action
   of `Equiv.Perm (Fin m)` on functions, `Nat.multinomial`, or
   `Multiset.Nodup`/`Multiset.permutations` cardinalities.

3. `fiber_card_eq_contribution` then follows from
   `Finset.card_eq_sum_card_fiberwise` applied to `absMap` on the shape-fiber:
     fiber(s).card = ∑_{abs-profiles g of shape s} (signFiber g).card
                   = (arrangement_card) · 2^{#nonzero s}
                   = shapeContribution m s.

Step 2 is the sole genuine combinatorial residue; steps 1 and 3 are bookkeeping.
-/
