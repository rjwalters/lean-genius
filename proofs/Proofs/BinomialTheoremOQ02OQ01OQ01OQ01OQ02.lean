/-
# Multinomial Marginal Distribution is Binomial

## Open Question (slug: binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-02)

The parent file `BinomialTheoremOQ02OQ01OQ01.lean` defers (line 178, `sorry`)
the marginal-distribution law: in a `Multinomial(n; p)` distribution on the
alphabet `s`, the marginal distribution of the count `X i` of a single outcome
`i ∈ s` is `Binomial(n, p i)`. Concretely, summing the multinomial probability
mass over all compositions `k` of `n` on `s` with the `i`-coordinate fixed to
`m` collapses to the binomial mass:

  ∑_{k ∈ piAntidiag s n, k i = m} multinomial(s,k) · ∏_{j∈s} p j ^ k j
      = C(n,m) · p i ^ m · (1 - p i) ^ (n - m).

## Strategy (this file, ACT)

The proof is a reindex-then-fold:

1. **Reindex (Leaf A `marginal_sum_reindex`)**: the bijection
     {k ∈ piAntidiag s n | k i = m} ≃ piAntidiag (s.erase i) (n - m)
   with forward map `k ↦ Function.update k i 0` and inverse
   `f ↦ Function.update f i m`. (The forward image has `i`-coordinate 0 and
   support in `s.erase i`, summing to `n - m`; the inverse re-installs `m` at
   `i`.) This turns the constrained sum into an unconstrained sum over
   compositions of `n - m` on `s.erase i`.

2. **Coefficient split (Leaf B `multinomial_update_eq`)**: for `f` supported
   on `s.erase i` (so `f i = 0`) with `∑_{s.erase i} f = n - m`,
     multinomial s (update f i m) = C(n,m) · multinomial (s.erase i) f,
   via `Nat.multinomial_insert` on `s = insert i (s.erase i)` (here
   `(m) + (n-m) = n` uses `m ≤ n`).

3. **Product split (Leaf C `prod_update_eq`)**:
     ∏_{j∈s} p j ^ (update f i m) j = p i ^ m · ∏_{j∈s.erase i} p j ^ f j,
   via `Finset.prod_insert` on `s = insert i (s.erase i)` and
   `Function.update`.

4. **Power fold (in-line, Mathlib)**: the remaining inner sum is exactly the
   multinomial theorem on `s.erase i`:
     ∑_{f ∈ piAntidiag (s.erase i) (n-m)} multinomial(s.erase i) f · ∏ p^f
       = (∑_{j∈s.erase i} p j) ^ (n - m),
   which is `Finset.sum_pow_eq_sum_piAntidiag` reversed; then
   `Finset.sum_erase_eq_sub` and the normalization `∑_s p = 1` give
   `∑_{s.erase i} p = 1 - p i`.

## Mathlib API used (verified against mathlib4_docs, 2026-06-15)

  Nat.multinomial_insert (ha : a ∉ s) :
    multinomial (insert a s) f = (f a + ∑ i∈s, f i).choose (f a) * multinomial s f
  Finset.sum_pow_eq_sum_piAntidiag (s) (f) (n) :
    (∑ i∈s, f i)^n = ∑ k ∈ s.piAntidiag n, ↑(multinomial s k) * ∏ i∈s, f i ^ k i
  Finset.mem_piAntidiag : f ∈ s.piAntidiag n ↔ s.sum f = n ∧ ∀ i, f i ≠ 0 → i ∈ s
  Finset.insert_erase (h : a ∈ s) : insert a (s.erase a) = s
  Finset.not_mem_erase : a ∉ s.erase a
  Finset.sum_erase_eq_sub (h : a ∈ s) : (s.erase a).sum f = s.sum f - f a

## Status

The reduction (combining the leaves + the power fold) is written out. The three
combinatorial leaf lemmas are stated precisely and left as `sorry` — they are
self-contained, mechanical, and are ideal Aristotle targets (HARD-but-known).
Build-pending: Docker pool saturated and Aristotle backend offline this session.
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace BinomialMultinomialMarginal

open Finset BigOperators

variable {α : Type*} [DecidableEq α]

/-! ## Leaf A — the indexing bijection (Aristotle target)

Reindex the marginal sum over the bijection
`{k ∈ piAntidiag s n | k i = m} ≃ piAntidiag (s.erase i) (n - m)`,
forward `k ↦ update k i 0`, inverse `f ↦ update f i m`.

Proof route: `Finset.sum_nbij'` (or rewrite the filtered finset as an image of
`piAntidiag (s.erase i) (n-m)` under `f ↦ update f i m` and use
`Finset.sum_image`, the map being injective). Membership uses
`Finset.mem_filter`, `Finset.mem_piAntidiag`, `Finset.not_mem_erase`,
`Finset.ne_of_mem_erase`, `Finset.sum_erase_eq_sub`. The hypothesis `m ≤ n`
makes `n - m` the genuine residual mass. -/
theorem marginal_sum_reindex
    (s : Finset α) (n m : ℕ) (i : α) (hi : i ∈ s) (hm : m ≤ n)
    (G : (α → ℕ) → ℝ) :
    ∑ k ∈ (s.piAntidiag n).filter (fun k => k i = m), G k =
    ∑ f ∈ (s.erase i).piAntidiag (n - m), G (Function.update f i m) := by
  sorry

/-! ## Leaf B — multinomial coefficient split (Aristotle target)

For `f` supported on `s.erase i` (`f i = 0`) with `∑_{s.erase i} f = n - m` and
`m ≤ n`, installing `m` at coordinate `i` multiplies the multinomial coefficient
by `C(n,m)`. Route: `s = insert i (s.erase i)` via `Finset.insert_erase hi`,
then `Nat.multinomial_insert (Finset.not_mem_erase i s)`; evaluate
`Function.update` at `i` (`Function.update_self`) and off `i`
(`Function.update_of_ne` for `j ∈ s.erase i`, using `Finset.ne_of_mem_erase`);
finally `m + (n - m) = n` via `Nat.add_sub_cancel' hm`. -/
theorem multinomial_update_eq
    (s : Finset α) (i : α) (hi : i ∈ s) (m n : ℕ) (hm : m ≤ n) (f : α → ℕ)
    (hfi : f i = 0) (hfsum : ∑ j ∈ s.erase i, f j = n - m) :
    Nat.multinomial s (Function.update f i m)
      = n.choose m * Nat.multinomial (s.erase i) f := by
  sorry

/-! ## Leaf C — product split (Aristotle target)

`∏_{j∈s} p j ^ (update f i m) j = p i ^ m · ∏_{j∈s.erase i} p j ^ f j`.
Route: `s = insert i (s.erase i)` via `Finset.insert_erase hi`, then
`Finset.prod_insert (Finset.not_mem_erase i s)`; the `i`-factor is
`p i ^ (update f i m) i = p i ^ m` (`Function.update_self`) and the remaining
factors are unchanged (`Function.update_of_ne` with `Finset.ne_of_mem_erase`). -/
theorem prod_update_eq
    (s : Finset α) (p : α → ℝ) (i : α) (hi : i ∈ s) (m : ℕ) (f : α → ℕ) :
    ∏ j ∈ s, p j ^ (Function.update f i m) j
      = p i ^ m * ∏ j ∈ s.erase i, p j ^ f j := by
  sorry

/-! ## Main theorem — marginal distribution is binomial

Discharges `BinomialTheoremOQ02OQ01OQ01.multinomial_marginal_binomial`. -/
theorem multinomial_marginal_binomial
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) (m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ (s.piAntidiag n).filter (fun k => k i = m),
      (Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j =
    (Nat.choose n m : ℝ) * p i ^ m * (1 - p i) ^ (n - m) := by
  -- Step 1: reindex onto compositions of (n - m) on s.erase i (Leaf A).
  rw [marginal_sum_reindex s n m i hi hm
        (fun k => (Nat.multinomial s k : ℝ) * ∏ j ∈ s, p j ^ k j)]
  -- Step 2: simplify each summand using the coefficient split (B) and product
  -- split (C). For `f ∈ piAntidiag (s.erase i) (n-m)` we have `f i = 0` and
  -- `∑_{s.erase i} f = n - m` from `mem_piAntidiag`.
  have hsummand : ∀ f ∈ (s.erase i).piAntidiag (n - m),
      (Nat.multinomial s (Function.update f i m) : ℝ)
          * ∏ j ∈ s, p j ^ (Function.update f i m) j
        = ((Nat.choose n m : ℝ) * p i ^ m)
            * ((Nat.multinomial (s.erase i) f : ℝ) * ∏ j ∈ s.erase i, p j ^ f j) := by
    intro f hf
    rw [Finset.mem_piAntidiag] at hf
    obtain ⟨hfsum, hfsupp⟩ := hf
    have hfi : f i = 0 := by
      by_contra h
      exact (Finset.not_mem_erase i s) (hfsupp i h)
    rw [multinomial_update_eq s i hi m n hm f hfi hfsum,
        prod_update_eq s p i hi m f]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsummand]
  -- Step 3: pull the constant `C(n,m) · p i ^ m` out of the sum.
  rw [← Finset.mul_sum]
  -- Step 4: fold the inner weighted sum into a power (multinomial theorem).
  rw [← Finset.sum_pow_eq_sum_piAntidiag (s.erase i) p (n - m)]
  -- Step 5: `∑_{s.erase i} p = 1 - p i` from the normalization `∑_s p = 1`.
  rw [Finset.sum_erase_eq_sub hi, hp_sum]
  ring

end BinomialMultinomialMarginal
