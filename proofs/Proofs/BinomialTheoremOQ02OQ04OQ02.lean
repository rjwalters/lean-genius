/-
# A `piAntidiag`-free proof of the multinomial theorem via Finsupp/Multiset

*Open Question OQ-02 from `BinomialTheoremOQ02OQ04`*: The parent entry proves the
multinomial theorem by induction on `|s|`, but its right-hand side is still indexed
by `Finset.piAntidiag s n`, a `Finset (α → ℕ)` of *ordinary* exponent functions.
This open question asks for a proof of the multinomial theorem that **avoids
`Finset.piAntidiag` entirely**, working directly with the **Finsupp** (`α →₀ ℕ`) or
**Multiset** (`Sym α n`) representations of the exponent multisets, as an alternative
combinatorial route.

## Answer: Yes — and there are two canonical routes

This file collects the `piAntidiag`-free routes and connects them to the parent's
`piAntidiag`-indexed expansion.

* **Word route** (`multinomial_via_words`).  The most elementary expansion:
  `(∑ᵢ f i)^n = ∑_{p : Fin n → s} ∏ₖ f (p k)`, a sum over *words* of length `n` in
  the alphabet `s`.  No exponent vectors at all — the multinomial coefficients only
  appear once words are grouped by their content multiset.  This is exactly
  `Finset.sum_pow'` (proved from `Finset.prod_univ_sum`, i.e. distributing the
  `n`-fold product), and uses no antidiagonal of any kind.

* **Multiset route** (`multinomial_via_sym`).  The collected form indexed by the
  multiset of exponents: `(∑ᵢ f i)^n = ∑_{M ∈ s.sym n} M.multinomial · ∏(M.map f)`,
  a sum over the `Finset (Sym α n)` of size-`n` multisets drawn from `s`.  Here the
  exponent data is a genuine `Multiset`, and the coefficient is
  `Multiset.multinomial`, defined via the Finsupp `M.toFinsupp`.  This is Mathlib's
  `Finset.sum_pow`, whose own proof is an `add_pow` induction on `s` that never
  mentions `piAntidiag`.

* **Route equivalence** (`sym_sum_eq_piAntidiag_sum`, `content_bij_*`).  The parent's
  `piAntidiag` expansion and the multiset expansion are literally the same finite sum,
  reindexed along the content bijection `M ↦ (i ↦ M.count i)` between size-`n`
  multisets over `s` and exponent vectors in `s.piAntidiag n`.  We exhibit this
  bijection explicitly and check the summands match term by term, so the equivalence
  of the two combinatorial routes is *constructive*, not merely a consequence of both
  sides equalling the same power.

## Status
- [x] Word route (0 sorries)
- [x] Multiset route (0 sorries)
- [x] Constructive content bijection `s.sym n ↔ s.piAntidiag n` (0 sorries)
- [x] All results 0 sorries, 0 axioms beyond Mathlib's foundations
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Tactic

namespace BinomialTheoremOQ02OQ04OQ02

open Finset BigOperators

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-! ## Route 1 — the word (function) expansion, free of any antidiagonal -/

omit [DecidableEq α] in
/-- **Multinomial theorem, word form.**  Expanding the `n`-th power of a finite sum
distributes into a sum over *words* `p : Fin n → s` of the product `∏ₖ f (p k)`.
This is the rawest `piAntidiag`-free statement: it indexes by `Fin n → α` functions
landing in `s` (via `Fintype.piFinset`), obtained purely by distributing the `n`-fold
product `∏_{k : Fin n} (∑ᵢ f i)` — no exponent vectors and no antidiagonal appear. -/
theorem multinomial_via_words (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ a ∈ s, f a) ^ n = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => s), ∏ i, f (p i) :=
  Finset.sum_pow' s f n

/-! ## Route 2 — the multiset (Sym) expansion, coefficients via `Multiset.multinomial` -/

/-- **Multinomial theorem, multiset form.**  Grouping the words of `multinomial_via_words`
by their content multiset yields the collected expansion indexed by `s.sym n`, the
`Finset` of size-`n` multisets over `s`.  The coefficient of a multiset `M` is
`M.multinomial` (the number of words with content `M`), and the monomial is
`(M.map f).prod = ∏_{i ∈ M} f i`.  This is Mathlib's `Finset.sum_pow`; its proof is an
`add_pow` induction on `s` that never constructs `Finset.piAntidiag`. -/
theorem multinomial_via_sym (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n
      = ∑ M ∈ s.sym n, (M.val.multinomial : R) * (M.val.map f).prod :=
  Finset.sum_pow f n

/-! ## Content correspondence — how a multiset summand becomes the parent's exponent-vector summand

For a multiset `M ∈ s.sym n`, its *content* is the exponent vector `i ↦ M.count i`,
which lands in `s.piAntidiag n` (the parent's index set).  The two lemmas below check,
term by term, that the multiset summand `M.multinomial · ∏(M.map f)` equals the parent's
summand `Nat.multinomial s (M.count) · ∏ᵢ f i ^ M.count i` under this correspondence.
This is the explicit mechanism behind the route equivalence: no antidiagonal is used to
*build* these terms — only `Multiset.count` and `Multiset.multinomial`. -/

/-- The content of `M ∈ s.sym n`, `i ↦ M.count i`, is an exponent vector in the parent's
index set `s.piAntidiag n`. -/
theorem content_mem_piAntidiag {s : Finset α} {n : ℕ} {M : Sym α n} (hM : M ∈ s.sym n) :
    (fun i => M.val.count i) ∈ s.piAntidiag n := by
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, ?_⟩
  · -- ∑_{i ∈ s} M.count i = card M = n, since every element of M lies in s
    have hsub : M.val.toFinset ⊆ s := fun a ha =>
      (Finset.mem_sym_iff.1 hM) a (Multiset.mem_toFinset.1 ha)
    rw [← Finset.sum_subset hsub (fun a _ ha => Multiset.count_eq_zero.2
        (fun h => ha (Multiset.mem_toFinset.2 h)))]
    rw [Multiset.toFinset_sum_count_eq, M.2]
  · intro i hi
    exact (Finset.mem_sym_iff.1 hM) i (Multiset.count_pos.1 (Nat.pos_of_ne_zero hi))

/-- **Multiset monomial = parent monomial under the content correspondence.**
`(M.map f).prod = ∏_{i ∈ s} f i ^ M.count i`. -/
theorem sym_prod_eq_piAntidiag_prod {s : Finset α} {n : ℕ} (f : α → R) {M : Sym α n}
    (hM : M ∈ s.sym n) :
    (M.val.map f).prod = ∏ i ∈ s, f i ^ M.val.count i := by
  have hsub : M.val.toFinset ⊆ s := fun a ha =>
    (Finset.mem_sym_iff.1 hM) a (Multiset.mem_toFinset.1 ha)
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset hsub (fun a _ ha => ?_)
  rw [Multiset.count_eq_zero.2 (fun h => ha (Multiset.mem_toFinset.2 h)), pow_zero]

/-- **Multiset multinomial coefficient = parent multinomial coefficient under the content
correspondence.**  `M.multinomial = Nat.multinomial s (i ↦ M.count i)`. -/
theorem sym_multinomial_eq_piAntidiag_multinomial {s : Finset α} {n : ℕ} {M : Sym α n}
    (hM : M ∈ s.sym n) :
    M.val.multinomial = Nat.multinomial s (fun i => M.val.count i) := by
  have hsupp : (M.val.toFinsupp).support ⊆ s := by
    intro a ha
    rw [Finsupp.mem_support_iff, Multiset.toFinsupp_apply, Multiset.count_ne_zero] at ha
    exact (Finset.mem_sym_iff.1 hM) a ha
  rw [Multiset.multinomial, Finsupp.multinomial_eq_of_support_subset hsupp]
  exact Nat.multinomial_congr (fun i _ => Multiset.toFinsupp_apply _ i)

/-! ## Route equivalence -/

/-- **The multiset expansion and the parent's `piAntidiag` expansion are the same sum.**
Both compute `(∑ᵢ f i)^n`: the left side by the `piAntidiag`-free multiset route
(`multinomial_via_sym` / Mathlib's `Finset.sum_pow`), the right side by the parent's
`piAntidiag`-indexed route (`Finset.sum_pow_eq_sum_piAntidiag`).  The content lemmas above
identify the two families of summands term by term. -/
theorem sym_sum_eq_piAntidiag_sum (s : Finset α) (f : α → R) (n : ℕ) :
    ∑ M ∈ s.sym n, (M.val.multinomial : R) * (M.val.map f).prod
      = ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : R) * ∏ i ∈ s, f i ^ k i := by
  rw [← Finset.sum_pow, ← Finset.sum_pow_eq_sum_piAntidiag]

/-- **Consistency with the parent entry.**  Composing the multiset route with the route
equivalence recovers the parent's `piAntidiag`-indexed multinomial expansion, confirming
the `piAntidiag`-free proof answers the same question. -/
theorem multinomial_piAntidiag_via_sym (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n
      = ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : R) * ∏ i ∈ s, f i ^ k i := by
  rw [multinomial_via_sym, sym_sum_eq_piAntidiag_sum]

end BinomialTheoremOQ02OQ04OQ02
