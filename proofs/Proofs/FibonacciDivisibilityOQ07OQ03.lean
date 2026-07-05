import Mathlib

/-
# The Rank of Apparition: `k ∣ Fₙ ↔ (entry point of k) ∣ n`

For a fixed modulus `k ≥ 1`, the set of indices `n` at which `k` divides the
Fibonacci number `Fₙ` is exactly the set of multiples of a single index `α(k)`,
the **rank of apparition** (or *Fibonacci entry point*) of `k`.  This is the
exact divisibility characterization

  `k ∣ Fₙ  ↔  α(k) ∣ n`,

generalizing the modulus-specific corollaries `2 ∣ Fₙ ↔ 3 ∣ n`, `3 ∣ Fₙ ↔ 4 ∣ n`
of `fibonacci-divisibility-oq-07`, and dual to the parent's index-divisibility
statement `Fₘ ∣ Fₙ ↔ m ∣ n`.

Mathlib records the *strong divisibility* backbone
`Nat.fib_gcd : fib (gcd m n) = gcd (fib m) (fib n)` and its consequence
`Nat.fib_dvd : m ∣ n → fib m ∣ fib n`, but says nothing about the rank of
apparition itself: neither that it exists (that every `k ≥ 1` divides *some*
positive-index Fibonacci number) nor that it characterizes the divisibility set.

This file supplies both.

## The characterization from minimality

The heart of the matter needs no finiteness at all.  If `a` is *any* least
positive index with `k ∣ fib a`, then `k ∣ fib n ↔ a ∣ n`:

* (⟸) `a ∣ n` gives `fib a ∣ fib n` by `Nat.fib_dvd`, and `k ∣ fib a`
  transports across;
* (⟹) `k ∣ fib n` together with `k ∣ fib a` gives
  `k ∣ gcd (fib a) (fib n) = fib (gcd a n)` via `Nat.fib_gcd`, so `gcd a n` is a
  positive index (for `n > 0`) with `k ∣ fib (gcd a n)`; minimality forces
  `a ≤ gcd a n`, while `gcd a n ∣ a` forces `gcd a n ≤ a`, hence `gcd a n = a`
  and `a ∣ n`.

## Existence of the rank of apparition

That `α(k)` exists for every `k ≥ 1` is the substantive input.  We prove it by a
pigeonhole/periodicity argument on the pair sequence
`pₙ = (Fₙ, Fₙ₊₁) ∈ (ZMod k)²`.  The Fibonacci shift `(a, b) ↦ (b, a + b)` is a
*bijection* of `(ZMod k)²` (its inverse is `(a, b) ↦ (b − a, a)`), and
`pₙ₊₁ = shift pₙ`, so `pₙ = shiftⁿ p₀`.  Since `(ZMod k)²` is finite and `ℕ` is
infinite, two indices collide, `pᵢ = pⱼ` with `i < j`; injectivity of `shiftⁱ`
cancels the common prefix, giving `p₀ = p_{j−i}`.  Reading the first coordinate,
`F_{j−i} ≡ F₀ = 0 (mod k)`, so `k ∣ F_{j−i}` with `j − i > 0`.

`entryPoint k := Nat.find` of this existence is then a genuine, computable
definition, and the biconditional holds unconditionally for `k ≥ 1`.

Fully verified: 0 sorries, 0 axioms, no `native_decide`.  `decide` appears only
in the concrete examples to evaluate closed Fibonacci numerals `fib 1 … fib 5`,
which reduce in the kernel.
-/

namespace FibonacciDivisibilityOQ0703

open Nat

/-! ## The characterization from a least positive index -/

/-- **Rank-of-apparition characterization, from minimality.**  If `a` is a least
positive index with `k ∣ fib a` — i.e. `0 < a`, `k ∣ fib a`, and every positive
index `m` with `k ∣ fib m` satisfies `a ≤ m` — then for every `n`,
`k ∣ fib n ↔ a ∣ n`.

This is the mathematical core; it uses only `Nat.fib_dvd` and `Nat.fib_gcd` and
needs no hypothesis on `k` beyond the supplied minimal witness `a`. -/
theorem dvd_fib_iff_of_least {k a : ℕ} (ha : 0 < a) (hdvd : k ∣ fib a)
    (hleast : ∀ m, 0 < m → k ∣ fib m → a ≤ m) (n : ℕ) :
    k ∣ fib n ↔ a ∣ n := by
  constructor
  · intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact Dvd.intro 0 rfl
    · -- `k` divides `fib (gcd a n)` because it divides both `fib a` and `fib n`.
      have hkd : k ∣ fib (Nat.gcd a n) := by
        rw [Nat.fib_gcd]; exact Nat.dvd_gcd hdvd hn
      have hdpos : 0 < Nat.gcd a n := by
        rcases Nat.eq_zero_or_pos (Nat.gcd a n) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h; omega
        · exact h
      -- minimality (`a ≤ gcd`) and `gcd ∣ a` (`gcd ≤ a`) pin `gcd a n = a`.
      have hle : a ≤ Nat.gcd a n := hleast _ hdpos hkd
      have hge : Nat.gcd a n ≤ a := Nat.le_of_dvd ha (Nat.gcd_dvd_left a n)
      have heq : Nat.gcd a n = a := le_antisymm hge hle
      exact heq ▸ Nat.gcd_dvd_right a n
  · intro hn
    exact dvd_trans hdvd (Nat.fib_dvd a n hn)

/-! ## Existence of the rank of apparition via periodicity mod `k` -/

/-- The Fibonacci pair `(Fₙ, Fₙ₊₁)` reduced modulo `k`. -/
def fibPair (k n : ℕ) : ZMod k × ZMod k := ((fib n : ZMod k), (fib (n + 1) : ZMod k))

/-- The Fibonacci shift on pairs, `(a, b) ↦ (b, a + b)`, as an equivalence of
`(ZMod k)²` (inverse `(a, b) ↦ (b − a, a)`).  This is what makes the pair
sequence *purely* periodic. -/
def shift (k : ℕ) : ZMod k × ZMod k ≃ ZMod k × ZMod k where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by rintro ⟨a, b⟩; simp

@[simp] lemma shift_apply (k : ℕ) (p : ZMod k × ZMod k) :
    shift k p = (p.2, p.1 + p.2) := rfl

/-- One step of the pair sequence is one application of the shift. -/
lemma shift_fibPair (k n : ℕ) : shift k (fibPair k n) = fibPair k (n + 1) := by
  have h2 : (fib n : ZMod k) + (fib (n + 1) : ZMod k) = (fib (n + 2) : ZMod k) := by
    rw [fib_add_two]; push_cast; ring
  show ((fib (n + 1) : ZMod k), (fib n : ZMod k) + (fib (n + 1) : ZMod k))
      = ((fib (n + 1) : ZMod k), (fib (n + 1 + 1) : ZMod k))
  rw [Prod.mk.injEq]
  exact ⟨rfl, h2⟩

/-- The pair sequence is the shift orbit of the initial pair `(F₀, F₁) = (0, 1)`. -/
lemma fibPair_eq_iterate (k n : ℕ) : fibPair k n = (shift k)^[n] (fibPair k 0) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply, ← ih, shift_fibPair]

/-- From a repeat `fibPair k i = fibPair k j` with `i < j`, cancel the common
prefix (`shiftⁱ` is injective) to get `fibPair k 0 = fibPair k (j - i)`, whose
first coordinate says `k ∣ fib (j - i)` with `j - i > 0`. -/
private lemma exists_pos_dvd_of_pair_eq (k : ℕ) {i j : ℕ} (hlt : i < j)
    (hpair : fibPair k i = fibPair k j) : ∃ n, 0 < n ∧ k ∣ fib n := by
  refine ⟨j - i, by omega, ?_⟩
  have hinj : Function.Injective ((shift k)^[i]) := (shift k).injective.iterate i
  have hcol : fibPair k 0 = fibPair k (j - i) := by
    apply hinj
    have e1 : (shift k)^[i] (fibPair k 0) = fibPair k i := (fibPair_eq_iterate k i).symm
    have e2 : (shift k)^[i] (fibPair k (j - i)) = fibPair k (i + (j - i)) := by
      rw [← Function.iterate_add_apply, ← fibPair_eq_iterate]
    rw [e1, e2]
    have hij : i + (j - i) = j := by omega
    rw [hij]; exact hpair
  have hfst : ((fib 0 : ℕ) : ZMod k) = ((fib (j - i) : ℕ) : ZMod k) :=
    (Prod.ext_iff.mp hcol).1
  rw [fib_zero, Nat.cast_zero] at hfst
  exact (ZMod.natCast_eq_zero_iff _ _).mp hfst.symm

/-- **Existence of the rank of apparition.**  Every modulus `k ≥ 1` divides some
positive-index Fibonacci number.  Proof: the pair sequence `(Fₙ, Fₙ₊₁) mod k`
lives in the finite set `(ZMod k)²`, so by pigeonhole two indices collide; the
Fibonacci shift is a bijection, so the collision propagates back to index `0`. -/
theorem exists_pos_dvd_fib (k : ℕ) [NeZero k] : ∃ n, 0 < n ∧ k ∣ fib n := by
  obtain ⟨i, j, hij, hpair⟩ := Finite.exists_ne_map_eq_of_infinite (fibPair k)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact exists_pos_dvd_of_pair_eq k hlt hpair
  · exact exists_pos_dvd_of_pair_eq k hlt hpair.symm

/-! ## The entry point and the unconditional characterization -/

/-- The **rank of apparition** (Fibonacci entry point) of `k ≥ 1`: the least
positive index `n` with `k ∣ Fₙ`.  Total and computable, since existence is a
theorem. -/
def entryPoint (k : ℕ) [NeZero k] : ℕ := Nat.find (exists_pos_dvd_fib k)

lemma entryPoint_pos (k : ℕ) [NeZero k] : 0 < entryPoint k :=
  (Nat.find_spec (exists_pos_dvd_fib k)).1

lemma dvd_fib_entryPoint (k : ℕ) [NeZero k] : k ∣ fib (entryPoint k) :=
  (Nat.find_spec (exists_pos_dvd_fib k)).2

/-- Minimality of the entry point: any positive index at which `k` divides a
Fibonacci number is at least `entryPoint k`. -/
lemma entryPoint_le (k : ℕ) [NeZero k] {m : ℕ} (hm : 0 < m) (hd : k ∣ fib m) :
    entryPoint k ≤ m :=
  Nat.find_min' (exists_pos_dvd_fib k) ⟨hm, hd⟩

/-- **Main theorem — the rank of apparition characterizes Fibonacci
divisibility.**  For every `k ≥ 1` and every `n`,

  `k ∣ Fₙ  ↔  entryPoint k ∣ n`.

The divisibility set of `k` in the Fibonacci sequence is exactly the multiples of
the single index `entryPoint k`. -/
theorem dvd_fib_iff_entryPoint_dvd (k : ℕ) [NeZero k] (n : ℕ) :
    k ∣ fib n ↔ entryPoint k ∣ n :=
  dvd_fib_iff_of_least (entryPoint_pos k) (dvd_fib_entryPoint k)
    (fun _ hm hd => entryPoint_le k hm hd) n

/-! ## Concrete entry points

Verified via `dvd_fib_iff_of_least`, so no evaluation of `Nat.find` is needed —
only the finitely many small Fibonacci numerals below the claimed entry point. -/

/-- Entry point of `2` is `3`: `2 ∣ Fₙ ↔ 3 ∣ n`  (`F₃ = 2`, and `F₁ = F₂ = 1`). -/
example (n : ℕ) : 2 ∣ fib n ↔ 3 ∣ n := by
  refine dvd_fib_iff_of_least (by norm_num) (by decide) ?_ n
  intro m hm hd
  rcases m with _ | _ | _ | m
  · omega
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · omega

/-- Entry point of `3` is `4`: `3 ∣ Fₙ ↔ 4 ∣ n`  (`F₄ = 3`). -/
example (n : ℕ) : 3 ∣ fib n ↔ 4 ∣ n := by
  refine dvd_fib_iff_of_least (by norm_num) (by decide) ?_ n
  intro m hm hd
  rcases m with _ | _ | _ | _ | m
  · omega
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · omega

/-- Entry point of `5` is `5`: `5 ∣ Fₙ ↔ 5 ∣ n`  (`F₅ = 5`, the fixed point). -/
example (n : ℕ) : 5 ∣ fib n ↔ 5 ∣ n := by
  refine dvd_fib_iff_of_least (by norm_num) (by decide) ?_ n
  intro m hm hd
  rcases m with _ | _ | _ | _ | _ | m
  · omega
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · exact absurd hd (by decide)
  · omega

end FibonacciDivisibilityOQ0703
