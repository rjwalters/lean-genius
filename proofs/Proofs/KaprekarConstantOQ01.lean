import Mathlib

/-!
# Kaprekar's constant 6174

## What This Proves

Kaprekar's routine `T` acts on four-digit decimal strings (leading zeros allowed):
write the four digits in descending order to form `D`, in ascending order to form
`A`, and set `T(n) = D - A`.  Starting from any four-digit number whose digits are
**not all equal**, iterating `T` reaches **6174** — *Kaprekar's constant* — in at
most seven steps, and `6174` is the unique nonzero fixed point.

The main results are:

```
kaprekar_fixed          : kaprekarStep 6174 = 6174
kaprekar_converges      : n < 10000 → NonRepdigit n → kaprekarStep^[7] n = 6174
kaprekar_unique_fixed   : n < 10000 → NonRepdigit n → kaprekarStep n = n → n = 6174
kaprekar_bound_sharp    : ∃ n < 10000, NonRepdigit n ∧ kaprekarStep^[6] n ≠ 6174
```

Since `6174` is a fixed point, `kaprekarStep^[7] n = 6174` is exactly the statement
"`n` reaches `6174` within seven steps".  `kaprekar_bound_sharp` shows seven steps
are sometimes necessary, so the bound is tight.

## Strategy

`T` is defined by *pure arithmetic*: the four digits are extracted with `/` and `%`,
sorted ascending by an explicit five-comparator network built from `min`/`max`, and
recombined.  No `Nat.digits` or list `mergeSort` appears, so the map reduces quickly.
The bounded-convergence and uniqueness facts are finite statements over the 10000
four-digit strings and are discharged by `native_decide`.

## Status

`kaprekar_fixed` is kernel-checked (`decide`).  `kaprekar_unique_fixed` is derived
*structurally* from convergence (a fixed point is unchanged by seven iterations,
which equal `6174`), and `kaprekar_bound_sharp` is witnessed by the single string
`0014` via `decide`.  Only the bounded-convergence enumeration `kaprekar_converges_all`
uses `native_decide`, so `Lean.ofReduceBool` (compiled evaluation of a decidable
proposition) is the file's sole non-foundational axiom.

A fully `decide`-checked (0-axiom) version was attempted via the digit-multiset reduction
(`kaprekarStep n = kaprekarStep (canon n)`), which cuts the convergence enumeration from
10000 four-digit strings to the 715 sorted-digit representatives.  **This route is now
confirmed infeasible for kernel `decide`**: a companion built around
`∀ n < 10000, canon n = n → NonRepdigit n → kaprekarStep^[7] n = 6174 := by decide`
times out past 40 minutes even with a warm Mathlib cache, both with `Function.iterate` and
with an explicitly-unfolded seven-fold composition.  The wall is the `Nat.decidableBallLT`
term over the full `n < 10000` quantifier — the kernel must reduce/typecheck a proof term
proportional to the whole 10000-wide scan regardless of the cheap canonicality short-circuit,
so collapsing the *work* to 715 reductions does not collapse the *term*.  `native_decide`
remains the only feasible discharge, so `Lean.ofReduceBool` stands as the sole axiom.  The
one untested avenue is a hard-coded 715-element `List.all` decide (which sidesteps the
`decidableBallLT` term) plus a structural `canon n ∈ reps` completeness lemma; see the
problem knowledge base.
-/

namespace KaprekarConstantOQ01

/-- Sort four natural numbers into ascending order via a five-comparator
sorting network (Batcher / bubble network for `n = 4`). -/
def sortAsc4 (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let a' := min a b; let b' := max a b
  let c' := min c d; let d' := max c d
  let a'' := min a' c'; let c'' := max a' c'
  let b'' := min b' d'; let d'' := max b' d'
  let b''' := min c'' b''; let c''' := max c'' b''
  (a'', b''', c''', d'')

/-- One step of Kaprekar's routine on the four-digit decimal string of `n`
(leading zeros included).  Descending arrangement minus ascending arrangement. -/
def kaprekarStep (n : ℕ) : ℕ :=
  let a := n / 1000 % 10
  let b := n / 100 % 10
  let c := n / 10 % 10
  let d := n % 10
  let s := sortAsc4 a b c d
  let w := s.1; let x := s.2.1; let y := s.2.2.1; let z := s.2.2.2
  (z * 1000 + y * 100 + x * 10 + w) - (w * 1000 + x * 100 + y * 10 + z)

/-- The four-digit string of `n` does **not** have all digits equal. -/
def NonRepdigit (n : ℕ) : Prop :=
  ¬ (n / 1000 % 10 = n / 100 % 10 ∧ n / 100 % 10 = n / 10 % 10 ∧
      n / 10 % 10 = n % 10)

instance (n : ℕ) : Decidable (NonRepdigit n) := by unfold NonRepdigit; infer_instance

/-- `6174` is a fixed point of Kaprekar's routine. -/
theorem kaprekar_fixed : kaprekarStep 6174 = 6174 := by decide

/-- **Bounded convergence (enumerated form).** Every four-digit string with not all
digits equal reaches `6174` after at most seven steps of `T`. -/
theorem kaprekar_converges_all :
    ∀ n ∈ Finset.range 10000, NonRepdigit n → kaprekarStep^[7] n = 6174 := by
  native_decide

/-- **Bounded convergence.** For every `n < 10000` whose four-digit string is not a
repdigit, iterating Kaprekar's routine seven times yields `6174`. -/
theorem kaprekar_converges (n : ℕ) (h : n < 10000) (hn : NonRepdigit n) :
    kaprekarStep^[7] n = 6174 :=
  kaprekar_converges_all n (Finset.mem_range.mpr h) hn

/-- **Uniqueness of the fixed point.** `6174` is the unique fixed point of Kaprekar's
routine on four-digit non-repdigit strings.  No separate enumeration is needed: a fixed
point `n` is unchanged by *seven* iterations (`Function.iterate_fixed`), and seven
iterations land on `6174` by `kaprekar_converges`, so `n = 6174`. -/
theorem kaprekar_unique_fixed (n : ℕ) (h : n < 10000) (hn : NonRepdigit n)
    (hf : kaprekarStep n = n) : n = 6174 :=
  (Function.iterate_fixed hf 7).symm.trans (kaprekar_converges n h hn)

/-- **The bound is sharp.** The string `0014` still differs from `6174` after six
steps (`kaprekarStep^[6] 14 = 4176`), so seven steps are sometimes necessary.  A single
concrete witness suffices, checked by kernel `decide`. -/
theorem kaprekar_bound_sharp :
    ∃ n ∈ Finset.range 10000, NonRepdigit n ∧ kaprekarStep^[6] n ≠ 6174 :=
  ⟨14, Finset.mem_range.mpr (by omega), by decide, by decide⟩

end KaprekarConstantOQ01
