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

The single-point fact `kaprekar_fixed` is kernel-checked (`decide`).  The
finite-domain enumerations (`kaprekar_converges`, `kaprekar_unique_fixed`,
`kaprekar_bound_sharp`) use `native_decide` and therefore depend on the
`Lean.ofReduceBool` axiom (compiled evaluation of a decidable proposition).
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

/-- **Uniqueness of the fixed point (enumerated form).** Among the four-digit
strings with not all digits equal, `6174` is the only fixed point of `T`. -/
theorem kaprekar_unique_fixed_all :
    ∀ n ∈ Finset.range 10000, NonRepdigit n → kaprekarStep n = n → n = 6174 := by
  native_decide

/-- **Uniqueness of the fixed point.** `6174` is the unique nonzero fixed point of
Kaprekar's routine on four-digit non-repdigit strings. -/
theorem kaprekar_unique_fixed (n : ℕ) (h : n < 10000) (hn : NonRepdigit n)
    (hf : kaprekarStep n = n) : n = 6174 :=
  kaprekar_unique_fixed_all n (Finset.mem_range.mpr h) hn hf

/-- **The bound is sharp.** Some four-digit non-repdigit string needs the full seven
steps: six are not enough. -/
theorem kaprekar_bound_sharp :
    ∃ n ∈ Finset.range 10000, NonRepdigit n ∧ kaprekarStep^[6] n ≠ 6174 := by
  native_decide

end KaprekarConstantOQ01
