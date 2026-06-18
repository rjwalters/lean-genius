import Mathlib

/-!
# Kaprekar's constant 6174 — axiom-free (kernel `decide`) variant

This is a companion to `Proofs.KaprekarConstantOQ01`.  The main file discharges the
bounded-convergence enumeration with `native_decide`, which trusts the compiler and so
depends on `Lean.ofReduceBool`.  This file removes that dependency: the convergence
enumeration is reduced from the 10000 four-digit strings to the **715 sorted-digit
representatives** and discharged by the *kernel* `decide`, leaving the file with no
non-foundational axioms.

## The reduction

`kaprekarStep` depends only on the *multiset* of digits: it sorts them before taking
the descending-minus-ascending difference.  Concretely, with

```
canon n = recombine (sortAsc4 (digits n))
```

the canonical form `canon n` has the same digits as `n` but already in ascending order,
and `kaprekarStep (canon n) = kaprekarStep n`.  Peeling one iterate then gives
`kaprekarStep^[7] n = kaprekarStep^[7] (canon n)`, so it suffices to check convergence on
canonical inputs.  The enumeration

```
conv_canon : ∀ n < 10000, canon n = n → NonRepdigit n → kaprekarStep^[7] n = 6174
```

still ranges over `n < 10000`, but the decidable guard `canon n = n` short-circuits the
~9285 non-canonical strings *before* the heavy `^[7]` reduction runs, so the kernel only
performs the 715 seven-step reductions.

## BUILD STATUS — UNVERIFIED (tooling blackout)

This file was written under a Docker/Aristotle blackout and is **not yet machine-checked**.
The structural lemmas (`kaprekarStep_canon`, `iterate7_canon`, the `canon` facts) are
routine `omega` arithmetic over `min`/`max` and div/mod-by-literal; the single open
feasibility question is whether the kernel `decide` in `conv_canon` completes in time on
715 seven-step reductions (GMP-accelerated Nat literals make this plausible but unconfirmed).
If `conv_canon`'s `decide` proves infeasible, fall back to `native_decide` there — the
uniqueness and sharpness results stay axiom-free regardless.  **Do not advertise this file
as verified / 0-axiom until `./proofs/scripts/docker-build.sh Proofs.KaprekarConstantOQ01ZeroAxiom`
is green.**
-/

namespace KaprekarConstantOQ01ZeroAxiom

/-- Sort four naturals ascending via a five-comparator sorting network. -/
def sortAsc4 (a b c d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let a' := min a b; let b' := max a b
  let c' := min c d; let d' := max c d
  let a'' := min a' c'; let c'' := max a' c'
  let b'' := min b' d'; let d'' := max b' d'
  let b''' := min c'' b''; let c''' := max c'' b''
  (a'', b''', c''', d'')

/-- One step of Kaprekar's routine on the four-digit decimal string of `n`. -/
def kaprekarStep (n : ℕ) : ℕ :=
  let a := n / 1000 % 10
  let b := n / 100 % 10
  let c := n / 10 % 10
  let d := n % 10
  let s := sortAsc4 a b c d
  let w := s.1; let x := s.2.1; let y := s.2.2.1; let z := s.2.2.2
  (z * 1000 + y * 100 + x * 10 + w) - (w * 1000 + x * 100 + y * 10 + z)

/-- Canonical form: the same four digits written in ascending order. -/
def canon (n : ℕ) : ℕ :=
  let a := n / 1000 % 10
  let b := n / 100 % 10
  let c := n / 10 % 10
  let d := n % 10
  let s := sortAsc4 a b c d
  s.1 * 1000 + s.2.1 * 100 + s.2.2.1 * 10 + s.2.2.2

/-- The four-digit string of `n` does not have all digits equal. -/
def NonRepdigit (n : ℕ) : Prop :=
  ¬ (n / 1000 % 10 = n / 100 % 10 ∧ n / 100 % 10 = n / 10 % 10 ∧
      n / 10 % 10 = n % 10)

instance (n : ℕ) : Decidable (NonRepdigit n) := by unfold NonRepdigit; infer_instance

/-- `kaprekarStep` only depends on the digit multiset, so it is unchanged by
canonicalisation.  Both sides reduce to descending-minus-ascending of the same four
sorted digits; `omega` discharges the div/mod/`min`/`max` bookkeeping. -/
theorem kaprekarStep_canon (n : ℕ) : kaprekarStep (canon n) = kaprekarStep n := by
  simp only [kaprekarStep, canon, sortAsc4]
  omega

/-- Peeling one iterate: `kaprekarStep^[7] n = kaprekarStep^[7] (canon n)`. -/
theorem iterate7_canon (n : ℕ) :
    kaprekarStep^[7] n = kaprekarStep^[7] (canon n) := by
  have e : ∀ m, kaprekarStep^[7] m = kaprekarStep^[6] (kaprekarStep m) := fun m => by
    rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply]
  rw [e n, e (canon n), kaprekarStep_canon]

/-- `canon n` is a four-digit string. -/
theorem canon_lt (n : ℕ) : canon n < 10000 := by
  simp only [canon, sortAsc4]; omega

/-- Canonicalisation is idempotent: a sorted string is its own canonical form. -/
theorem canon_idem (n : ℕ) : canon (canon n) = canon n := by
  simp only [canon, sortAsc4]; omega

/-- Canonicalisation preserves the not-all-equal property (it only permutes digits). -/
theorem nonRepdigit_canon (n : ℕ) (hn : NonRepdigit n) : NonRepdigit (canon n) := by
  simp only [NonRepdigit, canon, sortAsc4] at hn ⊢
  omega

/-- **Bounded convergence on canonical representatives.** Ranging over `n < 10000`, the
decidable guard `canon n = n` keeps only the 715 sorted-digit strings, so the kernel runs
just those seven-step reductions.  Discharged by kernel `decide` (no `Lean.ofReduceBool`). -/
theorem conv_canon :
    ∀ n < 10000, canon n = n → NonRepdigit n → kaprekarStep^[7] n = 6174 := by
  decide

/-- **Bounded convergence (general form), axiom-free.** Every four-digit non-repdigit
string reaches `6174` within seven steps. -/
theorem kaprekar_converges (n : ℕ) (h : n < 10000) (hn : NonRepdigit n) :
    kaprekarStep^[7] n = 6174 := by
  have key : kaprekarStep^[7] (canon n) = 6174 :=
    conv_canon (canon n) (canon_lt n) (canon_idem n) (nonRepdigit_canon n hn)
  rw [iterate7_canon]; exact key

/-- `6174` is a fixed point of Kaprekar's routine (kernel `decide`). -/
theorem kaprekar_fixed : kaprekarStep 6174 = 6174 := by decide

/-- **Uniqueness of the fixed point**, derived structurally from convergence: a fixed
point is unchanged by seven iterations, which land on `6174`. -/
theorem kaprekar_unique_fixed (n : ℕ) (h : n < 10000) (hn : NonRepdigit n)
    (hf : kaprekarStep n = n) : n = 6174 :=
  (Function.iterate_fixed hf 7).symm.trans (kaprekar_converges n h hn)

/-- **The bound is sharp.** The string `0014` still differs from `6174` after six steps,
so seven steps are sometimes necessary (kernel `decide` witness). -/
theorem kaprekar_bound_sharp :
    ∃ n ∈ Finset.range 10000, NonRepdigit n ∧ kaprekarStep^[6] n ≠ 6174 :=
  ⟨14, Finset.mem_range.mpr (by omega), by decide, by decide⟩

end KaprekarConstantOQ01ZeroAxiom
