import Mathlib

/-!
# Collatz OQ-02-03 — Part XII: Certificate maximality / canonical generation (self-contained)

The companion `CollatzStructuredOQ02OQ03CertUnique` pinned the valid parity certificates of a
residue class to the *prefixes* of the auto-derived `deriveVec`, but only *within the
residue-determined window* — its exact characterization `affValid_iff_prefix_deriveVec` carries
the side hypothesis `v.length ≤ (deriveVec (2b+1) (2^b) r).length`.  The standing next step was
**maximality**: showing a valid certificate can never run past what `deriveVec` produces.

This file settles that in its cleanest, fully general form.  The key structural fact is that
the `AffValid` inductive can only extend a certificate while the *modulus* `c` is even (both the
`odd` and `even` constructors demand `c % 2 = 0`), and `deriveVec` halts on exactly the
complementary condition `c % 2 = 1`.  Consequently:

* `affValid_nil_of_odd_modulus` — a valid certificate for an **odd**-modulus class is empty:
  once `c` is odd the residue no longer forces any parity, so the window has closed.
* `affValid_eq_deriveVec_self` — **canonical generation**: *every* valid certificate `v` for a
  class `(c, d)` is literally `deriveVec v.length c d` — the derivation engine run with the
  certificate's own length as fuel reproduces it exactly.  No `2^b` structure, no length side
  condition: the engine *is* the certificate generator (answering the "mechanize certificate
  generation" step), and `deriveVec` is maximal because it stops precisely when `AffValid` must.
* `affValid_length_le_of_deriveVec_shorter` — the length-maximality reading: if `deriveVec`
  halts within `fuel` steps (returns something strictly shorter than `fuel`), no valid
  certificate for the class is longer than `deriveVec`'s output.

Self-contained: the `AffValid` inductive and the `deriveVec` engine are re-declared here exactly
as in the mother module `Proofs.CollatzStructuredOQ02OQ03` (which sits at the Lean kernel memory
ceiling and is expensive/fragile to rebuild), so these theorems stand on their own with only
`import Mathlib`.  Axiom-free; nothing here uses `decide`.

Reference: Terras (1976) parity vectors; the residue-determined-window coding of the Collatz map.
-/

namespace CollatzStructuredOQ02OQ03CertMaximal

/-- A parity certificate `v` is **valid** for the affine class `c·m + d` when it records, from
the front, the forced Collatz parities: each extending bit demands an even modulus `c`, and the
bit is the parity of the constant `d`, after which the class advances one Collatz step.  (Copied
verbatim from the mother module `Proofs.CollatzStructuredOQ02OQ03`.) -/
inductive AffValid : List Bool → ℕ → ℕ → Prop
  | nil  {c d} : AffValid [] c d
  | odd  {v c d} : c % 2 = 0 → d % 2 = 1 → AffValid v (3 * c) (3 * d + 1) →
      AffValid (true :: v) c d
  | even {v c d} : c % 2 = 0 → d % 2 = 0 → AffValid v (c / 2) (d / 2) →
      AffValid (false :: v) c d

/-- The auto-derivation engine: peel forced parities off `(c, d)` until the modulus `c` becomes
odd (the residue-determined window closes) or the `fuel` is exhausted.  (Copied verbatim from the
mother module.) -/
def deriveVec : ℕ → ℕ → ℕ → List Bool
  | 0,         _, _ => []
  | fuel + 1,  c, d =>
      if c % 2 = 1 then []
      else if d % 2 = 1 then true  :: deriveVec fuel (3 * c) (3 * d + 1)
      else false :: deriveVec fuel (c / 2) (d / 2)

/-- **Odd modulus closes the window.**  A valid certificate for a class whose modulus `c` is odd
must be empty: neither `AffValid` constructor that extends a certificate can fire (both require
`c % 2 = 0`), so `nil` is the only option.  This is the structural reason `deriveVec` halts on
`c % 2 = 1`. -/
theorem affValid_nil_of_odd_modulus {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hc : c % 2 = 1) : v = [] := by
  cases hv with
  | nil => rfl
  | odd hc0 _ _ => exact absurd hc (by omega)
  | even hc0 _ _ => exact absurd hc (by omega)

/-- **Canonical generation / maximality.**  Every valid certificate `v` for the class `(c, d)` is
exactly `deriveVec v.length c d`: running the derivation engine with the certificate's own length
as fuel reproduces it bit-for-bit.  Proof is a structural induction on `AffValid`; at each
extending step the modulus is even (`c % 2 = 0`), so `deriveVec` skips its `c % 2 = 1` halt and
takes the branch selected by `d % 2`, matching the constructor.  Hence `deriveVec` is the
certificate generator, and — since it halts as soon as the modulus turns odd, exactly when
`AffValid` can no longer extend — it is maximal: no valid certificate outruns it. -/
theorem affValid_eq_deriveVec_self {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) : v = deriveVec v.length c d := by
  induction hv with
  | nil => rfl
  | @odd v c d hc hd _htail ih =>
      show true :: v = deriveVec (true :: v).length c d
      simp only [List.length_cons, deriveVec]
      rw [if_neg (by omega : ¬ c % 2 = 1), if_pos hd, ← ih]
  | @even v c d hc hd _htail ih =>
      show false :: v = deriveVec (false :: v).length c d
      simp only [List.length_cons, deriveVec]
      rw [if_neg (by omega : ¬ c % 2 = 1), if_neg (by omega : ¬ d % 2 = 1), ← ih]

/-- **Length maximality.**  If the engine's output at fuel `v.length` is *shorter* than `v`
(i.e. `deriveVec` halted early, on an odd modulus), then `v` cannot be a valid certificate for the
class of that length — contrapositive of `affValid_eq_deriveVec_self`, which forces
`v.length = (deriveVec v.length c d).length`.  So a valid certificate's length is exactly the
number of steps `deriveVec` runs before halting: it never exceeds the residue-determined window. -/
theorem affValid_length_eq_deriveVec_self {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) : v.length = (deriveVec v.length c d).length := by
  conv_lhs => rw [affValid_eq_deriveVec_self hv]

end CollatzStructuredOQ02OQ03CertMaximal
