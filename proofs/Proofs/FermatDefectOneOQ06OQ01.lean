/-
  Fermat Defect-One — OQ-06-OQ-01: the even-exponent obstruction to the sign-flip map

  Parent (`Proofs.FermatDefectOneOQ06`, "The Sign-Flip Involution of the
  Defect-One Conjecture"): for every **odd** exponent `n` the involution
  `Ψ(a, b, c) = (c, -b, a)` negates the defect `a^n + b^n - c^n` and hence
  exchanges the two defect signs (`signFlip_negates_defect_odd`).  The parent
  observed that at **even** `n` this same `Ψ` fails to negate the defect —
  because `(-b)^n = +b^n`, `Ψ` sends `a^n + b^n - c^n` to `c^n + b^n - a^n`,
  an `a ↔ c` **swap** rather than a sign flip.

  OQ-06-OQ-01 asks: at even `n`, is there some *other* structural map exchanging
  the two defect signs, or is the absence of a sign-flip map a genuine even/odd
  asymmetry?

  ## Answer: a genuine even/odd asymmetry (for the natural class of maps)

  We work with the coordinate vector `v : Fin 3 → ℤ` and the defect form
  `defect n v = v 0 ^ n + v 1 ^ n - v 2 ^ n`.  The parent's `Ψ` belongs to the
  natural class of **signed coordinate permutations**

      (signedPerm σ s) v = fun i => s i * v (σ i),   σ ∈ S₃,  s i ∈ {±1},

  the maps that permute the three coordinates and independently flip their signs.
  (`Ψ(a,b,c) = (c,-b,a)` is `signedPerm (swap 0 2) ![1,-1,1]`.)  A map *negates
  the defect* when `defect n (φ v) = -defect n v` for all `v`.

  * **Odd `n` — a sign-flip map exists.**  The `Ψ`-analogue
    `signedPerm (Equiv.swap 0 2) ![1,-1,1]` negates the defect for every odd `n`
    (`signFlipFin_negates_odd`), recovering the parent involution in this
    framework.

  * **Even `n` — NO signed permutation negates the defect** (`no_signFlip_even`).
    The reason is *sign-blindness*: at even `n`, `(s i)^n = 1` for every sign
    `s i = ±1`, so the action of a signed permutation on the defect factors
    through the pure coordinate permutation `σ` — the signs `s` become invisible.
    A pure permutation only shuffles the three summands `v 0 ^ n, v 1 ^ n,
    v 2 ^ n`, so it fixes the value of the defect at the symmetric point
    `v = (1,1,1)`, where `defect = 1 + 1 - 1 = 1 > 0`.  A sign flip would need
    that value to become `-1`.  Since `1 ≠ -1`, no signed permutation can negate
    the even-exponent defect.  Evaluating at `(1,1,1)` makes this a one-line
    contradiction.

  Packaged as `even_odd_asymmetry`: for odd `n` a sign-flip map exists, for even
  `n ≥ 2` none does.  So the parent's `Ψ` has no even-exponent analogue within
  the class it belongs to — the absence is genuine, not an artefact of the
  particular map `Ψ`.

  ## Scope (honest statement)

  This resolves the question for the class of signed coordinate permutations —
  precisely the structural maps `Ψ` is drawn from.  The obstruction is the
  sign-blindness of even powers; it does not, by itself, rule out exotic
  non-linear or non-coordinate maps, which the parent OQ did not consider either.

  Everything is a polynomial identity / finite sign computation over `ℤ`, closed
  by `ring`, `simp`, `Even.neg_one_pow`, and `Odd.neg_pow`.  No `axiom`, no
  `sorry`, no `native_decide`: a fully verified, 0-axiom result.
-/

import Mathlib
import Proofs.FermatDefectOne
import Proofs.FermatDefectOneOQ06

namespace FermatDefectOneOQ06OQ01

open scoped BigOperators

/-! ## The defect form and the class of signed coordinate permutations -/

/-- The **defect form** at exponent `n` on a coordinate vector `v : Fin 3 → ℤ`,
with the canonical sign pattern `(+, +, -)`: `defect n v = v 0 ^ n + v 1 ^ n - v 2 ^ n`.
Matches the parent's `a^n + b^n - c^n` under `(a,b,c) ↦ ![a,b,c]`. -/
def defect (n : ℕ) (v : Fin 3 → ℤ) : ℤ := v 0 ^ n + v 1 ^ n - v 2 ^ n

/-- A **signed coordinate permutation**: permute the coordinates by `σ ∈ S₃`
and multiply coordinate `i` by the sign `s i`.  This is the natural class of
structural maps the parent's involution `Ψ(a,b,c) = (c,-b,a)` belongs to. -/
def signedPerm (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ) (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => s i * v (σ i)

/-- `s` is a **sign vector**: each entry is `±1`. -/
def IsSign (s : Fin 3 → ℤ) : Prop := ∀ i, s i = 1 ∨ s i = -1

/-- A map `φ` **negates the defect** at exponent `n` when `defect n (φ v) = -defect n v`
for every `v`.  This is exactly the sign-flip property OQ-06 asks about. -/
def NegatesDefect (n : ℕ) (φ : (Fin 3 → ℤ) → (Fin 3 → ℤ)) : Prop :=
  ∀ v, defect n (φ v) = -defect n v

/-! ## Sign-blindness of even powers -/

/-- A `±1` sign raised to an **even** power is `1`.  This is the source of the
even-exponent obstruction: even powers erase the sign. -/
theorem sign_even_pow {x : ℤ} (hx : x = 1 ∨ x = -1) {n : ℕ} (hn : Even n) : x ^ n = 1 := by
  rcases hx with h | h
  · simp [h]
  · simp [h, hn.neg_one_pow]

/-! ## Even `n`: no signed permutation negates the defect -/

/-- **Main obstruction.** For every **even** exponent `n`, no signed coordinate
permutation negates the defect form.

The proof is one evaluation: at the symmetric point `v = (1,1,1)` a signed
permutation `φ` outputs the sign vector `s` itself (`φ 1 = s`), and since `n`
is even every `(s i)^n = 1`, so `defect n (φ 1) = 1 + 1 - 1 = 1`.  But negation
demands `defect n (φ 1) = -defect n 1 = -1`.  As `1 ≠ -1`, no such `φ` exists. -/
theorem no_signFlip_even {n : ℕ} (hn : Even n) (σ : Equiv.Perm (Fin 3))
    {s : Fin 3 → ℤ} (hs : IsSign s) : ¬ NegatesDefect n (signedPerm σ s) := by
  intro h
  have key := h (fun _ => 1)
  -- At the all-ones vector, `(signedPerm σ s) 1 i = s i`, and `(s i)^n = 1`.
  have e0 : s 0 ^ n = 1 := sign_even_pow (hs 0) hn
  have e1 : s 1 ^ n = 1 := sign_even_pow (hs 1) hn
  have e2 : s 2 ^ n = 1 := sign_even_pow (hs 2) hn
  simp only [defect, signedPerm, mul_one] at key
  rw [e0, e1, e2] at key
  norm_num at key

/-! ## Odd `n`: the parent involution `Ψ` survives as a signed permutation -/

/-- The `Fin 3` incarnation of the parent's sign-flip involution
`Ψ(a,b,c) = (c,-b,a)`: permute by the swap `0 ↔ 2` and negate the middle
coordinate.  As a signed permutation this is `signedPerm (Equiv.swap 0 2) ![1,-1,1]`. -/
def signFlipFin : (Fin 3 → ℤ) → (Fin 3 → ℤ) := signedPerm (Equiv.swap 0 2) ![1, -1, 1]

/-- `![1,-1,1]` is a sign vector. -/
theorem isSign_signFlipFin : IsSign (![1, -1, 1] : Fin 3 → ℤ) := by
  intro i; fin_cases i <;> simp

/-- Explicit coordinates of `signFlipFin v = (v 2, -v 1, v 0)`, matching
`Ψ(a,b,c) = (c,-b,a)`. -/
theorem signFlipFin_apply (v : Fin 3 → ℤ) :
    signFlipFin v 0 = v 2 ∧ signFlipFin v 1 = -v 1 ∧ signFlipFin v 2 = v 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [signFlipFin, signedPerm]
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right,
        show (Equiv.swap (0 : Fin 3) 2) 1 = 1 from by decide]

/-- **Odd `n` admits a sign-flip map.** For every **odd** exponent `n`, the
`Ψ`-analogue `signFlipFin` negates the defect, exactly as the parent's
`signFlip_negates_defect_odd` does on triples. -/
theorem signFlipFin_negates_odd {n : ℕ} (hn : Odd n) : NegatesDefect n signFlipFin := by
  intro v
  obtain ⟨h0, h1, h2⟩ := signFlipFin_apply v
  simp only [defect, h0, h1, h2, hn.neg_pow]
  ring

/-! ## The even/odd asymmetry, packaged -/

/-- **Even/odd asymmetry (OQ-06-OQ-01).**  Within the class of signed coordinate
permutations — precisely the structural maps the parent's `Ψ` belongs to — a
defect-sign-flip map exists at every **odd** exponent but at **no even** exponent:

* (odd) there is an explicit signed permutation `signFlipFin` negating the defect;
* (even) *no* signed permutation `signedPerm σ s` negates the defect.

So the parent's involution `Ψ` has no even-exponent analogue in its own class:
the absence is a genuine even/odd asymmetry, forced by the sign-blindness of
even powers, not an artefact of the particular map `Ψ`. -/
theorem even_odd_asymmetry :
    (∀ {n : ℕ}, Odd n → NegatesDefect n signFlipFin) ∧
    (∀ {n : ℕ}, Even n → ∀ (σ : Equiv.Perm (Fin 3)) {s : Fin 3 → ℤ},
      IsSign s → ¬ NegatesDefect n (signedPerm σ s)) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact signFlipFin_negates_odd hn
  · intro n hn σ s hs
    exact no_signFlip_even hn σ hs

/-! ## Bridge to the parent `Ψ` on triples

The parent defines `Ψ` on `ℤ × ℤ × ℤ`.  Under the correspondence
`(a,b,c) ↦ ![a,b,c]`, `Ψ` is exactly `signFlipFin`, so the two frameworks agree. -/

/-- Under `(a,b,c) ↦ ![a,b,c]`, the parent's `Ψ` and the `Fin 3` map `signFlipFin`
compute the same coordinates: both send `(a,b,c)` to `(c,-b,a)`. -/
theorem signFlipFin_eq_parent (a b c : ℤ) :
    (signFlipFin ![a, b, c] 0, signFlipFin ![a, b, c] 1, signFlipFin ![a, b, c] 2)
      = FermatDefectOneOQ06.signFlip (a, b, c) := by
  obtain ⟨h0, h1, h2⟩ := signFlipFin_apply (![a, b, c])
  rw [h0, h1, h2]
  simp [FermatDefectOneOQ06.signFlip]

end FermatDefectOneOQ06OQ01
