/-
# Cantor's Theorem OQ-05: there is no greatest cardinal, and an explicit power tower

## Open Question
Turn Cantor's theorem `a < 2 ^ a` into its global structural consequence: the cardinals
have *no maximum*, and from any cardinal `a` there is an explicit strictly increasing
ℕ-indexed tower `a < 2^a < 2^(2^a) < ⋯` of distinct cardinals above it.

## Approach
Where the base entry and OQ-03 build the *diagonal constructions* that prove `a < 2 ^ a`
(Cantor / König / Lawvere), this entry takes that inequality as given (`Cardinal.cantor`)
and reads off the shape of the cardinal order:
  * `∃ b, a < b` — every cardinal is exceeded (take `b = 2 ^ a`).
  * `¬ IsMax a` — no cardinal is a maximum.
  * The iterated powerset `powTower a n = (2 ^ ·)^[n] a` is **strictly monotone** in `n`,
    hence injective: infinitely many distinct cardinals lie above any `a`.

A subtle point: the map `c ↦ 2 ^ c` is *not* provably strictly monotone on cardinals
(whether `a < b → 2^a < 2^b` is independent of ZFC — the GCH question). So the tower's
monotonicity cannot come from monotonicity of exponentiation; it comes from applying
`Cardinal.cantor` afresh at *each* level, `powTower a n < 2 ^ (powTower a n) = powTower a (n+1)`,
which is exactly what `strictMono_nat_of_lt_succ` needs.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CantorsTheoremOQ05

open Cardinal

/-- **Cantor's inequality `a < 2 ^ a`** (`Cardinal.cantor`), re-exported as the engine. The
powerset of any type is strictly larger than the type. -/
theorem cantor_lt (a : Cardinal.{u}) : a < 2 ^ a :=
  Cardinal.cantor a

/-- **Every cardinal is exceeded: `∃ b, a < b`.** Witness `b = 2 ^ a`. -/
theorem exists_gt (a : Cardinal.{u}) : ∃ b, a < b :=
  ⟨2 ^ a, cantor_lt a⟩

/-- **There is no greatest cardinal: `¬ IsMax a`.** If `a` were maximal then `2 ^ a ≤ a`
(maximality applied to `a ≤ 2 ^ a`), contradicting `a < 2 ^ a`. -/
theorem not_isMax (a : Cardinal.{u}) : ¬ IsMax a := by
  intro h
  exact absurd (h (cantor_lt a).le) (cantor_lt a).not_ge

/-- **The iterated-powerset tower** above `a`: `powTower a n = (2 ^ ·)^[n] a`, i.e.
`a, 2^a, 2^(2^a), …`. -/
def powTower (a : Cardinal.{u}) (n : ℕ) : Cardinal.{u} :=
  (fun c => (2 : Cardinal.{u}) ^ c)^[n] a

@[simp] theorem powTower_zero (a : Cardinal.{u}) : powTower a 0 = a := rfl

/-- Each rung is the powerset of the previous one: `powTower a (n+1) = 2 ^ powTower a n`. -/
theorem powTower_succ (a : Cardinal.{u}) (n : ℕ) :
    powTower a (n + 1) = 2 ^ powTower a n :=
  Function.iterate_succ_apply' _ _ _

/-- **The tower is strictly increasing.** Crucially this does *not* use monotonicity of
`c ↦ 2 ^ c` (which is independent of ZFC); each step is a fresh application of
`Cardinal.cantor` to the current rung. -/
theorem powTower_strictMono (a : Cardinal.{u}) : StrictMono (powTower a) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [powTower_succ]; exact cantor_lt (powTower a n)

/-- **The rungs are all distinct.** Strict monotonicity gives injectivity, so the tower
exhibits infinitely many pairwise-different cardinals — and all of them exceed `a` (for
`n ≥ 1`). -/
theorem powTower_injective (a : Cardinal.{u}) : Function.Injective (powTower a) :=
  (powTower_strictMono a).injective

/-- **Every rung past the base exceeds `a`: `a < powTower a (n+1)`.** Concretely the tower
escapes `a` immediately and never returns. -/
theorem lt_powTower_succ (a : Cardinal.{u}) (n : ℕ) : a < powTower a (n + 1) := by
  simpa using (powTower_strictMono a) (Nat.succ_pos n)

end CantorsTheoremOQ05
