/-
# Markov Equation — Vieta Ascent Generates Infinitely Many Solutions (OQ-06)

The parent development (`Proofs.MarkovEquation`) runs the Markov tree **downward**:
every positive Markov triple descends, by Vieta-jumping the *largest* coordinate,
back to the root `(1,1,1)` (`markov_classification`). The descent strictly
*decreases* the coordinate sum (`markov_vieta_lt`).

This file runs the tree the other way — **upward** — and draws the structural
consequence the descent theorem does not give: there are **infinitely many**
Markov triples.

The engine is the *ascent* move. Given a sorted triple `a ≤ b ≤ c`, Vieta-jump the
**smallest** coordinate `a ↦ 3bc − a`. The parent's third-coordinate jump,
conjugated by transpositions, shows the result `(b, c, 3bc − a)` is again a Markov
triple; and because `a ≤ c` while `b ≥ 1`, the new top coordinate satisfies

  `3bc − a ≥ 3bc − c = c(3b − 1) ≥ 2c > c`,

so the ascent **strictly increases** the maximal coordinate. Iterating from the
root produces the strictly growing sequence

  `(1,1,1) → (1,1,2) → (1,2,5) → (2,5,29) → ⋯`

of pairwise-distinct Markov triples. Injectivity of this sequence (its top
coordinate is strictly monotone) forces the solution set to be infinite.

We prove, all axiom-free and over `ℤ`:

* `markov_vieta_fst`   — Vieta-jumping the *first* coordinate preserves Markov;
* `markov_ascent_isMarkov` — the sorted ascent move `(a,b,c) ↦ (b,c,3bc−a)` lands
                          in the solution set;
* `ascent_spec`        — one ascent step keeps a sorted triple sorted and strictly
                          increases the top coordinate;
* `seq`                — the canonical ascent sequence rooted at `(1,1,1)`;
* `seq_zero … seq_three` — it reproduces the classical head `(1,1,1),(1,1,2),
                          (1,2,5),(2,5,29)`;
* `seq_top_strictMono` — its top coordinate is strictly monotone, hence `seq` is
                          injective (`seq_injective`);
* `markov_infinite`    — **the Markov solution set is infinite.**

Mathlib has no Markov-equation development, so none of this is available there;
it builds directly on the parent file.
-/
import Mathlib
import Proofs.MarkovEquation

namespace MarkovEquationOQ06

open MarkovEquation

/-! ## The ascent move

Vieta-jumping the *first* coordinate is the parent's third-coordinate jump
`markov_vieta` conjugated by the two transpositions `markov_swap12`,
`markov_swap23`. -/

/-- **Vieta jump on the first coordinate.** Replacing `x` by its conjugate root
`3yz − x` sends a Markov triple to a Markov triple. -/
theorem markov_vieta_fst {x y z : ℤ} (h : IsMarkov x y z) :
    IsMarkov (3 * y * z - x) y z :=
  markov_swap12 (markov_swap23 (markov_vieta (markov_swap23 (markov_swap12 h))))

/-- **The sorted ascent move lands in the solution set.** From a triple `(a,b,c)`
the move `(a,b,c) ↦ (b, c, 3bc − a)` (Vieta-jump the first coordinate, then keep
the natural sorted order) again yields a Markov triple. -/
theorem markov_ascent_isMarkov {a b c : ℤ} (h : IsMarkov a b c) :
    IsMarkov b c (3 * b * c - a) :=
  markov_vieta (markov_swap23 (markov_swap12 h))

/-- **One ascent step.** Applied to a *sorted* Markov triple `1 ≤ a ≤ b ≤ c`, the
ascent move returns a sorted Markov triple `b ≤ c ≤ 3bc − a` whose top coordinate
is *strictly larger* than the previous top: `c < 3bc − a`. -/
theorem ascent_spec {a b c : ℤ} (hM : IsMarkov a b c) (h1 : 1 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    IsMarkov b c (3 * b * c - a) ∧ 1 ≤ b ∧ b ≤ c ∧
      c ≤ 3 * b * c - a ∧ c < 3 * b * c - a := by
  have hac : a ≤ c := le_trans hab hbc
  have hc1 : (1 : ℤ) ≤ c := le_trans h1 hac
  -- `c·(3b − 2) = 3bc − 2c > 0`, the arithmetic core of the strict growth.
  have hprod : (0 : ℤ) < c * (3 * b - 2) := mul_pos (by linarith) (by linarith)
  refine ⟨markov_ascent_isMarkov hM, le_trans h1 hab, hbc, ?_, ?_⟩
  · nlinarith [hprod, hac]
  · nlinarith [hprod, hac]

/-! ## The canonical ascent sequence -/

/-- The ascent map on raw triples: `(a,b,c) ↦ (b, c, 3bc − a)`. -/
def ascent (p : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (p.2.1, p.2.2, 3 * p.2.1 * p.2.2 - p.1)

/-- The canonical ascent sequence of Markov triples rooted at `(1,1,1)`. -/
def seq : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 1, 1)
  | (n + 1) => ascent (seq n)

theorem seq_zero : seq 0 = (1, 1, 1) := rfl
theorem seq_one : seq 1 = (1, 1, 2) := by decide
theorem seq_two : seq 2 = (1, 2, 5) := by decide
theorem seq_three : seq 3 = (2, 5, 29) := by decide

/-- **Invariant.** Every term of the ascent sequence is a sorted Markov triple
`1 ≤ a ≤ b ≤ c`. -/
theorem seq_spec (n : ℕ) :
    IsMarkov (seq n).1 (seq n).2.1 (seq n).2.2 ∧
      1 ≤ (seq n).1 ∧ (seq n).1 ≤ (seq n).2.1 ∧ (seq n).2.1 ≤ (seq n).2.2 := by
  induction n with
  | zero => exact ⟨markov_one, le_refl _, le_refl _, le_refl _⟩
  | succ n ih =>
    obtain ⟨hM, h1, hab, hbc⟩ := ih
    obtain ⟨hM', hb1, hbc', hc', _⟩ := ascent_spec hM h1 hab hbc
    simp only [seq, ascent]
    exact ⟨hM', hb1, hbc', hc'⟩

/-- Every term of the sequence is a Markov triple. -/
theorem seq_mem_markov (n : ℕ) :
    IsMarkov (seq n).1 (seq n).2.1 (seq n).2.2 := (seq_spec n).1

/-- **Strict growth.** The top coordinate of the ascent sequence is strictly
monotone. -/
theorem seq_top_strictMono : StrictMono (fun n => (seq n).2.2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨hM, h1, hab, hbc⟩ := seq_spec n
  obtain ⟨_, _, _, _, hlt⟩ := ascent_spec hM h1 hab hbc
  simpa [seq, ascent] using hlt

/-- The ascent sequence is injective: distinct indices give distinct triples,
since their top coordinates already differ. -/
theorem seq_injective : Function.Injective seq := by
  intro n m h
  exact seq_top_strictMono.injective (by rw [h])

/-! ## Infinitude of the Markov solution set -/

/-- **Infinitely many Markov triples.** The Vieta ascent generates a strictly
increasing sequence of pairwise-distinct Markov triples, so the solution set of
the Markov equation `x² + y² + z² = 3xyz` over the positive integers is infinite.

This is the structural counterpart to the parent's descent theorem
(`MarkovEquation.markov_classification`): descent shows *every* triple reaches the
root; ascent shows the tree never terminates upward. -/
theorem markov_infinite :
    {p : ℤ × ℤ × ℤ | IsMarkov p.1 p.2.1 p.2.2}.Infinite :=
  Set.infinite_of_injective_forall_mem seq_injective (fun n => seq_mem_markov n)

end MarkovEquationOQ06
