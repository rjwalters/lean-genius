/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e8c7f151-cf4a-4257-9ee1-cc564571ebff

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 43, column 0:
  unexpected identifier; expected command

At line 70, column 0:
  unexpected identifier; expected command

At line 78, column 19:
  unexpected token 'open'; expected ']'

At line 78, column 24:
  unexpected token ','; expected 'private', 'scoped' or identifier

At line 87, column 10:
  unexpected token '('; expected ':=', 'where' or '|'
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: be886a2d-9127-4004-bf11-3814b8d91f71

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 15, column 0:
  unexpected identifier; expected command

At line 38, column 0:
  unexpected identifier; expected command

At line 42, column 19:
  unexpected token 'open'; expected ']'

At line 42, column 24:
  unexpected token ','; expected 'private', 'scoped' or identifier

At line 44, column 10:
  unexpected token '('; expected ':=', 'where' or '|'
-/

/-
Erdős Problem #312

Problem statement pending.

Reference: https://erdosproblems.com/312
-/

import Mathlib

-- Adapted from formal-conjectures
-- TODO: Enhance with proper formalization

Copyright 2025 The Formal Conjectures Authors.
/-
ERROR 1:
unexpected identifier; expected command
-/
/-
ERROR 1:
unexpected identifier; expected command
-/

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


# Erdős Problem 312

*Reference:* [erdosproblems.com/312](https://www.erdosproblems.com/312)
-/

namespace Erdos312

Does there exist a constant `c > 0` such that, for any `K > 1`, whenever `A` is a sufficiently large
/-
ERROR 1:
unexpected identifier; expected command
-/
/-
ERROR 1:
unexpected identifier; expected command
-/
finite multiset of integers with $\sum_{n \in A} 1/n > K$ there exists some $S \subseteq A$ such that
$1 - \exp(-(c*K)) < \sum_{n \in S} 1/n \le 1$?
-/
@[category research open, AMS 5 11]
/-
ERROR 1:
unexpected token 'open'; expected ']'

ERROR 2:
unexpected token ','; expected 'private', 'scoped' or identifier
-/
/-
ERROR 1:
unexpected token 'open'; expected ']'

ERROR 2:
unexpected token ','; expected 'private', 'scoped' or identifier
-/
theorem erdos_312 :
    answer(sorry) ↔
    /-
    ERROR 1:
    unexpected token '('; expected ':=', 'where' or '|'
    -/
    /-
    ERROR 1:
    unexpected token '('; expected ':=', 'where' or '|'
    -/
    ∃ (c : ℝ), 0 < c ∧
      ∀ (K : ℝ), 1 < K →
        ∃ (N₀ : ℕ),
          ∀ (n : ℕ) (a : Fin n → ℕ),
            (n ≥ N₀ ∧ (∑ i : Fin n, (a i : ℝ)⁻¹) > K) →
              ∃ (S : Finset (Fin n)),
                1 - Real.exp (-(c * K)) < (∑ i ∈ S, (a i : ℝ)⁻¹) ∧
                ∑ i ∈ S, (a i : ℝ)⁻¹ ≤ 1 := by
  sorry

end Erdos312

-- Placeholder for main result
theorem erdos_312_placeholder : True := trivial
