/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0fcaaee3-d231-46e3-a7b5-8ae2b066f02e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 15, column 0:
  unexpected identifier; expected command

At line 38, column 0:
  unexpected identifier; expected command

At line 41, column 19:
  unexpected token 'open'; expected ']'

At line 41, column 24:
  unexpected token ','; expected 'private', 'scoped' or identifier

At line 42, column 32:
  Invalid field `HasDensity`: The environment does not contain `Function.HasDensity`
  {n | ?m.5 ≤ ?m.7}
has type
  ?m.2 → Prop

At line 42, column 37:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n

At line 42, column 50:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (n + 1)

At line 45, column 0:
  unexpected identifier; expected command

At line 48, column 19:
  unexpected token 'open'; expected ']'

At line 48, column 24:
  unexpected token ','; expected 'private', 'scoped' or identifier

At line 49, column 32:
  Invalid field `HasDensity`: The environment does not contain `Function.HasDensity`
  {n | ?m.5 ≤ ?m.7}
has type
  ?m.2 → Prop

At line 49, column 37:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (n + 1)

At line 49, column 56:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n

At line 52, column 0:
  unexpected identifier; expected command

At line 56, column 19:
  unexpected token 'open'; expected ']'

At line 56, column 24:
  unexpected token ','; expected 'private', 'scoped' or identifier

At line 57, column 59:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n

At line 57, column 72:
  Function expected at
  primeGap
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (n + 1)
-/

/-
Erdős Problem #218

Problem statement pending.

Reference: https://erdosproblems.com/218
-/

import Mathlib

-- Adapted from formal-conjectures
-- TODO: Enhance with proper formalization

Copyright 2025 The Formal Conjectures Authors.
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


# Erdős Problem 218

*Reference:* [erdosproblems.com/218](https://www.erdosproblems.com/218)
-/

namespace Erdos218

The set of indices $n$ for which a prime gap is followed by a larger or equal prime gap has a
/-
ERROR 1:
unexpected identifier; expected command
-/
natural density of $\frac 1 2$.
-/
@[category research open, AMS 11]
/-
ERROR 1:
unexpected token 'open'; expected ']'

ERROR 2:
unexpected token ','; expected 'private', 'scoped' or identifier
-/
theorem erdos_218.variants.le : {n | primeGap n ≤ primeGap (n + 1)}.HasDensity <| 1 / 2 := by
  /-
  ERROR 1:
  Invalid field `HasDensity`: The environment does not contain `Function.HasDensity`
    {n | ?m.5 ≤ ?m.7}
  has type
    ?m.2 → Prop

  ERROR 2:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    n

  ERROR 3:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    (n + 1)
  -/
  sorry

The set of indices $n$ for which a prime gap is preceeded by a larger or equal prime gap has a
/-
ERROR 1:
unexpected identifier; expected command
-/
natural density of $\frac 1 2$.
-/
@[category research open, AMS 11]
/-
ERROR 1:
unexpected token 'open'; expected ']'

ERROR 2:
unexpected token ','; expected 'private', 'scoped' or identifier
-/
theorem erdos_218.variants.ge : {n | primeGap (n + 1) ≤ primeGap n}.HasDensity <| 1 / 2 := by
  /-
  ERROR 1:
  Invalid field `HasDensity`: The environment does not contain `Function.HasDensity`
    {n | ?m.5 ≤ ?m.7}
  has type
    ?m.2 → Prop

  ERROR 2:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    (n + 1)

  ERROR 3:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    n
  -/
  sorry

There are infintely many indices $n$ such that the prime gap at $n$ is equal to the prime gap
/-
ERROR 1:
unexpected identifier; expected command
-/
at $n+1$. This is equivalent to the existence of infinitely many arithmetic progressions of
length $3$, see `erdos_141.variant.infinite_three`.
-/
@[category research open, AMS 11]
/-
ERROR 1:
unexpected token 'open'; expected ']'

ERROR 2:
unexpected token ','; expected 'private', 'scoped' or identifier
-/
theorem erdos_218.variants.infinite_equal_prime_gap : {n | primeGap n = primeGap (n + 1)}.Infinite := by
  /-
  ERROR 1:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    n

  ERROR 2:
  Function expected at
    primeGap
  but this term has type
    ?m.1

  Note: Expected a function because this term is being applied to the argument
    (n + 1)
  -/
  sorry

end Erdos218

-- Placeholder for main result
theorem erdos_218_placeholder : True := trivial
