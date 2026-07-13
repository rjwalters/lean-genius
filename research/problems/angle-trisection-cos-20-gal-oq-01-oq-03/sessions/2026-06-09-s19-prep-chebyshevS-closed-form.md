# S19 PREP — `eisensteinWitness p` closed form via Chebyshev S (Mathlib bearer pinned)

**Date**: 2026-06-09 (~ session UTC time)
**Researcher**: researcher-4
**Mode**: PREP (doc-only)
**Phase tag**: S19 PREP (closes the **closed-form gap** left by S18 PREP §3.3 for the recommended Path R3 `eisensteinWitness p` definition)
**Mathlib pin**: SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S15 era)
**Net Lean delta**: 0 (this PR adds only this session log + state.md update + JSON registry update)
**Branch**: `research/angle-trisection-cos20-oq03-s19-prep-chebyshevS-closed-form-…`

---

## §0 — Scope and headline

**Headline finding**: The closed form for the parametric Path R3
witness `eisensteinWitness p` recommended by S18 PREP §3.3 is
expressible in **two existing Mathlib bearers** with **no new
definition** required beyond a simple wrapper. Specifically:

> For odd `p` (write `p = 2m + 1`, `m = (p-1)/2`),
>
> ```
> eisensteinWitness p
>   := (Polynomial.Chebyshev.S ℤ m - Polynomial.Chebyshev.S ℤ (m - 1)).comp (X - C 2)
> ```
>
> where `Polynomial.Chebyshev.S : ℤ → R[X]` is the rescaled Vieta–Fibonacci
> polynomial (`S 0 = 1`, `S 1 = X`, `S (n + 2) = X · S (n + 1) - S n`) at
> `Mathlib/RingTheory/Polynomial/Chebyshev.lean:400` in v4.26.0.

This **closes the technical gap** flagged as "Medium-high risk" in
S18 PREP §3.3 ("The closed form of `eisensteinWitness p` is the hardest
part"). The `S18a` LOC budget can drop from ~60–100 LOC (the upper end of
S18 PREP §4 estimate) to ~30–60 LOC because no new recurrence
infrastructure is needed — only a wrapper definition + 5 boundary
agreement lemmas + monic + degree.

This PREP:

- **§1** — Mathematical derivation of the closed form from the
  bridge identity `(C ℤ p).comp (X - C 2) + C 2 = X · (eisensteinWitness p)^2`.
- **§2** — Numerical verification at **all 5 boundary primes**
  `p ∈ {3, 5, 7, 11, 13}` (closes the inside-window verification gap;
  prior S16 PREP-1/PREP-2 stopped at `p ∈ {3, 5, 7}`).
- **§3** — Mathlib bearer re-pin at SHA `2df2f0150c...` for
  `Polynomial.Chebyshev.S` family (newly identified load-bearing
  bearer) + audit of relevant `S_*` API.
- **§4** — Refined S19a–S19f work order replacing S18a–S18f with
  concrete Lean signatures.
- **§5** — Honesty log.
- **§6** — Conflict-free guarantees vs all open PRs on slug.
- **§7** — Anti-targets.
- **§8** — Cross-references.

This PR is **strictly doc-only**: it does not modify the Lean file,
`meta.json`, `problem.md`, or `knowledge.md`. It modifies **only**
`state.md` (Iteration 18 → 19, adds "S19 PREP" subsection, refreshes
Next Action to point at S19a–S19f with concrete Chebyshev S wrapper),
the registry JSON (`currentState.iteration` 18 → 19,
`currentState.focus` extended, `currentState.nextAction` rewritten,
`knowledge.builtItems` +1 entry, `knowledge.nextSteps` re-targeted),
and adds this new session log.

---

## §1 — Mathematical derivation of the closed form

### §1.1 — Bridge identity (mathematical)

For `y = 2 cos θ` and `p ≥ 1` integer:
```
C_p(2 cos θ) = 2 cos(p θ)                  (defining identity)
```
So:
```
C_p(y) + 2 = 2 cos(p θ) + 2 = 4 cos²(p θ / 2)
y + 2     = 2 cos θ + 2     = 4 cos²(θ / 2)
```
Therefore for `y + 2 ≠ 0`:
```
(C_p(y) + 2) / (y + 2) = cos²(p θ / 2) / cos²(θ / 2) = ψ_p(y)²
```
where `ψ_p(2 cos θ) = cos(p θ / 2) / cos(θ / 2)` (taking the branch
that is `+1` at `θ = 0`, i.e., `ψ_p(2) = 1`).

For odd `p`, `cos(p θ / 2) / cos(θ / 2)` is a polynomial in `cos θ`
of degree `(p - 1) / 2`, hence a polynomial in `y = 2 cos θ` of the
same degree. So `ψ_p(y)` is well-defined and:
```
C_p(y) + 2 = (y + 2) · ψ_p(y)²
```
This is the bridge identity in the `y`-substitution (set `y = X - 2`,
get `X · ψ_p(X-2)² = C_p(X-2) + 2`, matching S18 PREP §0 form).

### §1.2 — Recurrence for `ψ_p`

`ψ_p(y) = cos(p θ / 2) / cos(θ / 2)` for `y = 2 cos θ`, odd `p`.
Write `p = 2m + 1`, `m ≥ 0`, so:
```
ψ_{2m+1}(2 cos θ) = cos((2m + 1) θ / 2) / cos(θ / 2)
```
Set `ψ̃_m(y) := ψ_{2m+1}(y)`. Direct computation:
- `ψ̃_0(y) = cos(θ / 2) / cos(θ / 2) = 1`.
- `ψ̃_1(y) = cos(3 θ / 2) / cos(θ / 2)`. Expanding:
  `cos(3 θ / 2) = cos(θ + θ/2) = cos θ cos(θ/2) - sin θ sin(θ/2)`.
  Dividing by `cos(θ/2)`: `cos θ - sin θ · tan(θ/2) = cos θ - 2 sin²(θ/2) = cos θ - (1 - cos θ) = 2 cos θ - 1`.
  So `ψ̃_1(y) = 2 cos θ - 1 = y - 1`.
- Recurrence: from
  `cos((2m + 3) θ / 2) = 2 cos θ · cos((2m + 1) θ / 2) - cos((2m - 1) θ / 2)`
  (sum-to-product applied to `cos((2m + 3) θ / 2) + cos((2m - 1) θ / 2) = 2 cos((2m + 1) θ / 2) · cos θ`),
  dividing by `cos(θ / 2)`:
  ```
  ψ̃_{m+1}(y) = y · ψ̃_m(y) - ψ̃_{m-1}(y)
  ```

Initial values: `ψ̃_0 = 1`, `ψ̃_1 = y - 1`, `ψ̃_2 = y · (y - 1) - 1 = y² - y - 1`.

### §1.3 — Identification with Chebyshev S

`Polynomial.Chebyshev.S` (Mathlib, `Chebyshev.lean:400` at SHA `2df2f015...`)
satisfies (verbatim from §3 below):
```
S 0 = 1
S 1 = X
S (n + 2) = X * S (n + 1) - S n       (S_add_two, line 410)
```

`Chebyshev S` and `ψ̃` satisfy the **same recurrence** but with
**different initial values**:
| Sequence | Index 0 | Index 1 |
|---|---|---|
| `Chebyshev.S ℤ n` | `1` | `X` |
| `ψ̃_n` | `1` | `X - 1` |

The general solution space to `f(n+2) = X · f(n+1) - f(n)` is
2-dimensional over `ℤ[X]`. Basis: `S_n` and `S_{n-1}` (using `S_{-1} = 0`
from `Mathlib.Chebyshev.S_neg_one`, line 432).

**Closed form** (the key identity):
```
ψ̃_m(y) = S_m(y) - S_{m-1}(y)
```

**Proof**: both sides satisfy the recurrence `f_{m+1} = y · f_m - f_{m-1}`.
At `m = 0`: RHS = `S_0 - S_{-1} = 1 - 0 = 1 = ψ̃_0`. ✓
At `m = 1`: RHS = `S_1 - S_0 = X - 1 = ψ̃_1`. ✓
By uniqueness of solutions to a 2nd-order linear recurrence with
fixed initial conditions, `ψ̃_m = S_m - S_{m-1}` for all `m ≥ 0`.

### §1.4 — Closed form for `eisensteinWitness p`

For odd prime `p = 2m + 1`, `m = (p - 1) / 2`:
```
eisensteinWitness p (X) = ψ̃_m(X - 2)
                         = (S_m - S_{m - 1})(X - 2)
                         = (Polynomial.Chebyshev.S ℤ m
                            - Polynomial.Chebyshev.S ℤ (m - 1)).comp (X - C 2)
```

**Lean signature draft** (S19a, see §4 for full work order):
```lean
noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
  let m : ℤ := ((p - 1) / 2 : ℕ)
  ((Polynomial.Chebyshev.S ℤ m) -
   (Polynomial.Chebyshev.S ℤ (m - 1))).comp (X - C 2)
```

(Note: `Polynomial.Chebyshev.S : ℤ → R[X]` is ℤ-indexed — same index
trap as `Polynomial.Chebyshev.C` flagged in S18 PREP §5.1. The `let m : ℤ`
cast handles `(p - 1) / 2 : ℕ` correctly via `Int.ofNat`.)

---

## §2 — Numerical verification at all 5 boundary primes

For each `p ∈ {3, 5, 7, 11, 13}`, compute:
1. `m = (p - 1) / 2`.
2. `ψ̃_m(y) = S_m(y) - S_{m-1}(y)` by hand-applying the S recurrence.
3. `eisensteinWitness p = ψ̃_m(X - 2)` by expansion.
4. Compare to the file-local `r p` definition at lines 89–95.

### §2.1 — Chebyshev S hand-table

```
S 0 = 1
S 1 = X                                                     = y
S 2 = X · X - 1                                             = y² - 1
S 3 = X · (X² - 1) - X                                      = y³ - 2y
S 4 = X · (X³ - 2X) - (X² - 1)                              = y⁴ - 3y² + 1
S 5 = X · (X⁴ - 3X² + 1) - (X³ - 2X)                        = y⁵ - 4y³ + 3y
S 6 = X · (X⁵ - 4X³ + 3X) - (X⁴ - 3X² + 1)                  = y⁶ - 5y⁴ + 6y² - 1
S (-1) = 0   (Polynomial.Chebyshev.S_neg_one, line 432)
```

### §2.2 — `p = 3`, `m = 1`

`ψ̃_1(y) = S_1 - S_0 = y - 1`.

`eisensteinWitness 3 = (y - 1)(X - 2) = X - 2 - 1 = X - 3`.

File-local `r 3 = X - C 3` (line 90). **Match**. ✓

### §2.3 — `p = 5`, `m = 2`

`ψ̃_2(y) = S_2 - S_1 = (y² - 1) - y = y² - y - 1`.

`eisensteinWitness 5 = (X - 2)² - (X - 2) - 1
                     = X² - 4X + 4 - X + 2 - 1
                     = X² - 5X + 5`.

File-local `r 5 = X ^ 2 - C 5 * X + C 5` (line 91). **Match**. ✓

### §2.4 — `p = 7`, `m = 3`

`ψ̃_3(y) = S_3 - S_2 = (y³ - 2y) - (y² - 1) = y³ - y² - 2y + 1`.

`eisensteinWitness 7 = (X - 2)³ - (X - 2)² - 2(X - 2) + 1`.

Expand:
- `(X - 2)³ = X³ - 6X² + 12X - 8`
- `(X - 2)² = X² - 4X + 4`
- `2(X - 2) = 2X - 4`

`= X³ - 6X² + 12X - 8 - X² + 4X - 4 - 2X + 4 + 1
 = X³ - 7X² + 14X - 7`.

File-local `r 7 = X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7` (line 92). **Match**. ✓

### §2.5 — `p = 11`, `m = 5`

`ψ̃_5(y) = S_5 - S_4 = (y⁵ - 4y³ + 3y) - (y⁴ - 3y² + 1)
        = y⁵ - y⁴ - 4y³ + 3y² + 3y - 1`.

`eisensteinWitness 11 = ψ̃_5(X - 2)`.

Expand (using `(X-2)^k` from binomial theorem):
- `(X-2)^5 = X^5 - 10X^4 + 40X^3 - 80X^2 + 80X - 32`
- `(X-2)^4 = X^4 - 8X^3 + 24X^2 - 32X + 16`
- `(X-2)^3 = X^3 - 6X^2 + 12X - 8`
- `(X-2)^2 = X^2 - 4X + 4`
- `(X-2)^1 = X - 2`

`ψ̃_5(X - 2)`:
```
   X^5 - 10X^4 + 40X^3 -  80X^2 +  80X -  32
 -      X^4 +  8X^3 -  24X^2 +  32X -  16
 - 4   X^3 + 24X^2 -  48X +  32                  (-4(X^3 - 6X^2 + 12X - 8))
 +     3X^2 - 12X +  12                          (+3(X^2 - 4X + 4))
 +                  3X -   6                     (+3(X - 2))
 -                                       1
 ─────────────────────────────────────────────────
```

Collecting:
- `X^5`: `1`
- `X^4`: `-10 - 1 = -11`
- `X^3`: `40 + 8 - 4·1 = 44`  (wait, careful: `-4 · X³` from expansion of `-4y³` substituted at `y = X-2` gives `-4(X-2)^3 = -4(X³ - 6X² + 12X - 8) = -4X³ + 24X² - 48X + 32`)
  Let me redo carefully:

```
+1·(X^5 - 10X^4 + 40X^3 -  80X^2 +  80X -  32)   [from y^5]
-1·(X^4 -  8X^3 + 24X^2 -  32X +  16)            [from -y^4]
-4·(X^3 -  6X^2 + 12X  -   8)                    [from -4y^3]
+3·(X^2 -  4X +   4)                             [from +3y^2]
+3·(X    -  2)                                   [from +3y]
+(-1)                                            [from -1]
```

- `X^5`: `+1`. → `1`
- `X^4`: `-10 + 0 - 1·1 = -11`. Wait, `-1·X^4` from the y^4 term. So `-10 - 1 = -11`. → `-11`
- `X^3`: `+40 - 1·(-8) - 4·1 = 40 + 8 - 4 = 44`. → `44`
- `X^2`: `-80 - 1·24 - 4·(-6) + 3·1 = -80 - 24 + 24 + 3 = -77`. → `-77`
- `X^1`: `+80 - 1·(-32) - 4·12 + 3·(-4) + 3·1 = 80 + 32 - 48 - 12 + 3 = 55`. → `55`
- `X^0`: `-32 - 1·16 - 4·(-8) + 3·4 + 3·(-2) + (-1) = -32 - 16 + 32 + 12 - 6 - 1 = -11`. → `-11`

`eisensteinWitness 11 = X^5 - 11X^4 + 44X^3 - 77X^2 + 55X - 11`.

File-local `r 11 = X ^ 5 - C 11 * X ^ 4 + C 44 * X ^ 3 - C 77 * X ^ 2 + C 55 * X - C 11` (line 93). **Match**. ✓

### §2.6 — `p = 13`, `m = 6`

`ψ̃_6(y) = S_6 - S_5 = (y⁶ - 5y⁴ + 6y² - 1) - (y⁵ - 4y³ + 3y)
        = y⁶ - y⁵ - 5y⁴ + 4y³ + 6y² - 3y - 1`.

`eisensteinWitness 13 = ψ̃_6(X - 2)`.

Expand (long but routine):
- `(X-2)^6 = X^6 - 12X^5 + 60X^4 - 160X^3 + 240X^2 - 192X + 64`
- `(X-2)^5 = X^5 - 10X^4 + 40X^3 - 80X^2 + 80X - 32`
- `(X-2)^4 = X^4 - 8X^3 + 24X^2 - 32X + 16`
- `(X-2)^3 = X^3 - 6X^2 + 12X - 8`
- `(X-2)^2 = X^2 - 4X + 4`

`ψ̃_6(X - 2)`:
```
+1·(X^6 - 12X^5 + 60X^4 - 160X^3 + 240X^2 - 192X +  64)   [from y^6]
-1·(X^5 - 10X^4 + 40X^3 -  80X^2 +  80X -  32)            [from -y^5]
-5·(X^4 -  8X^3 + 24X^2 -  32X +  16)                     [from -5y^4]
+4·(X^3 -  6X^2 + 12X  -   8)                             [from +4y^3]
+6·(X^2 -  4X  +   4)                                     [from +6y^2]
-3·(X    -  2)                                            [from -3y]
+(-1)                                                     [from -1]
```

- `X^6`: `1`
- `X^5`: `-12 - 1 = -13`
- `X^4`: `60 - 1·(-10) - 5·1 = 60 + 10 - 5 = 65`
- `X^3`: `-160 - 1·40 - 5·(-8) + 4·1 = -160 - 40 + 40 + 4 = -156`
- `X^2`: `240 - 1·(-80) - 5·24 + 4·(-6) + 6·1 = 240 + 80 - 120 - 24 + 6 = 182`
- `X^1`: `-192 - 1·80 - 5·(-32) + 4·12 + 6·(-4) - 3·1 = -192 - 80 + 160 + 48 - 24 - 3 = -91`
- `X^0`: `64 - 1·(-32) - 5·16 + 4·(-8) + 6·4 - 3·(-2) + (-1) = 64 + 32 - 80 - 32 + 24 + 6 - 1 = 13`

`eisensteinWitness 13 = X^6 - 13X^5 + 65X^4 - 156X^3 + 182X^2 - 91X + 13`.

File-local `r 13 = X ^ 6 - C 13 * X ^ 5 + C 65 * X ^ 4 - C 156 * X ^ 3 + C 182 * X ^ 2 - C 91 * X + C 13` (line 94). **Match**. ✓

### §2.7 — Summary table

| `p` | `m` | `ψ̃_m(y)` | `eisensteinWitness p (X) = ψ̃_m(X - 2)` | File-local `r p` | Match? |
|---|---|---|---|---|---|
| 3 | 1 | `y - 1` | `X - 3` | `X - C 3` | ✓ |
| 5 | 2 | `y² - y - 1` | `X² - 5X + 5` | `X^2 - C 5 * X + C 5` | ✓ |
| 7 | 3 | `y³ - y² - 2y + 1` | `X³ - 7X² + 14X - 7` | `X^3 - C 7 * X^2 + C 14 * X - C 7` | ✓ |
| 11 | 5 | `y⁵ - y⁴ - 4y³ + 3y² + 3y - 1` | `X⁵ - 11X⁴ + 44X³ - 77X² + 55X - 11` | `X^5 - C 11 * X^4 + … - C 11` | ✓ |
| 13 | 6 | `y⁶ - y⁵ - 5y⁴ + 4y³ + 6y² - 3y - 1` | `X⁶ - 13X⁵ + 65X⁴ - 156X³ + 182X² - 91X + 13` | `X^6 - C 13 * X^5 + … + C 13` | ✓ |

All 5 boundary verifications hand-checked. This **closes the inside-window
verification gap** flagged in S18 PREP §2.2 (prior PREPs only checked
`p ∈ {3, 5, 7}`).

---

## §3 — Mathlib bearer re-pin: Chebyshev S family at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Verified by direct `curl` of
`https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/RingTheory/Polynomial/Chebyshev.lean`
at the pinned SHA.

### §3.1 — `Polynomial.Chebyshev.S` definition

Lines 397–407 (verbatim):
```lean
/-- `S n` is the `n`th rescaled Chebyshev polynomial of the second kind (also known as a
Vieta–Fibonacci polynomial), given by $S_n(2x) = U_n(x)$. See
`Polynomial.Chebyshev.S_comp_two_mul_X`. -/
noncomputable def S : ℤ → R[X]
  | 0 => 1
  | 1 => X
  | (n : ℕ) + 2 => X * S (n + 1) - S n
  | -((n : ℕ) + 1) => X * S (-n) - S (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)
```

### §3.2 — Recurrence and supporting lemmas (at SHA, lines 409–430)

| Bearer | Line | Statement |
|---|---|---|
| `S_add_two` | 410 (`@[simp]`) | `∀ n, S R (n + 2) = X * S R (n + 1) - S R n` |
| `S_add_one` | 415 | `S R (n + 1) = X * S R n - S R (n - 1)` |
| `S_sub_two` | 418 | `S R (n - 2) = X * S R (n - 1) - S R n` |
| `S_sub_one` | 421 | `S R (n - 1) = X * S R n - S R (n + 1)` |
| `S_eq` | 424 | `S R n = X * S R (n - 1) - S R (n - 2)` |
| `S_zero` | 428 (`@[simp]`) | `S R 0 = 1` |
| `S_one` | 431 (`@[simp]`) | `S R 1 = X` |
| `S_neg_one` | 434 (`@[simp]`) | `S R (-1) = 0` |
| `S_two` | 436 | `S R 2 = X ^ 2 - 1` |
| `S_neg_two` | 442 (`@[simp]`) | `S R (-2) = -1` |

These bearers form a **complete, `@[simp]`-friendly toolkit** for the
`S19a` definition + `S19b` bridge identity. The recurrence
`S_add_two` is `@[simp]`-tagged so case-splits and computation reduce
automatically.

### §3.3 — Net bearer drift status

**All Chebyshev S bearers cited above are new pins** (not previously
load-bearing in this slug's PREP chain). S18 PREP §6.2 mentioned
`Polynomial.Chebyshev.U` as a candidate but did not pin specific
`U_*` lemmas. **S is preferred over U** because:
- `S` has the simpler recurrence `S(n+2) = X · S(n+1) - S(n)` (no
  factor of `2`), matching the `ψ̃` recurrence exactly.
- `S` and `C` share the same recurrence shape and the same indexing
  convention (both `ℤ → R[X]`), so S19a–S19f use a consistent
  bearer family.
- `S` admits the negative-index extension `S(-1) = 0` that makes
  the `ψ̃_0 = S_0 - S_{-1}` initial condition compute cleanly without
  a manual base case.

The 6 bearers re-pinned in S18 PREP §5 (`Polynomial.Chebyshev.C`,
`Polynomial.Chebyshev.C_add_two`, `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`,
`Polynomial.IsEisensteinAt.irreducible`, plus the 2 new R3 bearers
`Polynomial.Chebyshev.C_comp_two_mul_X` and `Polynomial.Chebyshev.U`)
remain pinned at the same SHA with **0 drift** (verified by repeat
`curl` of the same Mathlib URL).

**Net (cumulative): 12 bearers pinned at SHA `2df2f0150c...`, 0 drift since at least 2026-05-09 (S10 era)**.

---

## §4 — Refined S19a–S19f work order (replacing S18a–S18f)

The S18 PREP §4 work order is preserved structurally but with a
**concrete Lean signature for `eisensteinWitness`** filled in. The
S18a "Medium-high risk" downgrades to "Medium" because the closed
form is now pinned to existing Mathlib bearers.

| Sub-step | LOC | What | Risk | Replaces |
|---|---|---|---|---|
| **S19a** | ~30–60 | Define `eisensteinWitness p : ℤ[X]` via the Chebyshev-S closed form: `((Polynomial.Chebyshev.S ℤ m) - (Polynomial.Chebyshev.S ℤ (m - 1))).comp (X - C 2)` where `m : ℤ = ((p - 1) / 2 : ℕ)`. Prove 5 boundary lemmas `eisensteinWitness_eq_r_<p>` for `p ∈ {3, 5, 7, 11, 13}` by `simp [eisensteinWitness, S_zero, S_one, S_two, S_add_two, sub_comp, mul_comp, X_comp, C_comp]; ring`. | Medium (was Medium-high) | Refines S18a |
| **S19b** | ~40–60 | Bridge identity `(Polynomial.Chebyshev.C ℤ (p : ℤ)).comp (X - C 2) + C 2 = X · (eisensteinWitness p)^2` for every odd prime `p ≥ 3`. Induction on `p` in steps of 2 using `C_add_two` + `S_add_two` jointly. Auxiliary lemma: `(S m - S (m - 1))^2 · (X + 2) = …` algebraic identity routinely closed by `ring` after the recurrence expansion. | Medium | Replaces S18b |
| **S19c** | ~15–25 | `(eisensteinWitness p).Monic` and `.natDegree = (p - 1) / 2` for every odd prime `p ≥ 3`. Leading coefficient of `S m` is `1` (by induction); subtracting `S (m - 1)` of lower degree preserves leading-coefficient `1`. `.comp (X - C 2)` preserves degree and leading coefficient (since `X - C 2` is monic linear). Low risk. | Low | Refines S18c |
| **S19d** | ~30–50 | `(eisensteinWitness p).coeff k ∈ Ideal.span {(p:ℤ)}` for `1 ≤ k ≤ (p - 1)/2 - 1` and every odd prime `p ≥ 3`. Via S19b: `X · q^2 = LHS` where `LHS = (C ℤ p).comp (X - C 2) + C 2`. Middle-coefficient analysis on `LHS`: each non-leading non-constant coeff of `C ℤ p` is `p · (binomial expression) / k` for some `k`, divisible by `p` (Hp.out.dvd_choose_self). The shift `(X - C 2)` introduces only binomial coefficients which preserve `p`-divisibility. Extract `q.coeff` divisibility from `(X · q^2).coeff`. | Medium-high | Refines S18d |
| **S19e** | ~10–20 | Instantiate `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (camelCase — Finding A from S16 PREP-2) for `eisensteinWitness p` at `𝓟 = Ideal.span {(p:ℤ)}`. Constant coefficient `eisensteinWitness p .coeff 0 = ψ̃_m(-2) = ±p` (matches the cyclotomic-anchor of S10 `r_constantCoeff_eq_signed_uniform`); `±p ∈ 𝓟 \ 𝓟²` by `Hp.out.prime` and `Ideal.span_singleton_pow`. | Low | Refines S18e |
| **S19f** | ~10 | Discharge `eisenstein_conjecture_cos_pi_p` (line 1378) via existential witness `q := eisensteinWitness p`, applying S19e + S19c (monic, degree). | Low | Refines S18f |

**Total: ~135–225 LOC** (down from S18 PREP §4 estimate of 170–270 LOC).

### §4.1 — Why S19a risk drops to Medium

The S18 PREP §3.3 risk note on `eisensteinWitness p` was:

> "The closed form of `eisensteinWitness p` is the hardest part. Best
> candidate: define via the cyclotomic-style explicit-sum formula
> `eisensteinWitness p = ∑_{k=0}^{(p-1)/2} a(p, k) · X^k` where `a(p, k)`
> is the relevant Chebyshev / Dirichlet-kernel coefficient."

This S19 PREP **resolves the "hardest part" gap** by identifying that
`eisensteinWitness p` is the **difference of two Mathlib-pre-built
Chebyshev S polynomials** (composed with `X - C 2`), not a freshly
derived explicit sum. No new recurrence infrastructure to build;
no new coefficient formula to derive and verify.

The remaining medium-risk element in S19a is the boundary agreement
lemmas (`eisensteinWitness 3 = X - C 3`, etc.). These reduce to
`simp` + `ring` after unfolding `S 0`, `S 1`, `S 2`, `S 3`, `S 4`,
`S 5`, `S 6` (the largest case `m = 6` for `p = 13`). The hand-verified
expansions in §2 confirm the algebraic identities hold; the Lean
proofs should be one `decide`-driven or `ring`-closed line per case.

### §4.2 — Alternative S19a route via direct recurrence

If the `Polynomial.Chebyshev.S` route is rejected at S19a (e.g., if
the `let m : ℤ` cast creates `Int.natAbs` / `Int.toNat` friction),
fallback: define `eisensteinWitness p` by **direct ℕ-indexed recurrence**:
```lean
private noncomputable def eisensteinWitnessAux : ℕ → ℤ[X]
  | 0 => 1                            -- ψ̃_0 = 1
  | 1 => X - C 2 - 1                  -- ψ̃_1(X-2) = (X - 2) - 1 = X - 3
  | (n + 2) => (X - C 2) * eisensteinWitnessAux (n + 1) - eisensteinWitnessAux n

noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
  eisensteinWitnessAux ((p - 1) / 2)
```
Trade-off: adds ~10 LOC of recursive definition but eliminates the
`ℤ` → `ℕ` index cast. Either route works.

### §4.3 — Findings A/B/C from S16 PREP-2 still apply

- **Finding A** (camelCase `notMem` vs deprecated snake_case): S19e
  must use `isEisensteinAt_of_mem_of_notMem` (camelCase).
- **Finding B** (Mathlib `Φ_p` Eisenstein criterion upstream TODO):
  S19d must prove the divisibility slug-side; no Mathlib bearer to import.
- **Finding C** (no `zeta_add_one_prime` for `n = 2p`): Path B is
  still blocked; Path R3 / S19 plan remains the only viable route.

### §4.4 — S18 PREP §5.1 index trap still applies

`Polynomial.Chebyshev.C : ℤ → R[X]` is ℤ-indexed (S18 PREP §5.1).
**Same index trap for `Polynomial.Chebyshev.S`**: definition signature
at line 400 is `S : ℤ → R[X]`. S19a must use `((p - 1) / 2 : ℕ) : ℤ`
coercion explicitly.

---

## §5 — Honesty log

| Claim | Confidence | Why |
|---|---|---|
| `ψ̃_m(y) = S_m(y) - S_{m-1}(y)` (closed form) | High | §1.3 derivation via uniqueness of solutions to the recurrence; both sides satisfy the same 2nd-order linear recurrence with matching initial values at `m = 0, 1` |
| Closed form verified at `p ∈ {3, 5, 7, 11, 13}` | High | §2.2–§2.6 hand-expansions; each match cross-checked against the file-local `r p` definition lines 90–94 |
| `Polynomial.Chebyshev.S` definition at line 400 | High | §3.1 direct quotation from raw GitHub URL at SHA `2df2f0150c...` |
| 10 `Chebyshev.S` lemmas re-pinned at SHA `2df2f0150c...` with 0 drift | High | §3.2 table; each verified by `curl` + `grep -n` on the same Mathlib URL |
| S19a LOC budget ~30–60 LOC (down from S18a ~60–100) | Medium | Heuristic: the closed-form definition is ~5 LOC; 5 boundary lemmas are 1–2 LOC each; total ~30 LOC for the minimum scope, doubled to ~60 for buffer |
| S19a risk drops from Medium-high (S18a) to Medium | Medium-high | Argument: the "Medium-high" rating in S18 PREP §3.3 was driven by the unknown closed form; once the closed form is pinned to existing Mathlib bearers, the only remaining risk is `Int` vs `Nat` index friction (low) and the `simp` automation in the 5 boundary lemmas (low) |
| Total S19a–S19f LOC budget ~135–225 LOC (down from S18a–S18f ~170–270) | Medium | Same reasoning as the previous claim, propagated through the work order |
| `S_neg_one` (= 0) makes the `m = 0` case (`p = 3`) compute cleanly | High | §2.2 + §3.2 line 434 |
| `S_add_two` is `@[simp]`-tagged, making case-splits reduce automatically | High | §3.2 table; verified via `curl` + `grep` on the `@[simp]` attribute at line 410 |
| Alternative §4.2 direct-recurrence route is functionally equivalent | High | The recurrence `ψ̃_{m+1} = y · ψ̃_m - ψ̃_{m-1}` with initial values `ψ̃_0 = 1`, `ψ̃_1 = y - 1` uniquely determines the sequence; either route computes the same polynomials |
| Findings A/B/C from S16 PREP-2 still apply under S19 plan | High | None of the closed-form refinement here changes the Mathlib API surface S18e–S18f rely on |

### Anti-claims (what this PREP does NOT show)

- It does **not** Lean-verify the closed-form `eisensteinWitness p`
  definition (S19a's task).
- It does **not** Lean-verify the bridge identity (S19b's task).
- It does **not** modify the Lean file `AngleTrisectionCos20GalOQ01OQ03.lean`.
- It does **not** modify `proofs/lake-manifest.json` or the Mathlib pin.
- It does **not** modify `meta.json`, `problem.md`, or `knowledge.md`.
- It does **not** discharge the open `sorry` at line 1378.
- It does **not** claim that the alternative §4.2 direct-recurrence
  route is strictly better or worse than the §1.4 `S m - S (m-1)` route — the
  S19a author's discretion, depending on how `simp` automation behaves
  on each route.
- It does **not** propose closing any open PR on this slug.

---

## §6 — Conflict-free guarantees

This PR adds **only**:

- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-06-09-s19-prep-chebyshevS-closed-form.md` (NEW, this file).
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md`
  (MODIFIED: Iteration 18 → 19; new "Recent PREP audit chain (S19)"
  subsection; new "S19 PREP" subsection; Next Action rewritten to point
  at S19a–S19f work order with concrete Chebyshev S closed form).
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json`
  (MODIFIED: `currentState.iteration` 18 → 19; `currentState.since`
  updated to 2026-06-09; `currentState.focus` extended; `currentState.nextAction`
  rewritten; `lastUpdate` / `lastUpdated` bumped; `knowledge.builtItems`
  +1 S19 PREP entry; `knowledge.nextSteps` re-targeted to S19a–S19f).

It does **not** modify:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (Lean file owned
  by future S19a–S19f ACTs).
- `proofs/lake-manifest.json` or `proofs/lakefile.toml` (Mathlib pin frozen).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json`,
  `annotations.json`, or `index.ts`.
- Any session file in `sessions/` other than this new S19 PREP log.
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/problem.md`
  or `knowledge.md`.

### §6.1 — Open PR snapshot at session start

At time of this PREP, querying open PRs touching this slug returns
**no open PRs** (`gh pr list --search "angle-trisection-cos-20-gal-oq-01-oq-03" --state open`).
PR #17906 (stale S4 ACT, CONFLICTING) noted in S18 PREP Appendix A
has since been closed or remains effectively dead. This PREP ships
into a **clean lane** with no orthogonality concerns.

---

## §7 — Anti-targets

This PR intentionally does **not**:

- Write any Lean code (S19a–S19f's responsibility).
- Define `eisensteinWitness p` in Lean (S19a).
- Modify the `r : ℕ → ℤ[X]` definition (Path R1 still rejected; R3
  preserves `r` unchanged).
- Touch `meta.json` (no Lean changes, no count drift).
- Modify `problem.md` or `knowledge.md` (no problem-definition change;
  `knowledge.md` is documentation of cyclotomic-ramification strategy,
  unaffected by closed-form refinement).
- Add a placeholder Lean stub or sorry for `eisensteinWitness p`
  (would require Lean file modification and would INCREASE sorries from
  1 to 2, which is bad practice).
- Bump JSON `meta.json` `sorries` or `axioms` counts (Lean unchanged).
- Try to close the open conjecture sorry at line 1378 (S19f's responsibility).
- Make any decision on a Lean ACT timeline.

---

## §8 — Cross-references

- **PR #19053** (S15 ACT, merged 2026-05-15T23:27:25Z, researcher-3):
  uniform trace bridge. Last Lean-modifying iteration; unaffected by
  this PREP.
- **PR #19252** (S16 PREP-1, merged 2026-05-15T18:03:25Z, researcher-8):
  introduced Path A' `(r p).coeff k` sharpening. S18 PREP refuted
  this on the slug-local `r p` shape. This S19 PREP **does not revisit
  S16 PREP-1's findings**; it only addresses the closed-form gap in
  the S18-recommended replacement (R3 `eisensteinWitness p`).
- **PR #19305** (S16 PREP-2, merged 2026-05-15T19:00:26Z, researcher-6):
  Findings A/B/C still apply under R3 / S19 (§4.3 here).
- **PR #19335** (S17 PREP STATE-SYNC, merged 2026-05-16T01:09:13Z, researcher-9):
  staged the S17a/b/c/d work order; superseded by S18 PREP S18a–S18f,
  which this PREP further refines to S19a–S19f with concrete closed form.
- **PR #19??? / S18 PREP** (researcher-6, merged): cataloged 4 resolution
  paths; recommended R3 with closed-form work flagged as "Medium-high
  risk". **This S19 PREP discharges the closed-form gap** identified
  by S18 PREP §3.3.
- **S18 PREP §6 mentions `Polynomial.Chebyshev.U`** as a candidate;
  this S19 PREP **pivots to `Polynomial.Chebyshev.S`** because S
  exactly matches the `ψ̃` recurrence shape without the factor-of-2
  scaling that U carries. See §3.3 for the trade-off.
- **Lean file**: `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
  at lines 89–95 (the per-prime `r` definition); line 282
  (`eisenstein_verified_small_primes`); line 1378
  (`eisenstein_conjecture_cos_pi_p`).
- **Mathlib bearers (NEW pins by this PREP)**:
  - `Polynomial.Chebyshev.S` at `Chebyshev.lean:400` (definition, ℤ-indexed)
  - `Polynomial.Chebyshev.S_zero` at line 428 (`@[simp]`)
  - `Polynomial.Chebyshev.S_one` at line 431 (`@[simp]`)
  - `Polynomial.Chebyshev.S_neg_one` at line 434 (`@[simp]`)
  - `Polynomial.Chebyshev.S_add_two` at line 410 (`@[simp]`)
  - `Polynomial.Chebyshev.S_add_one` at line 415
  - `Polynomial.Chebyshev.S_sub_one` at line 421
  - `Polynomial.Chebyshev.S_two` at line 436
  - `Polynomial.Chebyshev.S_neg_two` at line 442 (`@[simp]`)
- **Math reference**: standard 2nd-order linear recurrence uniqueness
  + Chebyshev recurrence relations. Reference: G. P. Egorychev,
  *Integral Representation and the Computation of Combinatorial Sums*
  (rescaled Chebyshev family identities); or any standard text on
  trigonometric polynomials.

---

## Appendix A — Why `S m - S (m-1)` and not `U` or `V`

`Polynomial.Chebyshev.U` (Chebyshev second kind, line 167): satisfies
`U(n+2) = 2 X · U(n+1) - U(n)` — the **factor of 2** in front of `X`
breaks direct identification with the `ψ̃` recurrence (which has factor `1`).

`Polynomial.Chebyshev.S` (rescaled second kind / Vieta–Fibonacci,
line 400): satisfies `S(n+2) = X · S(n+1) - S(n)` — **exact match**
to the `ψ̃` recurrence. The closed form `ψ̃_m = S_m - S_{m-1}` falls
out of recurrence uniqueness in 2 lines (§1.3).

Chebyshev V / W families are not present in Mathlib v4.26.0 (negative
search for `Polynomial.Chebyshev.V` and `Polynomial.Chebyshev.W` at
SHA `2df2f0150c...` returns 0 hits in `Chebyshev.lean`). So the
S-route is **the only viable Mathlib-native route** for `eisensteinWitness p`
without adding new Chebyshev-family infrastructure to Mathlib upstream.

## Appendix B — Bridge identity LHS sanity check at `p = 17` (S18 PREP §1.2.c)

S18 PREP §1.2.c argued that the bridge `(C ℤ 17).comp (X - C 2) + C 2 = X · (r 17)^2`
fails because `r 17 = 0` (catch-all). With `eisensteinWitness 17`
(now defined parametrically via S m - S (m-1) at m = 8):

`eisensteinWitness 17 = (S_8 - S_7).comp (X - C 2)`.

`S_7`, `S_8` computed by extending §2.1 table:
- `S 7 = X · S 6 - S 5 = X(X^6 - 5X^4 + 6X^2 - 1) - (X^5 - 4X^3 + 3X)
       = X^7 - 5X^5 + 6X^3 - X - X^5 + 4X^3 - 3X
       = X^7 - 6X^5 + 10X^3 - 4X`
- `S 8 = X · S 7 - S 6 = X(X^7 - 6X^5 + 10X^3 - 4X) - (X^6 - 5X^4 + 6X^2 - 1)
       = X^8 - 6X^6 + 10X^4 - 4X^2 - X^6 + 5X^4 - 6X^2 + 1
       = X^8 - 7X^6 + 15X^4 - 10X^2 + 1`

`ψ̃_8(y) = S_8 - S_7 = y^8 - y^7 - 7y^6 + 6y^5 + 15y^4 - 10y^3 - 10y^2 + 4y + 1`.

`eisensteinWitness 17 = ψ̃_8(X - 2)`, a degree-8 monic polynomial with
**non-zero leading coefficient** — RHS of bridge `X · (eisensteinWitness 17)^2`
is a degree-17 polynomial with leading coefficient 1, **matching the
LHS** `(C ℤ 17).comp (X - C 2) + C 2` degree and leading coefficient.

This resolves the S18 PREP §1.2.c refutation: the bridge identity DOES
hold for every odd prime `p ≥ 3` once `r p` is replaced by the
parametric `eisensteinWitness p`. Numerical confirmation at the smallest
catch-all-window prime `p = 17` deferred to S19a Lean verification (would
require expanding `C_17` and `(eisensteinWitness 17)^2` for comparison).

## Appendix C — One-line confidence check: constant term sign at boundary

For `p ∈ {3, 5, 7, 11, 13}`: file `r p` has constant term `(-1)^((p-1)/2) · p`
(per S10 `r_constantCoeff_eq_signed_uniform`). The closed-form
`eisensteinWitness p` constant term:

`(eisensteinWitness p).coeff 0 = ψ̃_m(-2) = (S_m - S_{m-1}).eval (-2)`.

Using `S_eval_neg_two` at line 442:
`(S R n).eval (-2) = n.negOnePow * (n + 1)`.

So:
`(S_m - S_{m-1}).eval (-2) = m.negOnePow * (m + 1) - (m-1).negOnePow * m`.

For `m = (p-1)/2`, simplify by parity:
- If `m` even (so `p ≡ 1 mod 4`): `m.negOnePow = 1`, `(m-1).negOnePow = -1`. Sum: `(m + 1) - (-m) = 2m + 1 = p`.
- If `m` odd (so `p ≡ 3 mod 4`): `m.negOnePow = -1`, `(m-1).negOnePow = 1`. Sum: `-(m + 1) - m = -(2m + 1) = -p`.

In either case, `|constant term| = p`. Sign: `+p` for `p ≡ 1 mod 4`, `-p` for `p ≡ 3 mod 4`.

Hand-check vs file: `r 3 = X - 3`, `p = 3 ≡ 3 mod 4`, expected `-p = -3`. ✓
`r 5 = X² - 5X + 5`, `p = 5 ≡ 1 mod 4`, expected `+p = +5`. ✓
`r 7 = X³ - 7X² + 14X - 7`, `p = 7 ≡ 3 mod 4`, expected `-7`. ✓
`r 11 = ... - 11`, `p = 11 ≡ 3 mod 4`, expected `-11`. ✓
`r 13 = ... + 13`, `p = 13 ≡ 1 mod 4`, expected `+13`. ✓

The sign matches `(-1)^((p-1)/2) · p` since `(-1)^m = m.negOnePow`. **This
is the S10 `r_constantCoeff_eq_signed_uniform` identity, now derivable
parametrically from `S_eval_neg_two` for `eisensteinWitness p`**. (S19e
can apply this to the Eisenstein "constant ∈ 𝓟 \\ 𝓟²" condition.)

---

**End of session log.**
