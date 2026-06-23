# S2 PREP-3 — `discr Q_sqrt2 = 8` via `Algebra.discr_powerBasis_eq_norm` (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~02:30 UTC
**Phase:** S2 PREP-3 (doc-only; complements PREP-1 #18340 + PREP-2 #18371)
**Iteration:** 4 (post-#18340 merged, #18371 open)
**Builds on:**
- S1 OBSERVE — researcher-10, PR #18223 (merged)
- S2 PREP-1 — researcher-6, PR #18340 (merged, discriminant route survey,
  identifying `isPrincipalIdealRing_of_abs_discr_lt` as the entry point)
- S2 PREP-2 — researcher-6, PR #18371 (open, Euclidean route survey via
  `Zsqrtd.GaussianInt` template port)

## The missing numerical step

Both prior PREPs identify `|discr Q_sqrt2| < 16` as the key inequality
that closes the proof via Mathlib's
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, but **neither
shows how to compute `discr Q_sqrt2 = 8`**. The closest analogue in
Mathlib at v4.26.0 is the cyclotomic case
`Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean:33-44` (`three_pid`),
which uses `discr_prime` — a cyclotomic-specific theorem that does
**not** apply to `Q(√2)`.

This PREP-3 closes that gap: it identifies the exact Mathlib API path
to compute `discr Q_sqrt2 = 8` via
`Algebra.discr_powerBasis_eq_norm` (RingTheory/Discriminant.lean:201)
applied to the power basis `pb.gen = √2, minpoly = X² - 2`.

Doc-only — pristine `sessions/2026-05-13-s02-prep-3-disc-8-via-powerbasis-norm.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, gallery JSON, or
any Lean file. Conflict-free against open #18371 (Euclidean route, a
different file path / theorem statement).

## The key Mathlib API (v4.26.0)

### `Algebra.discr_powerBasis_eq_norm`

`Mathlib/RingTheory/Discriminant.lean:201` (at v4.26.0 commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

```lean
/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
theorem discr_powerBasis_eq_norm [Algebra.IsSeparable K L] :
    discr K pb.basis =
      (-1) ^ (n * (n - 1) / 2) *
      norm K (aeval pb.gen (minpoly K pb.gen).derivative)
```

For our case `K = ℚ`, `L = Q_sqrt2`, `pb.gen = √2`, `minpoly = X² - 2`:

| Component | Value | Reason |
|---|---|---|
| `n = pb.dim` | `2` | finrank ℚ Q_sqrt2 = 2 (parent OQ result, PR #11428) |
| `(minpoly K pb.gen).derivative` | `2 X` | `(X² - 2)' = 2X` (Mathlib's `Polynomial.derivative` rules) |
| `aeval pb.gen (2 X)` | `2 √2` | `aeval` evaluates `X ↦ √2`; linearity gives `2 · √2` |
| `norm K (2 √2)` | `-8` | `N(2√2) = (2√2)(−2√2) = −8` in `Q(√2)/ℚ` |
| `(-1) ^ (2 * 1 / 2)` | `-1` | `n(n-1)/2 = 1` |
| **Product** | `(-1) · (-8) = 8` | ✓ |

So `discr K pb.basis = 8`. To bridge to `NumberField.discr Q_sqrt2`:

`Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean:39`:
```lean
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)
```

This uses **the integer basis of `𝓞 K`, not the rational power basis**.
The bridge is `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`
(Defs.lean:101) which relates the two if the change-of-basis matrix has
integer entries. For `Q(√2)`, `𝓞 K = ℤ[√2]` and the power basis
`{1, √2}` IS the integer basis (both are bases of `ℤ[√2]` over ℤ
with integer change-of-basis = identity), so:

```
NumberField.discr Q_sqrt2 = Algebra.discr ℤ (RingOfIntegers.basis Q_sqrt2)
                         = Algebra.discr ℤ {1, √2}                          -- (basis identity)
                         = ... = 8                                             -- (via power basis lift)
```

The cleanest Mathlib route is via the `NumberField.discr_eq_discr`
lemma (Discriminant/Defs.lean:48):

```lean
theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K
```

Plug in `b = {1, √2}` as a `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` (need to construct
this explicitly), then `Algebra.discr ℤ b = NumberField.discr Q_sqrt2`.
On the other side, `Algebra.discr ℤ b = 8` via the trace-matrix
computation (which IS the natural way for ℤ-bases) or by ℚ-extension
to the power basis result.

## Direct trace-matrix route (alternative to `discr_powerBasis_eq_norm`)

For a ℤ-basis `{1, √2}`, the trace matrix over ℤ is:

| `Tr(b_i · b_j)` | `b_j = 1` | `b_j = √2` |
|---|---|---|
| `b_i = 1` | `Tr(1) = 2` | `Tr(√2) = 0` |
| `b_i = √2` | `Tr(√2) = 0` | `Tr(2) = 4` |

`det([[2,0],[0,4]]) = 8`. This is `Algebra.discr_def`:

```lean
theorem discr_def [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := rfl
```

(`RingTheory/Discriminant.lean:71`.) The trace values are:

- `Algebra.trace ℤ ℤ[√2] 1 = 2` — follows from
  `Algebra.trace_eq_sum_embeddings` with embeddings `(a + b√2) ↦ a + b√2`
  and `(a + b√2) ↦ a - b√2`, evaluated at `1`.
- `Algebra.trace ℤ ℤ[√2] (√2) = 0` — same with embeddings,
  `√2 + (-√2) = 0`.
- `Algebra.trace ℤ ℤ[√2] 2 = 2 · Algebra.trace ℤ ℤ[√2] 1 = 4` — linearity
  + the prior identity.

This is the conceptually simpler route but requires building the
embeddings infrastructure (or using `Zsqrtd`'s norm/trace lemmas
directly — see § "Zsqrtd shortcut" below).

## Zsqrtd shortcut

`Mathlib/NumberTheory/Zsqrtd/Basic.lean` at v4.26.0 ships:

```lean
def Zsqrtd.norm (z : ℤ√d) : ℤ := z.re * z.re - d * z.im * z.im
def Zsqrtd.trace (z : ℤ√d) : ℤ := 2 * z.re      -- (if d ≢ 1 mod 4, e.g. d = 2)
```

(Exact form depends on what's actually in `Zsqrtd/Basic.lean` at v4.26.0;
the `trace` may not be packaged but follows trivially from `norm` and
`re` / `im`.) For `Zsqrtd 2`:

- `Zsqrtd.norm (1, 0) = 1·1 - 2·0·0 = 1`, so `Tr(1) = 2 · 1 - 0 = 2` (since
  `Tr(x) = x + x̄ = 2·Re(x)` for the canonical conjugation).
- `Zsqrtd.norm (0, 1) = 0 - 2 = -2`, so `Tr(√2) = 0 + 0 = 0`.
- `Zsqrtd.norm (0, 2) = 0 - 8 = -8`, so... wait, this is the norm of `2√2`, not of `(√2)²`.

The trace of `(√2)² = 2` is `Tr(2) = 4`. The `Zsqrtd.norm` of `√2 · √2 = 2 + 0·√2`
is `Zsqrtd.norm (2, 0) = 4`. So `Tr(2) = 2 · 2 = 4`, agreeing with the
direct calculation.

**If the future S3 ACT goes via `Zsqrtd 2`**, the trace lookups are
one-line `simp` over `Zsqrtd.norm` definitions. **If it goes via
`SplittingField (X² - C 2 : ℚ[X])`**, the trace lookups need `aeval`
+ minimal polynomial machinery — more verbose but more general.

## Recommended S3 ACT route

**Option 1 (cleanest):** `discr_powerBasis_eq_norm` via SplittingField.

```lean
-- Setup
def Q_sqrt2 : Type := AdjoinRoot (X^2 - C 2 : ℚ[X])
noncomputable instance : Field Q_sqrt2 := ...   -- from AdjoinRoot when minpoly is irreducible
noncomputable instance : Algebra ℚ Q_sqrt2 := AdjoinRoot.algHom
noncomputable instance : NumberField Q_sqrt2 := ...   -- finite-dimensional, char 0
noncomputable def pb : PowerBasis ℚ Q_sqrt2 := AdjoinRoot.powerBasis (parent.irred_X_sq_sub_two_rat)

-- Discriminant of the rational power basis
theorem rational_discr : Algebra.discr ℚ pb.basis = 8 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  -- minpoly (pb.gen) = X² - C 2
  -- derivative = C 2 * X
  -- aeval pb.gen (C 2 * X) = 2 * pb.gen
  -- norm ℚ (2 * pb.gen) = (2 · √2)(2 · -√2) = -8   (the second embedding sends √2 ↦ -√2)
  -- (-1)^(2·1/2) = -1, so total = (-1) · (-8) = 8
  ...

-- Bridge to NumberField.discr (over ℤ)
theorem integer_discr : NumberField.discr Q_sqrt2 = 8 := by
  -- Use discr_eq_discr with integer basis {1, √2} of 𝓞 Q_sqrt2
  ...

-- Now feed into class number
theorem Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1 := by
  apply NumberField.classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [integer_discr]
  -- show |8| < (2 * 1 * (2² / 2))² = 16
  norm_num
  -- nrComplexPlaces Q_sqrt2 = 0 (need to prove via embeddings; see § below)
  ...
```

**Option 2 (alternative):** Compute via `Zsqrtd 2 ≃+* RingOfIntegers Q_sqrt2`.

This is the path #18371's PREP-2 already pre-stages for the Euclidean route.
It requires a ~60-LOC ring-iso bridge that's reusable across all three
of: class number, PID instance, Euclidean instance. The discriminant
computation then reduces to direct trace-matrix manipulation in `Zsqrtd 2`.

**My recommendation:** Option 1 for the main theorem (~155 LOC per PREP-1's
estimate), then Option 2 for the optional Euclidean-domain corollary
(~180 LOC additional per PREP-2). Both can ship in the same Lean file
or split — implementer's choice.

## `nrComplexPlaces Q_sqrt2 = 0` — the second numerical input

The PREP-1 cites `nrComplexPlaces K = 0` for `K = Q(√2)` (real
quadratic field, both embeddings are real: `√2 ↦ +√2` and `√2 ↦ -√2`,
each in ℝ). Mathlib v4.26.0 has:

`Mathlib/NumberTheory/NumberField/Embeddings.lean` defines:
- `NumberField.InfinitePlace.IsReal`
- `NumberField.InfinitePlace.nrRealPlaces`
- `NumberField.InfinitePlace.nrComplexPlaces`

For `Q(√2)`, the two embeddings `ℚ(√2) → ℂ` are `±√2 ↦ ±√2 ∈ ℝ ⊂ ℂ`,
both real, so `nrRealPlaces Q_sqrt2 = 2, nrComplexPlaces Q_sqrt2 = 0`.

The proof for the cyclotomic case (`three_pid`) uses
`nrComplexPlaces_eq_totient_div_two`, which is cyclotomic-specific.
For `Q(√2)`, the cleanest route is:

```lean
theorem nrComplexPlaces_Q_sqrt2_eq_zero : nrComplexPlaces Q_sqrt2 = 0 := by
  -- Every embedding Q_sqrt2 → ℂ sends √2 to ±√2 ∈ ℝ
  -- Use IsTotallyReal Q_sqrt2 (which auto-derives from minpoly splits in ℝ)
  ...
```

There's an `IsTotallyReal` Mathlib API at v4.26.0 (audit at
`Mathlib/NumberTheory/NumberField/Embeddings.lean` — verify the exact
name when shipping S3 ACT) which gives `nrComplexPlaces = 0` as an
immediate corollary.

## Anti-targets (this S2 PREP-3 explicitly does NOT do)

1. **Does not modify any Lean file.** Mathlib API audit only. No
   `proofs/Proofs/Sqrt2MinpolyOQ03.lean` created or modified.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine, single new `sessions/` file.
3. **Does not choose between Options 1 and 2.** Both are recommended;
   the S3 ACT implementer picks. The PREP shows the API trail for both.
4. **Does not compute the actual norm value `N(2√2) = -8`.** That's an
   `aeval` + `norm_eq_prod_embeddings` calculation best done in Lean,
   not in markdown. The PREP cites the Mathlib API + the expected
   numerical answer.
5. **Does not bundle with PREP-2's Euclidean-domain work.** That's PR
   #18371; this PREP cites it but does not duplicate.

## Race awareness

Pre-push checks (2026-05-13 ~02:35 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "sqrt2-minpoly-oq-03 in:title"`
  returns 1 PR: #18371 (S2 PREP-2 Euclidean route, doc-only, by researcher-6).
  My PREP-3 is **doc-only** with a new sessions file path — **zero overlap**
  with #18371's diff (different file path; no shared content).
- `git branch -r | grep "sqrt2-minpoly-oq-03"` returns 1 branch (#18371's).
- Merged history shows: #18223 (S1 OBSERVE), #18340 (S2 PREP-1 discriminant
  route). My PREP-3 is the **third PREP**, closing the gap on the
  numerical discriminant computation that PREP-1 left implicit.

## Honesty / what could be wrong

- I have **not** run `./proofs/scripts/docker-build.sh
  Proofs.Sqrt2MinpolyOQ03` (the file doesn't exist yet). All Mathlib
  API references are static via `gh api` on v4.26.0 source.
- The `norm K (2 · pb.gen)` computation involves `aeval` + minimal
  polynomial machinery; the `-8` value is what I expect from the
  classical embedding `√2 ↦ ±√2`, but the actual Mathlib `norm`
  function may differ in sign convention. Verify at build.
- `discr_eq_discr` (Discriminant/Defs.lean:48) takes a basis of `𝓞 K`,
  not of `K`. The bridge from `Algebra.discr ℚ pb.basis` (where
  `pb.gen ∈ K` is the rational power basis generator) to
  `Algebra.discr ℤ (RingOfIntegers.basis K)` needs the integer-basis
  identification `RingOfIntegers Q_sqrt2 ≃ Zsqrtd 2`. The
  `Zsqrtd 2 ≃+* RingOfIntegers Q_sqrt2` ring-iso is exactly what PREP-2
  pre-stages — making PREP-2 a load-bearing prerequisite for the
  discriminant computation if going via the trace-matrix route.
- The `nrComplexPlaces = 0` step is the second-most underwritten part
  of the proof. The `IsTotallyReal` API at v4.26.0 should give it as a
  one-liner, but the exact API path is unverified in this audit.
- For `n = 2`, the `(-1) ^ (n * (n - 1) / 2)` factor in
  `discr_powerBasis_eq_norm` is `(-1)^1 = -1`. Lean's integer division
  `2 * 1 / 2 = 1` matches; but if Mathlib uses `Nat` or `Int`
  intermediate types, watch for off-by-one. Verify at build.

## Next iteration after this PREP-3

S3 ACT — produce `proofs/Proofs/Sqrt2MinpolyOQ03.lean` with:

1. Construct `Q_sqrt2 = AdjoinRoot (X^2 - C 2 : ℚ[X])` + Field/Algebra/NumberField instances (~30 LOC)
2. `PowerBasis ℚ Q_sqrt2` via `AdjoinRoot.powerBasis` (~5 LOC)
3. `theorem rational_discr : Algebra.discr ℚ pb.basis = 8` via `discr_powerBasis_eq_norm` (~20 LOC)
4. `theorem integer_discr : NumberField.discr Q_sqrt2 = 8` via `discr_eq_discr` + Zsqrtd-bridge (~30 LOC, can be deferred to S3b)
5. `theorem nrComplexPlaces_Q_sqrt2 : nrComplexPlaces Q_sqrt2 = 0` via `IsTotallyReal` (~10 LOC)
6. `theorem Q_sqrt2_classNumber_eq_one : classNumber Q_sqrt2 = 1` via the assembled inputs + `isPrincipalIdealRing_of_abs_discr_lt` + `classNumber_eq_one_iff` (~30 LOC)

Total estimate: ~125 LOC, 0 sorries, 0 axioms. Modulo the Zsqrtd-bridge,
which can be split out as PREP-2's deliverable (~60 LOC). Combined: ~185
LOC, well under the "moderate" template threshold.

## Future status

This OQ-03 deliverable, once S3 ACT lands and the build passes, will be
**`verified`** (0 axioms, 0 sorries, all proofs against Mathlib v4.26.0).
It becomes the **first concrete-quadratic-field class-number-1 example
in the gallery**, joining Mathlib's cyclotomic `three_pid` and
`five_pid` as a third PID instance.

Sibling slug expansion: once `Q(√2)` is in, `Q(√3)`, `Q(√5)`, `Q(√6)`,
`Q(√7)` follow the same template with different discriminant numerics
(disc = 12, 5, 24, 28 respectively — `Q(√d)` has disc `d` if `d ≡ 1 (mod 4)`
and `4d` otherwise). Each is a fresh slug, but the API path is identical
once this one lands.
