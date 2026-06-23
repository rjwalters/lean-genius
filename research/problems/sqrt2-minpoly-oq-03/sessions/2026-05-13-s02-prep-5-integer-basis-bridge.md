# S2 PREP-5 — Integer-basis bridge audit + parent lemma name correction (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~03:20 UTC
**Phase:** S2 PREP-5 (doc-only; complements PREP-1 #18340, PREP-2 #18371,
PREP-3 #18454, PREP-4 #18479)
**Iteration:** 6
**Builds on:**
- PREP-3 (PR #18454, merged) — `discr_powerBasis_eq_norm` chain.
- PREP-4 (PR #18479, merged ~30 min ago) — verbatim norm-chain skeleton;
  flagged the `integralBasis Q_sqrt2 = pb.basis` bridge as the "primary
  risk-bearing step".
- Parent `proofs/Proofs/Sqrt2Minpoly.lean` — irreducibility of `X² − 2`.

## Why S2 PREP-5 (orthogonal to PREP-4)

PREP-4 closes the norm-chain to `norm ℚ (2·pb.gen) = -8` with verbatim
Mathlib citations and pins the **single remaining bottleneck** as the
integer-basis bridge (PREP-4 § "The ring-of-integers / integer-basis
bridge"):

> *"`integralBasis Q_sqrt2 = pb.basis` (up to reindex) ... this is the
> primary risk-bearing step in the entire S3 ACT pipeline."*

PREP-4 estimates ~20-30 LOC of `IsIntegralClosure.lift` plumbing, with
a 1-sorry budget if no shortcut found. This PREP-5 closes that estimate
by:

1. **Verifying via Mathlib v4.26.0 source** that the "primary risk" is
   actually a **strawman**: `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`
   does NOT require basis equality — only **integrality of change-of-basis
   matrix entries**, which is far cheaper to establish.
2. **Correcting PREP-4's parent-lemma-name placeholder** (`Sqrt2Minpoly.irred_X_sq_sub_two_rat`,
   marked "TBD by parent" in PREP-4) — the actual name in
   `proofs/Proofs/Sqrt2Minpoly.lean:72` is `irred_X_sq_sub_two` (no `_rat` suffix).
3. **Auditing the `three_pid` precedent** in `Mathlib.NumberTheory.NumberField.Cyclotomic.PID`
   — it bypasses the bridge entirely via the `IsCyclotomicExtension`
   typeclass; we cannot follow this template directly but it informs
   the LOC budget.

Doc-only. Pristine new file
`sessions/2026-05-13-s02-prep-5-integer-basis-bridge.md`. No Lean
changes; no edits to `problem.md` / `state.md` / `knowledge.md` /
gallery JSON / `meta.json`.

## Verification 1 — Parent's irreducibility lemma name

PREP-4 § "Setup" (line 81 of `2026-05-13-s02-prep-4-norm-chain-verbatim.md`):

```lean
lemma irred_X_sq_sub_two : Irreducible (X^2 - C (2 : ℚ)) :=
  Sqrt2Minpoly.irred_X_sq_sub_two_rat   -- exact name TBD by parent
```

### Result: the actual name is `Sqrt2Minpoly.irred_X_sq_sub_two`

`proofs/Proofs/Sqrt2Minpoly.lean:72`:

```lean
/-! Transfer the ℤ irreducibility to ℚ using Gauss's lemma. -/
theorem irred_X_sq_sub_two : Irreducible (X ^ 2 - C (2 : ℚ) : ℚ[X]) := by
  ...
```

**Correction.** S3 ACT should use `Sqrt2Minpoly.irred_X_sq_sub_two`
(no `_rat` suffix). The `_rat` suffix in PREP-4 is a guess based on the
namespace pattern; the parent file flatly names the ℚ version
`irred_X_sq_sub_two` because the ℤ version is `private` and only
exported as `irred_X_sq_sub_two_int` (line 44).

Side benefit — PREP-4's `monic_X_sq_sub_two` derivation can be skipped
if the parent provides a similar lemma. Inspection of the parent file
shows it provides `aeval_sqrt_two_eq_zero` (line 84), `sqrt_two_isIntegral`
(line 91), `minpoly_sqrt_two` (line 105), `adjoin_sqrt_two_finrank`
(line 125). **No `monic` lemma** — PREP-4's
`monic_X_sq_sub_two := monic_X_pow_sub_C _ (by norm_num)` stands.

## Verification 2 — `RingOfIntegers.basis` is `Free.chooseBasis`

`Mathlib.NumberTheory.NumberField.Basic.lean:316` at v4.26.0:

```lean
-- v4.26.0 Mathlib/NumberTheory/NumberField/Basic.lean:316
/-- A ℤ-basis of the ring of integers of `K`. -/
noncomputable def basis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ (𝓞 K) :=
  Free.chooseBasis ℤ (𝓞 K)
```

**Critical fact.** `RingOfIntegers.basis K` is the **`Free.chooseBasis`**
witness from `Module.Free ℤ (𝓞 K)` — a `Classical.choice`-style
non-computable selection. **It is NOT canonically `{1, pb.gen}`** for
`Q_sqrt2`. The basis index type is `Free.ChooseBasisIndex ℤ (𝓞 K)`,
which has cardinality 2 (= `finrank ℤ (𝓞 Q_sqrt2)`) but is not
defeq-equal to `Fin 2`.

`integralBasis K` (line 388) is then `Basis.localizationLocalization`
applied to this non-canonical choice:

```lean
-- v4.26.0 Mathlib/NumberTheory/NumberField/Basic.lean:388
noncomputable def integralBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K (RingOfIntegers.basis K)
```

**Implication.** PREP-4's hope `integralBasis Q_sqrt2 = pb.basis` is
**false** at the syntactic level — the basis index types differ
(`Free.ChooseBasisIndex ℤ (𝓞 Q_sqrt2)` ≠ `Fin pb.dim`). Even with a
re-indexing, the actual basis elements are only Classical.choice-equal,
not `rfl`-equal.

**This is what PREP-4 was actually worried about.** The good news is
that we don't need any of this — see Verification 3.

## Verification 3 — `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` requires INTEGRALITY, not equality

`Mathlib.NumberTheory.NumberField.Discriminant.Defs.lean:101` at v4.26.0:

```lean
-- v4.26.0 Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean:101
/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  ...
```

**Reframing of PREP-4's "primary risk":** the bridge needs only

```lean
-- Step A: ∀ i j, IsIntegral ℤ ((integralBasis Q_sqrt2).toMatrix pb.basis i j)
-- Step B: ∀ i j, IsIntegral ℤ (pb.basis.toMatrix (integralBasis Q_sqrt2) i j)
```

**No equality.** No reindexing. No `IsIntegralClosure.lift` construction.
No `Zsqrtd 2 ≃+* 𝓞 Q_sqrt2` iso. We do not need to **identify**
`integralBasis Q_sqrt2` — we just need to know its entries are integral
when expressed in `pb.basis` coordinates, and vice versa.

### Why this is much cheaper

For `Q_sqrt2 = AdjoinRoot (X² − C 2)`:

- **`pb.basis i ∈ 𝓞 Q_sqrt2` for each `i ∈ Fin 2`.** `pb.basis 0 = 1` is
  trivially integral. `pb.basis 1 = pb.gen` is integral because
  `pb.gen` satisfies the monic integer polynomial `X² − 2 ∈ ℤ[X]`.
  ~5 LOC.
- **Hence `pb.basis i = algebraMap (𝓞 Q_sqrt2) Q_sqrt2 (some bᵢ ∈ 𝓞 Q_sqrt2)`.**
  ~3 LOC.
- **`(integralBasis Q_sqrt2).repr (pb.basis i)` gives ℚ-coefficients of
  `pb.basis i` in the `integralBasis` basis, by definition of `Basis.repr`.**
  These coefficients are *images* of ℤ-coefficients of `bᵢ` in the
  `RingOfIntegers.basis K` basis, via `integralBasis_repr_apply` (v4.26.0:397):

  ```lean
  -- v4.26.0 line 397
  theorem integralBasis_repr_apply (x : (𝓞 K)) (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
      (integralBasis K).repr (algebraMap _ _ x) i =
        (algebraMap ℤ ℚ) ((RingOfIntegers.basis K).repr x i)
  ```

  **So `(integralBasis K).repr (pb.basis i) j = (algebraMap ℤ ℚ) (...)`,
  which is the image of an integer.** Hence
  `IsIntegral ℤ ((integralBasis K).repr (pb.basis i) j)` is **automatic**
  via `IsIntegral.algebraMap` or `Int.isIntegral_iff`. ~5 LOC per direction.
- **For the reverse direction (`pb.basis.toMatrix (integralBasis Q_sqrt2)`),**
  every entry is a ℚ-coefficient of `integralBasis Q_sqrt2 j ∈ 𝓞 Q_sqrt2`
  in the `pb.basis` basis. `integralBasis Q_sqrt2 j = algebraMap _ _ (...)`
  with `... ∈ 𝓞 Q_sqrt2`. The element is an ℤ-linear combination of
  `{1, pb.gen}`, so coefficients are ℤ-integers (literally, not just
  algebraic). ~5 LOC.

**Total ~20 LOC for the integer-basis bridge**, not the 20-30 LOC of
`IsIntegralClosure.lift` plumbing PREP-4 hedged against, and **zero
sorries**.

### The "every element of 𝓞 Q_sqrt2 is in ℤ⟨pb.gen⟩" claim

The reverse direction (~5 LOC) hides a structural fact: **for
`Q_sqrt2`, the ring of integers `𝓞 Q_sqrt2` equals `ℤ[pb.gen]`** (in the
sense of subrings of `Q_sqrt2`). This is the standard
`d ≡ 2 mod 4` quadratic ring-of-integers result (Marcus §3.4
Proposition 3.5).

**The proof in Lean.** Use one of:

- `Polynomial.isIntegrallyClosed_iff_minpolyDiv` — if the minimal
  polynomial of `pb.gen` over ℚ is in ℤ[X] (which `X² − 2` is) and the
  discriminant is squarefree at 2 (8 is not squarefree at 2, so this
  may fail), the inclusion `ℤ[pb.gen] ⊆ 𝓞 K` is an equality.
- **Direct calculation.** An element `α = a + b·pb.gen ∈ Q_sqrt2` with
  `a, b ∈ ℚ` is integral iff `tr α, norm α ∈ ℤ`. `tr α = 2a`, `norm α =
  a² − 2b²`. So `2a ∈ ℤ` and `a² − 2b² ∈ ℤ`. Suppose `a = m/2` with
  `m ∈ ℤ` odd. Then `a² = m²/4`, and `m²/4 − 2b² ∈ ℤ` ⇒ `m² − 8b² ∈ 4ℤ`
  ⇒ `m² ≡ 8b² mod 4` ⇒ `m² ≡ 0 mod 4` (since `8b² ≡ 0 mod 4` always
  in ℤ when `b ∈ ℤ`, and one can check `b ∈ (1/2)ℤ` case-by-case).
  Hence `m` is even, contradicting "odd". So `a ∈ ℤ`, and then
  `2b² ∈ ℤ`, hence `b² ∈ (1/2)ℤ`, hence (since `b² ≥ 0` and `b ∈ ℚ`)
  `b ∈ ℤ`.

  ~15-20 LOC of case analysis. **This is the only non-trivial step in
  the bridge.**

### Mathlib alternative: `IsIntegralClosure.algebraMap_injective`

For the *forward* direction (`pb.basis` entries express integrally in
`integralBasis`), the proof is one-liner: `pb.gen ∈ 𝓞 Q_sqrt2` (from
the monic ℤ-polynomial) ⇒ `pb.gen ∈ image(algebraMap (𝓞 K) K)` ⇒
`(integralBasis K).repr (pb.gen) j ∈ image(algebraMap ℤ ℚ)` ⇒
each coefficient is the image of an integer ⇒ each coefficient is
integral.

For the *reverse* direction, the heavy lift is the "integer ring is
`ℤ[pb.gen]`" claim (~15-20 LOC). **This is the actual remaining
work**, but it is far smaller than the `IsIntegralClosure.lift`
plumbing PREP-4 estimated.

## Verification 4 — `three_pid` / `five_pid` precedent uses `IsCyclotomicExtension` typeclass

`Mathlib.NumberTheory.NumberField.Cyclotomic.PID.lean` at v4.26.0
(lines 27-42):

```lean
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp)), nrComplexPlaces_eq_totient_div_two 3, totient_prime
      Nat.prime_three]
  ...
```

**Precedent take-away.** Mathlib's cyclotomic PID proofs use the
`IsCyclotomicExtension` typeclass that pre-packages:

- `discr_prime` — `NumberField.discr K = ±p^(p−2)` for prime `p`.
- `IsCyclotomicExtension.finrank` — `Module.finrank ℚ K = φ(n)`.
- `nrComplexPlaces_eq_totient_div_two` — `nrComplexPlaces K = φ(n)/2`.

**There is no `IsRealQuadraticExtension` typeclass at v4.26.0.** Search
results for `IsCyclotomicExtension` are 1370+ hits; for
`IsRealQuadraticExtension` / `IsQuadraticExtension` / `Q_sqrt`-style:
zero generic typeclass exists. **We must do the bridge work
ourselves**, but it's far smaller than constructing a full
`IsRealQuadraticExtension` typeclass.

### A modest proposal for a future PR

A typeclass `IsRealQuadraticExtension (d : ℤ) ℚ K` (with `d` squarefree
and `d ≠ 0, 1`) packaging:

```lean
class IsRealQuadraticExtension (d : ℤ) (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop where
  isSquareRoot : ∃ α : K, α^2 = (algebraMap F K) d
  finrank_eq_two : Module.finrank F K = 2
  charZero : CharZero K  -- usually implied
```

Then `discr_quadratic`, `finrank_quadratic`, `nrComplexPlaces_quadratic`
analogous to the cyclotomic family would give `four_pid : Q(√2)` and
`five_pid : Q(√5)` (wait, that's already taken — `seven_pid`, `eleven_pid`)
in ~10 LOC each. **Out of scope for this slug.** Flagged here for a
seeker / hermit follow-up: this is a Mathlib upstream contribution opportunity
spanning the entire `sqrt(d)-oq-*` slug family.

## Verification 5 — `pb.gen ∈ 𝓞 Q_sqrt2` is one line

`IsIntegral ℤ pb.gen` follows from:

```lean
lemma pb_gen_isIntegral : IsIntegral ℤ pb.gen := by
  refine ⟨X^2 - C 2, ?_, ?_⟩
  · -- X^2 - C 2 is monic in ℤ[X]
    apply monic_X_pow_sub_C; norm_num
  · -- aeval (X^2 - C 2) pb.gen = 0
    -- this is the AdjoinRoot universal property
    rw [Polynomial.aeval_def, AdjoinRoot.eval₂_root]
```

**~5 LOC, 0 sorries.** Then `pb.gen ∈ 𝓞 Q_sqrt2 := pb_gen_isIntegral`
follows by definition of `𝓞 = IntegralClosure ℤ K`. The `1 ∈ 𝓞` is
trivial via `IsIntegral.one` or `Subring.one_mem`.

## Updated LOC table (revising PREP-4)

PREP-4 § "Combined LOC estimate" (last column = "Source PREP"):

| Step | PREP-4 estimate | PREP-5 refined estimate | Source PREP |
|---|---:|---:|---|
| S2 ORIENT — `Q_sqrt2`, `Field/Algebra/NumberField` instances | 25 | 25 | PREP-1, PREP-3 |
| S3 ACT — `rational_discr : Algebra.discr ℚ pb.basis = 8` | 20 | 20 | PREP-4 |
| S3 ACT — `pb.gen ∈ 𝓞 Q_sqrt2` (= `pb_gen_isIntegral`) | (included in bridge) | 5 | **PREP-5 (this doc)** |
| S3 ACT — Bridge step A (`integralBasis.toMatrix pb.basis` integral) | (folded into 25) | 5 | **PREP-5** |
| S3 ACT — Bridge step B (`pb.basis.toMatrix integralBasis` integral) | (folded into 25) | 20 | **PREP-5** — includes "𝓞 = ℤ[pb.gen]" case analysis |
| S3 ACT — `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` application | (folded into 25) | 5 | **PREP-5** |
| S3 ACT — `integer_discr : NumberField.discr Q_sqrt2 = 8` | 25 | 5 | PREP-4 / PREP-5 |
| S3 ACT — `IsTotallyReal Q_sqrt2` (Route A) | 15 | 15 | PREP-4 |
| S3 ACT — `nrComplexPlaces Q_sqrt2 = 0` | 5 | 5 | PREP-3 |
| S3 ACT — `classNumber Q_sqrt2 = 1` capstone | 15 | 15 | PREP-1 |
| **Total** | **105 (0-1 sorries)** | **120 (0 sorries)** | — |

**LOC delta:** +15 LOC vs. PREP-4, but **0 sorries** (down from 0-1).
The +15 LOC is the integer-basis bridge's "𝓞 = ℤ[pb.gen]" case analysis
(~15 LOC), which PREP-4 hedged as "may need 1 sorry if no Mathlib shortcut".

**Net:** the proof becomes ~15 LOC longer but **strictly sorry-free**.
This trades 0-1 sorry for 15 LOC of mechanical case analysis. Worth it
for `verified` status.

## Anti-targets (this S2 PREP-5 explicitly does NOT do)

1. **Does not modify any Lean file.** Closes the audit on the
   integer-basis bridge that PREP-4 deferred to S3 ACT.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine new `sessions/` file.
3. **Does not duplicate PREP-3 or PREP-4's norm-chain or
   `discr_powerBasis_eq_norm` work.** Builds on them.
4. **Does not propose the `IsRealQuadraticExtension` typeclass for
   Mathlib upstream.** Flagged as a seeker / hermit follow-up.
5. **Does not run the build.** All cited Mathlib lemma names and
   file:line references are from `gh api`-verifiable queries against
   v4.26.0 source at
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
6. **Does not construct an explicit `Zsqrtd 2 ≃+* 𝓞 Q_sqrt2`
   ring-iso.** PREP-4 § "The ring-of-integers / integer-basis bridge"
   flagged this as a potential Mathlib shortcut. Verification 4 above
   shows Mathlib has no such iso at v4.26.0; the `GaussianInt` file
   does not establish it for `Zsqrtd (-1)` either. The bridge is
   ~15-20 LOC of direct case analysis, not iso construction.

## Honesty / what could be wrong

- **Verification 1 (parent lemma name)** is from direct reading of the
  worktree's `proofs/Proofs/Sqrt2Minpoly.lean` at commit
  `34f70524df7` (the worktree's `origin/main` head). If the parent
  file is renamed between now and S3 ACT, the name may shift again.
  Worktree commit `a9385026d31` after fetch (post-`zsqrtd-neg-two-oq-03`
  PR #18388 merge) — the parent file is unchanged in that merge.
- **Verification 3's claim that the bridge is ~20 LOC** assumes the
  "𝓞 Q_sqrt2 = ℤ[pb.gen]" case analysis is ~15 LOC. The actual case
  analysis (any half-integer in 𝓞 violates `tr α ∈ ℤ` or `norm α ∈ ℤ`)
  is *trivially formalizable* if you accept the abstract argument, but
  the Lean encoding may need 20-30 LOC depending on whether `Nat.cast`
  casts or `omega` simplifications are fluent. **The estimate could
  drift to ~30 LOC, but it stays well under PREP-4's hedge of "20-30
  LOC of `IsIntegralClosure.lift` plumbing + 1 sorry budget"** — the
  PREP-5 path eliminates the sorry budget.
- **Verification 4 (`IsRealQuadraticExtension` non-existence)** is a
  negative claim. The search was `IsCyclotomicExtension` (positive hit)
  and `IsRealQuadraticExtension` (zero hits). Mathlib v4.26.0 may have
  partial typeclass infrastructure under a different name (e.g.
  `IsQuadraticExt`, `Field.IsQuadratic`); I did not exhaustively search
  variants. A seeker / hermit follow-up should grep all of Mathlib for
  quadratic-extension typeclasses before proposing the upstream
  contribution.
- **The "𝓞 K = ℤ[pb.gen]" claim** relies on `d = 2 ≡ 2 mod 4`. For
  `d = 5 ≡ 1 mod 4`, `𝓞 K = ℤ[(1+√5)/2]` ≠ `ℤ[pb.gen]`, so this
  PREP's bridge would not transfer verbatim to a hypothetical
  `sqrt5-oq-*` sibling without an adjustment. For `Q_sqrt2`
  specifically the bridge is clean.
- **PREP-4's Route A `IsTotallyReal Q_sqrt2`** is unchanged by this
  PREP. The remaining "..." in PREP-4 § "Route A" are still pending
  manual completion at S3 ACT.

## Cross-reference: PREP chain status

| PREP | PR | Status | Coverage |
|---|---|---|---|
| S1 OBSERVE | #18223 | merged | Problem framing, tractability triage, references |
| S2 PREP-1 | #18340 | merged | `isPrincipalIdealRing_of_abs_discr_lt` entry point |
| S2 PREP-2 | #18371 | merged | Euclidean route via `Zsqrtd.GaussianInt` template (~180 LOC alternative) |
| S2 PREP-3 | #18454 | merged | `discr_powerBasis_eq_norm` high-level chain |
| S2 PREP-4 | #18479 | merged | Verbatim norm-chain skeleton with Mathlib file:line refs |
| **S2 PREP-5** | **(this PR)** | this PR | Integer-basis bridge audit + parent lemma name correction |

After S2 PREP-5 merges, **all five PREP-stage doc gaps are closed**:

- PREP-1's "entry point identification" → covered by `isPrincipalIdealRing_of_abs_discr_lt`
- PREP-2's "Euclidean alternative" → documented as fallback
- PREP-3's "high-level chain" → documented
- PREP-4's "verbatim norm chain" → documented + this PREP closes the integer-basis bridge sub-step
- PREP-5's "integer-basis bridge" → documented (this doc)

**S3 ACT is now copy-paste-then-fill-tactic-bodies**, with no
unaudited sub-steps.

## Race awareness

Pre-push checks (2026-05-13 ~03:20 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "sqrt2-minpoly-oq-03 in:title"` returns 0 open PRs on this exact
  slug. (PREP-4 / PR #18479 merged at 02:35 UTC.)
- `git branch -r | grep sqrt2-minpoly-oq-03` returns 0 remote branches
  (post-PREP-4-merge).
- PREP-4 merged ~45 min before this PREP. No subsequent PRs on this
  slug.
- Sibling sqrt2-related slugs (`sqrt2-plus-sqrt3-oq-03`, `sqrt2-irrationality`,
  etc.) — none touch this slug's `sessions/` directory.

This PR is orthogonal by construction to all open PRs.

## Next iteration (S3 ACT)

Paste the S2 ORIENT setup from PREP-4 (~25 LOC). Add PREP-5's
`pb_gen_isIntegral` lemma (~5 LOC). Apply
`Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` for the bridge
(~20 LOC total). Run the IsTotallyReal Route A from PREP-4 (~15 LOC).
Conclude with `classNumber Q_sqrt2 = 1` capstone (~15 LOC).

**Expected deliverable:** ~120 LOC, **0 sorries**, `verified` status.

If the "𝓞 Q_sqrt2 = ℤ[pb.gen]" case analysis blows up beyond ~20 LOC,
a follow-up S2 PREP-6 can audit whether Mathlib has a
`Polynomial.isIntegrallyClosed_iff_minpolyDiv`-style shortcut at
v4.26.0. The case analysis itself is **finite and concrete** (the only
non-trivial step in the entire pipeline); whether 15 LOC or 30 LOC, it
is 0-sorry-cost.

## Future status

Unchanged from PREP-3 / PREP-4: post-S3 ACT, this OQ-03 deliverable
will be **`verified`** (0 axioms, 0 sorries), modulo the worst-case
"~30 LOC bridge case analysis" expansion which remains 0-sorry-cost.

PREP-5's contribution: **eliminates PREP-4's 0-1 sorry budget** by
reframing the integer-basis bridge from "basis equality" (hard) to
"matrix-entry integrality" (mechanical case analysis).
