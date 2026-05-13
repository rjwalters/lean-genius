# Session S19 PREP — `p = 3` singular-reduction witness audit + numerical re-derivation (doc-only)

**Researcher**: researcher-1
**Date**: 2026-05-13
**Mode**: Doc-only (no `.lean` changes, no markdown edits outside this new file, no JSON edits)
**Predecessors**:
- PR #18427 (MERGED 2026-05-13T00:59Z, researcher-4) — S18 OBSERVE Case-B + special-prime elimination roadmap, file `2026-05-12-s18-observe-caseB-special-prime-elimination.md` (424 lines).
- Open: PR #17610 (Iter 15 universal Case-A, CONFLICTING since 2026-05-09), PR #17645 (Iter 16, CONFLICTING since 2026-05-09) — both orthogonal to this audit.
- Iter 17 (merged) — Section 27 universal Case-A theorem for `p ≡ 2 (mod 3), p ∉ {2, 5}`.
**Orthogonality**: this note revisits the **`p = 3` action item** raised in S18 §6, which explicitly requested:

> "**Action item for a future S19 mechanic session**: re-derive the correct mod-27 witness for `p = 3`."

By construction orthogonal to the Case-A iterations #17610 / #17645 (which both add more `p ≡ 2 (mod 3)` primes), and orthogonal to S18 itself (which is a Case-B / special-prime roadmap rather than a verification).

**Adds exactly one new file**:
`research/problems/hilbert-11-oq-02/sessions/2026-05-13-s19-prep-p3-singular-reduction-witness-audit.md`.

No edits to `problem.md`, `state.md`, `knowledge.md`, gallery `meta.json`, the parent `.lean` file, or any other tracked file.

---

## §1. Headline finding

**S18 OBSERVE §6 raises a false alarm. The parent file's mod-27 witness `(0, 1, 4)` IS correct under strong-form Hensel; no mechanic re-derivation is needed.**

The alarm originated in a **transcription error**: S18 §6 quotes the parent file at lines 304-310 as documenting the witness `(2, 1, 4)`. The parent file actually documents the witness `(0, 1, 4)` (`Hilbert11OQ02.lean:308`). The `(2, 1, 4)` triple does indeed fail strong-form Hensel (`v₃(F) = 1` ≯ `2·v₃(∂_z F) = 2`), so the chain of reasoning S18 §6 builds atop the misquote is internally consistent — but it isn't pointing at the parent docstring.

This S19 PREP discharges the S18 §6 mechanic action item without any `.lean` edit: the parent file is already correct.

---

## §2. What S18 OBSERVE §6 claimed (verbatim, with my line markers)

S18 OBSERVE §6 contains, near the top, the following passage (file
`2026-05-12-s18-observe-caseB-special-prime-elimination.md` around line 250):

> "The parent file's lines 304-310 say:
>
> > 'p = 3. *Singular reduction.* … We must climb to mod 27 = 3³ before the
> > strong-form Hensel hypothesis `|f(α)|_p < |f'(α)|_p²` is met. The
> > witness `(2, 1, 4)` gives `3·8 + 4·1 + 5·64 = 24 + 4 + 320 = 348 = 12·29`,
> > with `v_3(348) = 1` … `v_3(15z²) = 1 + 2·v_3(z)`. For z = 4: `v_3(15·16) = v_3(240) = 1`.
> > Since `v_3(f) ≥ 3 > 2 · v_3(∂_z f) = 2`, strong-form Hensel applies.'
>
> Wait — the docstring text suggests `v_3(348) = 1`, which would mean
> `‖F(2, 1, 4)‖_3 = 3^{-1}`, but `v_3(240) = 1` gives `‖∂_z F‖_3 = 3^{-1}`,
> so `3^{-1} < (3^{-1})² = 3^{-2}` is again **FALSE**. The numerical
> verification in the docstring appears inconsistent."

S18 §6 then constructs the alternative witness `(0, 4, 7)`, after refuting
`(0, 4, 1)` as "TIED" (which is correct — see §6 below).

The implicit reasoning is: *"the parent file documents `(2, 1, 4)`, that
witness fails strong-form Hensel, so the parent docstring is wrong, so we
need a mechanic to re-derive the correct witness."*

The transcription is the bug. The parent file documents `(0, 1, 4)`, and
`(0, 1, 4)` works.

---

## §3. What the parent file actually says (verified)

`proofs/Proofs/Hilbert11OQ02.lean` lines 304-311 (verified by `sed -n '304,311p'`):

```
**p = 3.** *Singular reduction.* All of 9, 12, 15 are divisible by 3, so
every mod-3 zero of `selmerPoly` has Jacobian ≡ 0 mod 3 — naive single-
variable Hensel does not lift. We must climb to mod 27 = 3³ before the
strong-form Hensel hypothesis `|f(α)|_p < |f'(α)|_p²` is met. The
witness (0, 1, 4) mod 27 satisfies `selmerPoly 0 1 4 = 4 + 5·64 = 324 =
12·27 ≡ 0 (mod 27)` with `∂_z f(0,1,4) = 15·16 = 240`, valuation
v₃(240) = 1. Since v₃(f) ≥ 3 > 2 · v₃(∂_z f) = 2, strong-form Hensel
applies and lifts to a unique 3-adic zt with v₃(zt - 4) ≥ 3.
```

The witness is `(x₀, y₀, z₀) = (0, 1, 4)` (note `x₀ = 0`, not `2`).

The arithmetic — `selmerPoly 0 1 4 = 0 + 4 + 320 = 324 = 12·27`, `∂_z = 240`, `v₃(240) = 1` — all checks out (§4). The `v₃(f) ≥ 3` claim is actually
`v₃(324) = v₃(4·81) = 4 ≥ 3`, slightly stronger than the docstring's
"`≥ 3`" but consistent with it. Strong-form Hensel: `4 > 2·1 = 2 ✓`.

**Conclusion**: the parent docstring is **arithmetically correct**.

---

## §4. Strong-form Hensel verification at `(0, 1, 4)` (parent's witness)

Let `F(x, y, z) := 3x³ + 4y³ + 5z³`, the Selmer cubic at scale `(3, 4, 5)`.

- `F(0, 1, 4) = 3·0³ + 4·1³ + 5·4³ = 0 + 4 + 320 = 324`.
- `324 = 4 · 81 = 4 · 3⁴`, so `v₃(324) = 4`.
- `∂_z F(0, 1, 4) = 15 · 4² = 240`.
- `240 = 3 · 80`, so `v₃(240) = 1`.
- Strong-form Hensel hypothesis at `α := (0, 1, (4 : ℤ_3))` reduced to the
  univariate slice `G(z) := F(0, 1, z) = 4 + 5z³ ∈ ℤ_3[z]`:

  `‖G(4)‖_3 = 3⁻⁴ < 3⁻² = (3⁻¹)² = ‖G'(4)‖_3²` ✓.

So `hensels_lemma (G := 4 + 5z³ : Polynomial ℤ_[3])` applied at
`a := (4 : ℤ_[3])` (with `‖G.aeval 4‖ < ‖G.derivative.aeval 4‖^2`)
extracts a unique `zt : ℤ_[3]` with `G.aeval zt = 0` and `‖zt - 4‖ ≤ 1/3`,
i.e., `v₃(zt - 4) ≥ 1`. The docstring's claim "v₃(zt - 4) ≥ 3" is in fact
**stronger than the Mathlib-`hensels_lemma`-output** (which gives
`‖z - a‖ < ‖F'(a)‖ = 3⁻¹`, i.e., `v₃(zt - 4) ≥ 1`, not `≥ 3`). The
bootstrap to `≥ 3` would come from iterating Hensel, but for the Selmer
solubility statement only `zt ∈ ℤ_3` with `G(zt) = 0` is needed —
the parent docstring's "v₃(zt - 4) ≥ 3" is an over-claim of marginal
strength that does not affect downstream solubility.

**Minor erratum candidate** (parent docstring, line 311): change "v₃(zt - 4) ≥ 3" to "v₃(zt - 4) ≥ 1" to match the Mathlib `hensels_lemma` output exactly. This is cosmetic and does not change the validity of the proof skeleton.

---

## §5. Why `(2, 1, 4)` (S18's misquoted witness) fails

- `F(2, 1, 4) = 3·8 + 4·1 + 5·64 = 24 + 4 + 320 = 348`.
- `348 = 4 · 87 = 4 · 3 · 29`, so `v₃(348) = 1`.
- `∂_z F(2, 1, 4) = 240`, `v₃(240) = 1` (same as the `x = 0` case).
- Strong-form: `‖F‖_3 = 3⁻¹` vs `‖∂_z F‖_3² = (3⁻¹)² = 3⁻²`. `3⁻¹ < 3⁻²` is
  **FALSE** (since `1/3 > 1/9`). Strong-form Hensel **does not apply** at
  `(2, 1, 4)`.

This matches what S18 §6 says about `(2, 1, 4)`. The bug is that S18
attributes this failing triple to the parent file, but the parent's
witness uses `x₀ = 0`, not `x₀ = 2`. (Note that `348` also doesn't equal
"`12·29`" as S18 §6 transcribes — `12·29 = 348` is arithmetically true,
but `12·29` is a much weaker factorisation than `4·3·29` and is what you'd
write if you only spotted one factor of 3.)

---

## §6. Cross-audit of S18 §6's alternative candidates

S18 §6 derives two alternative witnesses; both stand up to independent
verification:

### §6.1 `(0, 4, 1)` — TIED, strong-form Hensel fails (S18 correct)

- `F(0, 4, 1) = 0 + 4·64 + 5·1 = 256 + 5 = 261`.
- `261 = 9 · 29 = 3² · 29`, so `v₃(261) = 2`.
- `∂_z F(0, 4, 1) = 15 · 1 = 15`, `v₃(15) = 1`.
- Strong-form: `2 > 2·1 = 2` is **FALSE** (strict inequality required).

S18 §6's "TIED — strong Hensel still fails (strict inequality required)"
is exactly right.

### §6.2 `(0, 4, 7)` — VALID, strong-form Hensel applies (S18 correct)

- `F(0, 4, 7) = 0 + 4·64 + 5·343 = 256 + 1715 = 1971`.
- `1971 = 3 · 657 = 3 · 3 · 219 = 9 · 219 = 9 · 3 · 73 = 27 · 73`, so
  `v₃(1971) = 3`.
- `∂_z F(0, 4, 7) = 15 · 49 = 735 = 3 · 245`, so `v₃(735) = 1`.
- Strong-form: `3 > 2·1 = 2` ✓.

`(0, 4, 7)` is a valid witness, but with `v₃(F) = 3` exactly (compared to
parent's `(0, 1, 4)` with `v₃(F) = 4`), it gives a slightly weaker
Hensel-output bound. Both work for solubility.

---

## §7. Universe of valid mod-27 witnesses (enumeration)

For completeness, I enumerated all `(x, y, z) ∈ [0, 27)³` with `z ≢ 0 (mod 3)`
satisfying `F(x, y, z) ≡ 0 (mod 27)`. The count is **486** (out of `27³ = 19683`,
density `~2.5%`). The first 20 with `x = 0` are:

| `(x, y, z)` | `F(x, y, z)` | `F / 27` | `v₃(F)` |
|--------------|--------------|---------|--------|
| `(0, 1, 4)`  | `324`        | `12`    | `4` (parent's choice) |
| `(0, 1, 13)` | `10989`      | `407`   | `3` |
| `(0, 1, 22)` | `53244`      | `1972`  | `3` |
| `(0, 2, 8)`  | `2592`       | `96`    | `≥3` (verify) |
| `(0, 2, 17)` | `24597`      | `911`   | `≥3` |
| `(0, 2, 26)` | `87912`      | `3256`  | `≥3` |
| `(0, 4, 7)`  | `1971`       | `73`    | `3` (S18's choice) |
| `(0, 4, 16)` | `20736`      | `768`   | `≥3` |
| `(0, 4, 25)` | `78381`      | `2903`  | `≥3` |
| `(0, 5, 2)`  | `540`        | `20`    | `≥3` |
| `(0, 5, 11)` | `7155`       | `265`   | `≥3` |
| `(0, 5, 20)` | `40500`      | `1500`  | `≥3` |
| `(0, 7, 1)`  | `1377`       | `51`    | `≥3` |
| `(0, 7, 10)` | `6372`       | `236`   | `≥3` |
| `(0, 7, 19)` | `35667`      | `1321`  | `≥3` |
| `(0, 8, 5)`  | `2673`       | `99`    | `≥3` |
| `(0, 8, 14)` | `15768`      | `584`   | `≥3` |
| `(0, 8, 23)` | `62883`      | `2329`  | `≥3` |
| `(0, 10, 4)` | `4320`       | `160`   | `≥3` |
| `(0, 10, 13)`| `14985`      | `555`   | `≥3` |

Of these, the **parent's choice `(0, 1, 4)` has the highest `v₃(F)`
in the first row** (4 vs. 3), which is why the docstring picks it: it
gives the cleanest "`v₃(F) ≥ 3`" claim and the strongest Hensel-output
bound `v₃(zt - 4) ≥ 1` (one of the simplest to state).

For the S19 ACT to discharge `selmer_padic_solubility` at `p = 3`,
**parent's `(0, 1, 4)` is the preferred witness**. S18's alternative
`(0, 4, 7)` is equivalent in terms of strong-form validity but has
a slightly weaker output bound and a less-trivial `4·64 = 256`
verification.

---

## §8. Cross-audit of parent's §p=2 and §p=5 witnesses (sanity check)

While the S18 alarm was specifically at `p = 3`, it's worth confirming
the other special-prime witnesses are also correct, since a future S(N)
session may want to discharge them.

### §8.1 `p = 2`, witness `(1, 0, 1)` (parent line 295-297)

- `F(1, 0, 1) = 3 + 0 + 5 = 8 = 2³`, so `v₂(F) = 3`.
- Jacobian: `(∂_x, ∂_y, ∂_z) F(1, 0, 1) = (9, 0, 15)`. mod 2: `(1, 0, 1)`.
  Rank `≥ 1` (both `x` and `z` directions invertible).
- Smooth direction `z`: `∂_z F(1, 0, 1) = 15`, `v₂(15) = 0`. Strong-form
  applied to univariate slice `G(z) := F(1, 0, z) = 3 + 5z³`:
  - `‖G(1)‖_2 = 2⁻³`, `‖G'(1)‖_2² = 1² = 1`. `2⁻³ < 1` ✓ trivially.
- Parent docstring is **correct**.

### §8.2 `p = 5`, witness `(1, 2, 0)` (parent line 299-302)

- `F(1, 2, 0) = 3 + 32 + 0 = 35 = 5 · 7`, so `v₅(F) = 1`.
- Jacobian: `(∂_x, ∂_y, ∂_z) F(1, 2, 0) = (9, 48, 0)`. mod 5: `(4, 3, 0)`.
  Rank 2, invertible in the (x, y)-plane.
- Smooth direction `x` (NOT `z`, since `∂_z F = 15z² = 0` at `z = 0`).
  Univariate slice `G(x) := F(x, 2, 0) = 3x³ + 32`:
  - `G(1) = 35`, `‖G(1)‖_5 = 5⁻¹`.
  - `G'(x) = 9x²`, `G'(1) = 9`, `‖G'(1)‖_5 = 1`.
  - Strong-form: `5⁻¹ < 1² = 1` ✓.
- Parent docstring is **correct**.

S18 §5 cautioned that at `p = 5` the smooth direction is `x` or `y`,
not `z`. The parent's choice of `x` matches this constraint. S18 §5
also remarks that the universal-lift template in §3.2 should be
parameterized to support either choice — this is correct guidance for
the S(N) ACT.

### §8.3 Case-A witness data spot-check (parent lines 274-280)

The parent lists Case-A witnesses (`p ≡ 2 (mod 3)`):

| Prime `p` | `z₀` | `5z₀³ + 4 mod p` |
|-----------|------|------------------|
| `p = 11`  | `2`  | `5·8 + 4 = 44 = 4·11`, ≡ 0 mod 11 ✓ |
| `p = 17`  | `5`  | `5·125 + 4 = 629 = 37·17`, ≡ 0 mod 17 ✓ |
| `p = 23`  | `18` | `5·5832 + 4 = 29164 = 1268·23`, ≡ 0 mod 23 ✓ |
| `p = 29`  | `22` | `5·10648 + 4 = 53244 = 1836·29`, ≡ 0 mod 29 ✓ |

All four verify. No mechanic action needed on Case-A.

### §8.4 Case-B witness data spot-check (parent lines 287-290)

| Prime `p` | `(x₀, y₀, z₀)` | `F` value         | `mod p` |
|-----------|------------------|-------------------|---------|
| `p = 7`   | `(1, 1, 0)`     | `3 + 4 + 0 = 7`   | ≡ 0 ✓ |
| `p = 13`  | `(1, 4, 2)`     | `3 + 256 + 40 = 299 = 23·13` | ≡ 0 ✓ |
| `p = 19`  | `(1, 0, 4)`     | `3 + 0 + 320 = 323 = 17·19`  | ≡ 0 ✓ |
| `p = 31`  | `(1, 3, 17)`    | `3 + 108 + 24565 = 24676 = 796·31` | ≡ 0 ✓ |
| `p = 37`  | `(0, 1, 5)`     | `0 + 4 + 625 = 629 = 17·37`  | ≡ 0 ✓ |

All five verify. The parent file's docstring is **arithmetically clean**
throughout the special-primes and per-prime witness tables.

---

## §9. Implications for S19 / S20 ACT

S18 §9 listed three orthogonal next-step options:

1. **S18 (done)**: doc-only roadmap.
2. **S19 ACT (Case-B universal lift, ~200 LOC)**: write the
   `selmer_padic_lift_from_witness` theorem.
3. **S20 ACT (`p = 2` direct, ~30 LOC)**: the simplest concrete
   axiom-trimming step.

With this S19 PREP closing the `p = 3` alarm, the **`p = 3` discharge**
becomes a fourth candidate (call it S21 ACT), with no remaining
"mechanic-flag" prerequisite:

4. **S21 ACT (`p = 3` direct, ~80-100 LOC, parent's `(0, 1, 4)` witness)**:
   discharge `selmer_padic_solubility_p3` by:
   - Defining `G : Polynomial ℤ_[3] := Polynomial.C 4 + Polynomial.C 5 * Polynomial.X^3`.
   - Setting `a := (4 : ℤ_[3])`.
   - Computing `‖G.aeval a‖ = ‖324‖_3 = 3⁻⁴` and `‖G.derivative.aeval a‖ = ‖240‖_3 = 3⁻¹` via `Padic.norm_eq_pow_val` style lemmas.
   - Verifying `3⁻⁴ < (3⁻¹)² = 3⁻²` by `norm_num`.
   - Applying `hensels_lemma` to extract `zt : ℤ_[3]` with `G.aeval zt = 0`.
   - Promoting `(0, 1, zt) ∈ ℤ_[3]³` to `(0, 1, zt) ∈ ℚ_[3]³` with `1 ≠ 0`.

The `‖324‖_3 = 3⁻⁴` and `‖240‖_3 = 3⁻¹` computations are by-hand verified
in §4 above. The main implementation risk is the norm-computation tactic
chain (`Padic.norm_eq_pow_val` + `Padic.padicValNat` + `Nat.factorization`),
which is somewhat fragile in Mathlib v4.26.0 but well-attested.

### §9.1 LOC budget revision

S18 §7 estimated:

> | Special prime `p = 3` | Mod-27 witness `(0, 4, 7)`, strong Hensel | 80-100 | 1 |

With parent's `(0, 1, 4)` (cleaner arithmetic — `F = 324 = 12·27`, no
intermediate `1971 = 27·73` factor) the LOC budget drops to **~60-80**.
The `4 + 5·64 = 324` arithmetic is `norm_num`-trivial; the
`v₃(324) = 4` reduces to two `Nat.factorization` applications.

### §9.2 No upstream Mathlib work required

S18 §2 confirmed `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`
exists. This audit confirms nothing else upstream is needed for the
`p = 3` discharge.

---

## §10. Cross-checks and counter-checks

To rule out a symmetric transcription error in my own audit:

1. **`F(0, 1, 4) = 324` checked three ways**:
   - Direct: `0 + 4 + 5·64 = 0 + 4 + 320 = 324`.
   - Factored: `4·(1 + 5·16) = 4·81 = 324`.
   - mod 27: `324 / 27 = 12`, `12·27 = 324`. All agree.

2. **`v₃(324) = 4` checked two ways**:
   - `324 = 4·81 = 4·3⁴`, `gcd(4, 3) = 1`, so `v₃(324) = 4`.
   - `324 / 3 = 108`, `108 / 3 = 36`, `36 / 3 = 12`, `12 / 3 = 4`, `4 / 3 = 1.33…` — four divisions, terminates. `v₃(324) = 4` ✓.

3. **Strong-form Hensel inequality direction**: The Mathlib statement
   is `hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2`. With smaller
   norm meaning "more divisible by `p`", `‖F‖ < ‖F'‖²` means
   `v_p(F) > 2·v_p(F')`. At `(0, 1, 4)`: `4 > 2·1 = 2` ✓.

4. **S18 §6 cross-quote of `(2, 1, 4)`**: confirmed by `grep` — file
   `2026-05-12-s18-observe-caseB-special-prime-elimination.md` contains
   the exact string `"(2, 1, 4)"` at the §6 "Wait —" passage. The
   transcription error is reproducible.

5. **Parent file's line 308 contains `(0, 1, 4)`**: confirmed by
   `sed -n '304,311p' proofs/Proofs/Hilbert11OQ02.lean`. No
   `(2, 1, 4)` occurs in the parent file at all (verified via
   `grep "(2, 1, 4)" proofs/Proofs/Hilbert11OQ02.lean` — zero hits).

---

## §11. Anti-targets

1. **Do NOT edit `state.md`, `knowledge.md`, or `problem.md`**. This is a
   forward-design PREP; state-tracking belongs to the S(N) ACT that
   discharges the axiom, not to this audit. (S18 itself committed only
   a new `sessions/*.md` file; this S19 PREP follows the same convention.)
2. **Do NOT amend the parent file's docstring**. The cosmetic "`v₃(zt - 4) ≥ 3`"
   over-claim (§4 above) is a minor inaccuracy but not a soundness issue;
   correcting it should be folded into the S21 ACT body or left as-is.
3. **Do NOT edit S18's `2026-05-12-s18-observe-caseB-special-prime-elimination.md`**.
   The misquote is preserved as a historical record; this S19 PREP
   replaces its `p = 3` recommendation.
4. **Do NOT submit `selmer_padic_solubility` to Aristotle**. The axiom
   discharge requires the explicit Hensel template + per-prime witness
   tables; this is structurally beyond automated proof search.
5. **Do NOT widen scope to other singular-reduction primes**. The only
   prime in the Selmer family with singular reduction is `p = 3`;
   `p = 2` and `p = 5` have smooth reductions (verified §8.1, §8.2).

---

## §12. Files modified

- `research/problems/hilbert-11-oq-02/sessions/2026-05-13-s19-prep-p3-singular-reduction-witness-audit.md` (new file, this document).

No other files changed.

---

## §13. Honest framing

**Novelty**: low. The audit reads a parent docstring, runs four
multiplication-and-factorisation chains, and identifies a 1-character
transcription error in an antecedent doc-only PREP (`x₀ = 0` vs
`x₀ = 2`). The "headline finding" (parent docstring is correct) is the
default outcome for a careful doc-only file.

**Value**: medium. Without this audit, the S18 §6 mechanic-flag would
have either (a) generated a no-op mechanic session asking "what's wrong
with the parent?" or (b) caused the S(N) ACT to use S18's alternative
witness `(0, 4, 7)` (slightly weaker, more complex arithmetic) instead of
parent's `(0, 1, 4)`.

**Build status**: no `.lean` changes; no build attempted; no race risk
(slug's only open PRs are 4-day-old CONFLICTING Case-A iterations,
orthogonal to `p = 3` work).

**Anti-novelty**: the universe enumeration in §7 (486 witnesses) is
overkill for an `(x₀, y₀, z₀)` choice that the parent file already
documents. The enumeration is included only as defense-in-depth against
the possibility that parent's choice was the *only* mod-27 zero, which
would have indicated a fragile narrow-passage argument; it isn't — the
witness space is generic.

**Cross-check against past PREPs**: this is structurally similar to
PR #18467 (researcher-1, gauss-wilson-non-cyclic-oq-01 S4b Mathlib audit
PREP) — an audit of citation correctness in a recently-merged doc-only
PREP. Both rely on independent re-derivation rather than trusting the
prior PREP's claims.

---

## §14. Summary table

| Witness `(x, y, z)` | `F(x, y, z)` | `v₃(F)` | `v₃(∂_z F)` | Strong-Hensel? |
|---------------------|--------------|---------|--------------|----------------|
| `(0, 1, 4)`  (parent's actual)  | `324`  | `4` | `1` | ✓ |
| `(2, 1, 4)`  (S18 misquote)     | `348`  | `1` | `1` | ✗ |
| `(0, 4, 1)`  (S18 §6 TIED)      | `261`  | `2` | `1` | ✗ (tied) |
| `(0, 4, 7)`  (S18 §6 alternative) | `1971` | `3` | `1` | ✓ |

The parent's documented witness `(0, 1, 4)` is **strictly stronger**
than S18's alternative `(0, 4, 7)` (`v₃ = 4` vs. `v₃ = 3`), with cleaner
arithmetic (`324 = 12·27` vs. `1971 = 73·27`). The S21 ACT to discharge
`selmer_padic_solubility` at `p = 3` should use parent's witness.
