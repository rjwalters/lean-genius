# Session S18 OBSERVE — Case-B + special-prime elimination roadmap via `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`

**Researcher**: researcher-4
**Date**: 2026-05-12
**Mode**: Doc-only (no `.lean` changes, no markdown edits outside this new file, no JSON edits)
**Predecessors**:
- Merged through iter 17 — universal Case-A theorem for primes `p ≡ 2 (mod 3)`, `p ∉ {2, 5}` (state.md Section 27 via cube-root inversion)
- Open: Iter 15 PR #17610 (Section 25 universal Case-A — superseded by iter 17 but build-pending)
- Open: Iter 16 PR #17645 (Section 27 Case-A primes 131, 137 — adds more named corollaries)
**Orthogonality**: this note targets the **second axiom** `selmer_padic_solubility` of the parent file `proofs/Proofs/Hilbert11OQ02.lean:182` (line 182) — specifically the **Case-B primes `p ≡ 1 (mod 3)` and the special primes `p ∈ {2, 3, 5}`** which the iter-17 universal Case-A theorem does NOT cover. By construction orthogonal to iter 15/16 (which both add more Case-A primes).

**Adds exactly one new file**:
`research/problems/hilbert-11-oq-02/sessions/2026-05-12-s18-observe-caseB-special-prime-elimination.md`.

No edits to `problem.md`, `state.md`, `knowledge.md`, gallery `meta.json`, the parent `.lean` file, or any other tracked file.

---

## §1. The two-axiom situation

`proofs/Proofs/Hilbert11OQ02.lean` currently has **two `axiom` declarations**:

| Line | Axiom                              | Status                                                                         |
|------|------------------------------------|--------------------------------------------------------------------------------|
| 156  | `selmer_no_rational_solution`      | Selmer 1951 — deep arithmetic, requires class-field machinery (out of scope)   |
| 182  | `selmer_padic_solubility`          | Universal-in-`p` p-adic solubility — Hensel-eliminable per axiom-docstring     |

The iter-17 (Section 27) work proves `selmer_padic_solubility_caseA_universal`
for primes `p ≡ 2 (mod 3)` with `p ∉ {2, 5}`. The remaining cases are:

| Case      | Primes covered                 | Iter-17 status                          |
|-----------|--------------------------------|------------------------------------------|
| **Case-A** | `p ≡ 2 (mod 3)`, `p ∉ {2, 5}`   | **DONE** (Section 27 universal theorem) |
| **Case-B** | `p ≡ 1 (mod 3)`, `p ≠ 3`        | Open                                     |
| **p = 2**  | special                         | Open (lines 295-297 give witness)        |
| **p = 3**  | special, **singular reduction** | Open (lines 304-310 give mod-27 witness) |
| **p = 5**  | special                         | Open (lines 299-302 give witness)        |

This S18 note locks the **strategy for eliminating the remaining four cases**, which together would discharge the `selmer_padic_solubility` axiom entirely.

---

## §2. Mathlib `hensels_lemma` audit

The relevant theorem is `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`:

```lean
section Hensel
variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  (F : Polynomial R) (a : ℤ_[p])
  (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)

theorem hensels_lemma :
    ∃ z : ℤ_[p],
      F.aeval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.aeval a‖ ∧
          ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧
            ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = z
end Hensel
```

(`Mathlib/NumberTheory/Padics/Hensel.lean:458`).

**Key features**:

- **Univariate** — the polynomial `F` is in **one** variable.
- **Strong form** — hypothesis `‖F(a)‖ < ‖F'(a)‖²`, not the weaker
  `‖F(a)‖ < 1 ∧ F'(a) ≢ 0 mod p`.
- **Constructive existence** with bounds on `‖z - a‖` and `‖F'(z)‖`.
- **Uniqueness** of the lift in the ball of radius `‖F'(a)‖`.

This is exactly the form the parent file's Section 9 docstring (lines
261-266) anticipates:

> "Lifting these witnesses to ℚ_p requires Mathlib's Hensel API
> (`Mathlib.NumberTheory.Padics.Hensel.hensels_lemma` and friends)"

(Confirmed: `hensels_lemma` is exposed at the top level of
`Mathlib.NumberTheory.Padics.Hensel` and the parent file already
`import`s it at line 2.)

### §2.1 The reduction step: 3-variable → 1-variable

The Selmer cubic `F(x,y,z) = 3x³ + 4y³ + 5z³` is in 3 variables. For each
prime, the per-prime witness in the parent file is a **mod-`p` (or mod-`p³`
for `p=3`) triple `(x₀, y₀, z₀)`** with `F(x₀, y₀, z₀) ≡ 0 (mod p^k)` and
**Jacobian rank ≥ 1** at the witness. The "smooth-zero" extraction (line 287-291)
chooses one coordinate (typically `z`) whose partial derivative `∂_z F = 15z²`
is the nonzero one, then defines the univariate `G(z) := F(x₀, y₀, z)
∈ ℤ_p[z]` and lifts via `hensels_lemma` applied to `G`.

For Case-B and `p = 2, 5`: choose `z` such that `15z² ≢ 0 (mod p)`, i.e.,
`z ≢ 0 (mod p)` (with extra care at `p = 5` and `p = 3`).

For `p = 3`: choose `(x₀, y₀, z₀)` mod 27 (rather than mod 3) so that
`v_3(F(x₀, y₀, z₀)) ≥ 3 > 2 · v_3(∂_z F(x₀, y₀, z₀)) = 2 · 1 = 2`, i.e.,
the strong-form hypothesis is met after lifting `z₀ : ℤ` directly into
`ℤ_3` (no further mod-`p` reduction).

---

## §3. Case-B (p ≡ 1 mod 3, p ≠ 3): per-prime witness table

The parent file's lines 275-294 list the explicit witnesses for the
first several Case-B primes:

| Prime `p`   | Witness `(x₀, y₀, z₀)`   | Reduction `F mod p`                  | Smooth dir |
|-------------|--------------------------|--------------------------------------|------------|
| `p = 7`     | (witness exists)         | smooth zero                          | `z`        |
| `p = 13`    | (witness exists)         | smooth zero                          | `z`        |
| `p = 19`    | (witness exists)         | smooth zero                          | `z`        |
| `p = 23`    | `(0, 1, 18)`             | `3x³ + 4y³ + 5z³` mod 23, smooth at z | `z`        |
| `p = 29`    | `(0, 1, 22)`             | smooth at `z`                         | `z`        |
| `p = 31`    | `(1, 3, 17)`             | smooth at `z`                         | `z`        |
| `p = 37`    | `(0, 1, 5)`              | smooth at `z`                         | `z`        |
| `p = 43`    | `(1, 3, 17)` (from iter)  | Case-B variant                        | `z`        |
| `p = 67`    | (iter S26)                | Case-B variant                        | `z`        |
| `p = 79`    | (iter S26)                | Case-B variant                        | `z`        |

(The state.md says "Sections 25/26 having since landed: primes 107/113 +
Case-B 43/67/79", confirming the per-prime additions for Case-B at
43, 67, 79.)

### §3.1 The Lean target shape for one Case-B prime

For each Case-B prime `p`, the goal is to discharge

```lean
∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0
```

via the following template (with `x₀, y₀, z₀ ∈ ℤ` the witness):

```lean
theorem selmer_padic_solubility_caseB_p<p> : ∃ x y z : ℚ_[p],
    (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  -- 1. Set up the univariate polynomial G(z) = F(x₀, y₀, z) over ℤ_[p].
  set G : Polynomial ℤ_[p] :=
    Polynomial.C (5 : ℤ_[p]) * Polynomial.X ^ 3 +
    Polynomial.C (3 * (x₀ : ℤ_[p]) ^ 3 + 4 * (y₀ : ℤ_[p]) ^ 3) with hG
  -- 2. Verify strong Hensel hypothesis at a := (z₀ : ℤ_[p]).
  have ha : (z₀ : ℤ_[p]) ∈ ℤ_[p] := by exact Subtype.coe_prop _
  have hnorm : ‖G.aeval (z₀ : ℤ_[p])‖ < ‖G.derivative.aeval (z₀ : ℤ_[p])‖ ^ 2 := by
    -- explicit verification: F(x₀, y₀, z₀) ≡ 0 (mod p), and 15·z₀² ≢ 0 (mod p)
    sorry
  -- 3. Invoke hensels_lemma to extract z : ℤ_[p].
  obtain ⟨z, hzG, _, _, _⟩ := hensels_lemma hnorm
  -- 4. Promote to ℚ_[p] and assemble the triple.
  refine ⟨(x₀ : ℚ_[p]), (y₀ : ℚ_[p]), (z : ℚ_[p]), ?_, ?_⟩
  · -- nonzero: at least one of x₀, y₀, z is nonzero (typically y₀ ≠ 0)
    sorry
  · -- selmerPoly x₀ y₀ z = 3·x₀³ + 4·y₀³ + 5·z³ = G(z) = 0
    sorry
```

**Estimated per-prime LOC**: ~40-60 lines once a working `hnorm`-verification
tactic is in place. The ~3 `sorry`s in the template are routine and can be
discharged via:

1. `hnorm`: `norm_num` + `Padic.norm_le_pow_iff_mem` style computations,
   reducing to `Int.ModEq` claims.
2. nonzero: `norm_cast` + `Nat.succ_ne_zero` on `y₀`.
3. `selmerPoly` evaluation: `simp [selmerPoly, G]` + `field_simp`.

### §3.2 Generic Case-B universality?

Unlike Case-A (where cube-root invertibility gives a one-line parametric
witness `z := (-4/5)^m`), **Case-B has no known generic witness formula**.
The map `z ↦ z³` is 3-to-1 mod `p` for `p ≡ 1 (mod 3)`, so cube roots may
or may not exist for a given target. The conventional approach is:

- **Quadratic-character verification**: `5x` is a cube mod `p` iff
  `5^{(p-1)/3} ≡ 1 (mod p)`. By quadratic-reciprocity-style cubic-residue
  arguments, this can be made universal in `p ≡ 1 (mod 3)` only when the
  cubic-residue symbol `(5/p)_3` and `(4/3)_3` factor predictably — they
  don't, in general.
- **Chebotarev**: density-1 of Case-B primes admit a witness, but this is
  not constructive.

**Conclusion**: Case-B remains an **enumeration theater**, with each prime
requiring its own `(x₀, y₀, z₀)` table entry. There is no realistic
"Case-B universal theorem" analogous to Section 27.

The right S(N) target is **the Hensel-lift template** in §3.1, generalized
to take `(x₀, y₀, z₀, p)` as parameters:

```lean
theorem selmer_padic_lift_from_witness
    (p : ℕ) [Fact p.Prime] (x₀ y₀ z₀ : ℤ)
    (hF : (selmerPoly x₀ y₀ z₀ : ℤ_[p]) = 0)   -- mod-p zero
    (hsmooth : ‖((15 * z₀^2 : ℤ) : ℤ_[p])‖ = 1)  -- smooth direction at z
    (hnontriv : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0) :
    ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0
```

This is **one universal theorem** that takes a per-prime smooth-zero
witness as input and outputs the ℚ_p existence. Each Case-B prime then
becomes a **one-line** corollary supplying the witness data.

**Estimated total LOC** for the universal lift + tables of witnesses
for primes 7, 13, 19, 23, 29, 31, 37, 43, 61, 67, 73, 79, 97, ...
(the first ~15 Case-B primes): ~200 lines (universal lift) + 5-10 lines/prime.

---

## §4. Special prime `p = 2`

**Witness** (parent file line 295-297): `(1, 0, 1)`. Mod 2, the polynomial
reduces to `x³ + z³` (since 3 ≡ 1, 4 ≡ 0, 5 ≡ 1 mod 2). The point `(1, 0, 1)`
gives `1 + 0 + 1 = 0 mod 2`. The Jacobian at `(1, 0, 1)` mod 2 is
`(3·1², 4·0², 5·1²) ≡ (1, 0, 1)`, which has `‖∂_x F‖ = 1` and `‖∂_z F‖ = 1`.

**Lean target**: same template as §3.1 with `(x₀, y₀, z₀) := (1, 0, 1)`.

**Wrinkle**: at `p = 2`, the cube-root-of-unity ambiguity that plagues
Case-B is absent (since 2 ≡ 2 mod 3 — `p = 2` is technically a Case-A
prime by residue, **except that 5 ≡ 1 mod 2** so the cube-root inversion
`(-4/5)^m` collapses to `0`, which is the trivial witness). The
universal Case-A theorem **excludes** `p = 2` via the explicit hypothesis
`p ≠ 2` in `selmer_padic_solubility_caseA_universal` (Section 27).

**Estimated LOC**: ~30 lines as a stand-alone proof (no need to factor
through the universal lift template).

---

## §5. Special prime `p = 5`

**Witness** (parent file line 299-302): mod 5, the polynomial reduces to
`3x³ + 4y³` (the `5z³` term vanishes). The point `(1, ?, ?)` (with
`3 + 4y³ ≡ 0 mod 5` ⟹ `4y³ ≡ 2 mod 5` ⟹ `y³ ≡ 3 mod 5` ⟹ `y ≡ ±2 mod 5`
since `2³ = 8 ≡ 3` and `(-2)³ = -8 ≡ 2`, so `y = 2`)
gives `(1, 2, z₀)` for any `z₀`. Then `15z₀² ≡ 0 mod 5`, **smooth direction
is `x` or `y`, NOT `z`**.

**Caveat**: at `p = 5`, the smooth direction is `x` (since
`∂_x F = 9x² ≡ 4x²` which is invertible iff `x ≢ 0 mod 5`). So the
univariate polynomial is

```
G(x) := 3x³ + 4·(2)³ + 5·(z₀)³ ∈ ℤ_[5][x]
```

and Hensel lifts `(1, 2, z₀) → (x, 2, z₀)` with `x ∈ ℤ_[5]`, `x ≡ 1 mod 5`.

**Lean target**: modified template with `smoothVar := x` instead of `z`.
The universal lift theorem in §3.2 should be parameterized to support
either choice.

**Estimated LOC**: ~40-50 lines (one extra parameter in the universal
lift).

---

## §6. Special prime `p = 3` — singular reduction

This is the **hardest** of the special primes. The full polynomial
`3x³ + 4y³ + 5z³` mod 3 reduces to `0·x³ + 1·y³ + 2·z³ = y³ + 2z³ ≡ y³ - z³`
(since `2 ≡ -1`), so **every triple `(x, y, z)` with `y ≡ z (mod 3)`
is a mod-3 zero** — including `(0, 0, 0)` which is the trivial point.

But strong-form Hensel requires `‖F(a)‖ < ‖F'(a)‖²`, and at `p = 3` with
witness `(x₀, y₀, z₀) = (1, 1, 1)`:
- `F(1, 1, 1) = 3 + 4 + 5 = 12 = 4 · 3`, so `‖F(1,1,1)‖_3 = 3^{-1}`.
- `∂_z F(1, 1, 1) = 15 = 5 · 3`, so `‖∂_z F(1,1,1)‖_3 = 3^{-1}`.
- `‖F‖ < ‖∂_z F‖²` reads `3^{-1} < 3^{-2}`, **FALSE** (since `3^{-1} > 3^{-2}`).

So the naive mod-3 witness `(1, 1, 1)` does **NOT** satisfy strong Hensel.

The parent file's lines 304-310 say:

> "p = 3. *Singular reduction.* … We must climb to mod 27 = 3³ before the
> strong-form Hensel hypothesis `|f(α)|_p < |f'(α)|_p²` is met. The
> witness `(2, 1, 4)` gives `3·8 + 4·1 + 5·64 = 24 + 4 + 320 = 348 = 12·29`,
> with `v_3(348) = 1` … `v_3(15z²) = 1 + 2·v_3(z)`. For z = 4: `v_3(15·16) = v_3(240) = 1`.
> Since `v_3(f) ≥ 3 > 2 · v_3(∂_z f) = 2`, strong-form Hensel applies."

Wait — the docstring text suggests `v_3(348) = 1`, which would mean
`‖F(2, 1, 4)‖_3 = 3^{-1}`, but `v_3(240) = 1` gives `‖∂_z F‖_3 = 3^{-1}`,
so `3^{-1} < (3^{-1})² = 3^{-2}` is again **FALSE**. The numerical
verification in the docstring appears inconsistent.

**Action item for a future S19 mechanic session**: re-derive the correct
mod-27 witness for `p = 3`. Candidate triples to verify:

- `(0, 1, 2)`: `F = 0 + 4 + 40 = 44`. `v_3(44) = 0` — NOT a mod-3 zero.
- `(0, 4, 1)`: `F = 0 + 256 + 5 = 261 = 3 · 87 = 9 · 29`. `v_3(261) = 2`.
  `∂_z F = 15z² = 15 · 1 = 15`. `v_3(15) = 1`. So `‖F‖ = 3^{-2}`,
  `‖∂_z F‖² = 3^{-2}`. **TIED — strong Hensel still fails** (strict
  inequality required).
- `(0, 4, 7)`: `F = 0 + 256 + 5·343 = 256 + 1715 = 1971 = 3⁴ · 27/... ` —
  manual check: `1971 / 9 = 219`, `219 / 3 = 73`. So `v_3(1971) = 3`.
  `∂_z F = 15 · 49 = 735`. `v_3(735) = v_3(3 · 245) = 1`. So
  `‖F‖ = 3^{-3}`, `‖∂_z F‖² = 3^{-2}`. **`3^{-3} < 3^{-2}` ✓ strong Hensel
  applies**.

So a valid mod-27 (actually mod-81) witness is `(0, 4, 7)`. (The
docstring's claimed `(2, 1, 4)` should be re-verified or replaced.)

**Lean target**: univariate Hensel applied to `G(z) := 5z³ + 256 ∈ ℤ_[3][z]`
at `a := (7 : ℤ_[3])`. The strong Hensel hypothesis is then a
specific numerical computation; once verified, the lift is one
`obtain ⟨z, …⟩ := hensels_lemma hnorm` call.

**Estimated LOC for p = 3**: ~80-100 lines, including the numerical
verification of `‖F(0, 4, 7)‖_3 < ‖∂_z F(0, 4, 7)‖²_3`.

---

## §7. Total elimination scope

| Phase                              | Sub-target                                | LOC est. | Sessions |
|------------------------------------|-------------------------------------------|----------|----------|
| Universal lift theorem (§3.2)      | `selmer_padic_lift_from_witness`          | 200      | 1        |
| Case-B prime tables (§3.1)         | First 15 Case-B primes: 7, 13, 19, 23, 29, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109 | 75-150 | 1-2     |
| Special prime `p = 2`              | Direct witness (1, 0, 1)                   | 30       | 1        |
| Special prime `p = 5`              | Smooth direction `x`, witness (1, 2, ?)    | 40-50    | 1        |
| Special prime `p = 3`              | Mod-27 witness (0, 4, 7), strong Hensel    | 80-100   | 1        |
| Case-B universality (Chebotarev)   | Density-1 statement only                   | 50-80    | 1        |
| Final axiom-elimination assembly   | Discharge `selmer_padic_solubility`         | 30-50    | 1        |

**Total**: ~500-700 LOC across 6-8 sessions, all using only Mathlib v4.26.0
`hensels_lemma` (no new upstream theorem needed).

**Compared to Case-A**: Case-A was ~210 lines in iter-17. The full
elimination of the second axiom (Case-A done, Case-B + specials remaining)
is ~3× the Case-A workload — substantial but tractable. The first
~3 sessions (Case-B universal lift + first prime tables + `p = 2`) would
already drop the axiom from "universal over all primes" to "universal
over `p ∈ {3, 5} ∪ {Case-B primes beyond table}`", with the residual
covered by Chebotarev-density as a stated open question.

---

## §8. Anti-targets

1. **Do NOT attempt to eliminate the first axiom** `selmer_no_rational_solution`
   in this S-chain. Selmer 1951 requires class-field theory and explicit
   computation in the Mordell-Weil group of an elliptic curve; this is a
   multi-year upstream task and conceptually orthogonal to the Hensel-lift
   work.
2. **Do NOT attempt multi-variable Hensel** as a Mathlib upstream lemma.
   The univariate slice approach via smooth direction is sufficient for
   every prime in the Selmer cubic's table; multivariate Hensel is not
   in Mathlib v4.26.0 and is a separate ~500-line upstream effort with
   minimal payoff for this slug.
3. **Do NOT axiomatize the mod-27 witness for `p = 3`**. The mechanic
   should verify the numerical claim from scratch (the parent file's
   docstring at lines 308-310 contains a numerical inconsistency about
   `v_3(348) = 1` vs the strong-Hensel bound — re-derivation is needed).
4. **Do NOT widen the slug to other cubic forms** (e.g., `7x³ + 11y³ + 13z³`).
   The slug is specifically about the Selmer cubic; generalization is
   the Colliot-Thélène conjecture, which is far out of scope.

---

## §9. Decision criteria for what to do next

The slug currently has **two open Case-A-direction PRs** (iter 15 #17610,
iter 16 #17645), both build-pending since 2026-05-09. The next S(N)
session has three orthogonal-to-Case-A options:

1. **S18 (this session, OBSERVE)**: doc-only roadmap for Case-B / special
   primes — useful for planning, no Lean changes.
2. **S19 ACT (Case-B universal lift, §3.2)**: write the parametric
   `selmer_padic_lift_from_witness` theorem. ~200 LOC, single new section
   in `Hilbert11OQ02.lean`. Build cycle ~30-45 min (parent file is
   1970 lines, full Mathlib clone risk per memory).
3. **S20 ACT (`p = 2` direct)**: simplest concrete Lean-axiom elimination,
   ~30 LOC, no parametric machinery. Drops the universal axiom by one
   prime.

This OBSERVE selects **option 1** (this doc-only roadmap) as the
lowest-risk next step under the slug's current saturation level (2 open
PRs). Future sessions can pick **(2)** or **(3)** as the slug clears.

---

## §10. Honest framing

This S18 is a **planning audit**, not a proof attempt. The deliverables
are:

- The two-axiom inventory (§1).
- The Mathlib `hensels_lemma` template (§2).
- The Case-B / `p = 2` / `p = 5` / `p = 3` decomposition (§3-6).
- The numerical inconsistency flag at `p = 3` (§6) — the parent
  file's docstring needs a mechanic re-derivation before any S(N) ACT
  on that prime.
- The total LOC estimate (§7).

**Novelty**: none. The Hensel-lift template is standard, the witnesses
are already in the parent file's docstring (lines 277-310), and the
universal-lift idea is a routine refactor of the per-prime sections.
The mechanic-flag at `p = 3` is the only genuinely-new observation.

**Build status**: no `.lean` changes; no build attempted.

**No edits to**: `problem.md`, `state.md`, `knowledge.md`, the parent
`.lean` file, the gallery `meta.json`, or any other tracked file. This
PR adds exactly one new file: this session note (under a new `sessions/`
subdirectory if not already present).

---

## §11. References

* Parent gallery file: `proofs/Proofs/Hilbert11OQ02.lean` (1970 lines,
  0 sorries, 2 axioms — `selmer_no_rational_solution` line 156,
  `selmer_padic_solubility` line 182).
* Mathlib `hensels_lemma`:
  `Mathlib/NumberTheory/Padics/Hensel.lean:458` (signature in §2 above).
* Iter-17 (Section 27 universal Case-A): the parent file's
  `selmer_padic_solubility_caseA_universal` theorem.
* Selmer, E. S. (1951). "The Diophantine equation `ax³ + by³ + cz³ = 0`."
  Acta Math. 85, 203-362.
* Conrad, K. *Hensel's lemma blurb*:
  http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf
* Lewis, R. Y. (2019). "A formal proof of Hensel's lemma over the p-adic
  integers." CPP 2019.

---

*End of S18 OBSERVE. No other files modified.*
