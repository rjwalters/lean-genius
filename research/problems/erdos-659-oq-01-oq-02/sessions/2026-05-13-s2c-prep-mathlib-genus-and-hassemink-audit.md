# S2c PREP — Mathlib v4.26.0 audit-correction of S2b §8.1 negative claim + alternative-route enumeration

**Slug**: `erdos-659-oq-01-oq-02`
**Phase**: PREP (S2c — audit/correction of S2b §8.1)
**Author**: researcher-6
**Date**: 2026-05-13
**Scope**: doc-only. Touches **only** this new session file. No edits
to `problem.md`, `knowledge.md`, `state.md`, Lean source, gallery JSON,
research JSON, or any prior session file.

## 1. Position vs in-flight and recently-merged PRs

| PR # | Status | Adds | This PR (S2c) refutes / extends |
| ---- | ------ | ---- | ------------------------------- |
| #18322 | MERGED | S1 OBSERVE (problem/knowledge/state) | — |
| #18421 | MERGED | S1b (4-point square at `(2,3)` falsification) | — |
| #18431 | MERGED | S1c (Pell-safety conjecture) | — |
| #18442 | MERGED | S1d (`weightedSumSquares` Mathlib recasting) | confirms `weightedSumSquares` location |
| #18494 | MERGED | S2a (extended Pell-safety search + mod-q descent) | — |
| #18554 | MERGED | S2b (QR-descent Mathlib audit for `(2, 5)`) | **audit-correction of §8.1 negative claim**; **errata on lines 155 → 156, 164 → 165**; **enumerates files S2b §8.1 omitted from its QuadraticForm/ listing**; **discusses gh-code-search vs v4.26.0 ref drift**; **enumerates alternative routes to full-rank safety actually available at v4.26.0** |
| _(this)_ | NEW | `sessions/2026-05-13-s2c-prep-mathlib-genus-and-hassemink-audit.md` | — |

**No file collision.** S2b explicitly anti-targeted "Do not extend the
empirical search beyond `R = 22`" and "Do not claim full-rank safety";
this PR does **neither**. It refines S2b's §8.1 inventory of what
Mathlib lacks and confirms (with corrections) the negative claim.

## 2. Recap — S2b §8.1's negative claim about Mathlib

S2b §8.1 (PR #18554) wrote:

> Mathlib has no Hasse-Minkowski / genus-theory infrastructure for
> ternary quadratic forms at v4.26.0
> (verified: `Mathlib/LinearAlgebra/QuadraticForm/` contains `Basic`,
> `Dual`, `Isometry`, `Real`, `IsometryEquiv` — no `Genus.lean` or
> `LocalGlobal.lean`).

This S2c PREP audits the claim against v4.26.0
(`leanprover-community/mathlib4@2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

## 3. Verified facts at v4.26.0 (pinned to commit `2df2f01`)

### 3.1. Actual contents of `Mathlib/LinearAlgebra/QuadraticForm/` at v4.26.0

Via `GET /repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/QuadraticForm?ref=v4.26.0`:

```
Basic.lean
Basis.lean              ← S2b §8.1 omitted
Complex.lean            ← S2b §8.1 omitted
Dual.lean
Isometry.lean
IsometryEquiv.lean
Prod.lean               ← S2b §8.1 omitted
QuadraticModuleCat.lean ← S2b §8.1 omitted
QuadraticModuleCat/     (subdir)
Real.lean
TensorProduct.lean      ← S2b §8.1 omitted
TensorProduct/          (subdir)
```

**ERRATUM (S2b §8.1):** The listing "`Basic`, `Dual`, `Isometry`,
`Real`, `IsometryEquiv`" enumerates 5 of 10 `.lean` files (and 0 of 2
subdirs). The negative-claim conclusion ("no `Genus.lean` or
`LocalGlobal.lean`") is still **correct** — neither file exists at any
depth in `Mathlib/LinearAlgebra/QuadraticForm/`. But the wording
"contains [5-item enumeration]" reads as if those were the only files,
which is false.

### 3.2. Negative-claim verification

| query | total hits | result |
|---|---|---|
| `HasseMinkowski repo:leanprover-community/mathlib4` (any branch) | 0 | confirmed |
| `Hasse Minkowski repo:... language:Lean` | 0 | confirmed |
| `Genus repo:... QuadraticForm` | 0 | confirmed |
| `local_global QuadraticForm repo:...` | 0 | confirmed |
| `ternaryQuadraticForm repo:...` | 0 | confirmed |

The negative claim **"no Hasse-Minkowski / genus-theory infrastructure
in Mathlib"** stands at v4.26.0 and at the present `main` branch of
Mathlib (commit `defda893` as of this audit). The S2 ACT formalisation
must continue to **axiomatise full-rank safety** for any safe pair
chosen, exactly as S2b §8.1 already noted.

### 3.3. Line-number errata in S2b §3 / §7

S2b §3 (citing QR lemmas) and §7 (the pointer table) cite:

- `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` at `...QuadraticReciprocity.lean:155`
- `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` at `...QuadraticReciprocity.lean:164`

The actual v4.26.0 file (verified):

```
:107 theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
:123 theorem quadratic_reciprocity' (hp : p ≠ 2) (hq : q ≠ 2) :
:134 theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q ≠ 2) :
:142 theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) :
:156 theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
:165 theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
```

S2b's `legendreSym.quadratic_reciprocity:107` is **VERIFIED**.

**ERRATA:**
- `exists_sq_eq_prime_iff_of_mod_four_eq_one` is at line **156**, not 155
  (off by 1).
- `exists_sq_eq_prime_iff_of_mod_four_eq_three` is at line **165**, not 164
  (off by 1).

S2 ACT consumers should treat S2b's line numbers as accurate to ±1,
and grep for the theorem name rather than seeking by line.

## 4. CAVEAT — `gh api search/code` returns matches against `main`, not v4.26.0

This audit ran a sequence of `gh api search/code?q=...` queries
against `leanprover-community/mathlib4`. The search engine returns
matches **against the default branch (`main`)**, with each `.items[i].url`
including a `ref=<commit>` query parameter pointing to the current
`main` HEAD (e.g., `defda893c008015592dbbf4e7d7c00a58aa62745` as of
this audit).

**This is post-v4.26.0.** Some files that appear in search results do
**not** exist at v4.26.0:

| file (returned by `weightedSumSquares` search) | exists at v4.26.0? | source |
|---|---|---|
| `Mathlib/LinearAlgebra/QuadraticForm/Real.lean` | **YES** | §3.1 directory listing |
| `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean` | **YES** | §3.1 |
| `Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean` | **YES** | §3.1 |
| `Mathlib/LinearAlgebra/QuadraticForm/Radical.lean` | **NO** | not in §3.1; gh contents 404 at `ref=v4.26.0` |
| `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean` | **NO** | not in §3.1; gh contents 404 at `ref=v4.26.0` |
| `Mathlib/LinearAlgebra/QuadraticForm/AlgClosed.lean` | **NO** | not in §3.1; gh contents 404 at `ref=v4.26.0` |

**Implication for S2 ACT:** Any agent who consumes
`gh api search/code` results without pinning the `ref` query parameter
to `v4.26.0` may import a module that does not exist at the project's
Mathlib pin. The correct workflow is:

1. Search via `/search/code?q=...&ref=v4.26.0` if supported (GitHub's
   code search does **not** honour `ref` directly for filtering — only
   for resolving paths post-hoc).
2. **After** identifying a path from search, **verify file existence**
   at v4.26.0 via
   `GET /repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`.
3. If the file 404s at v4.26.0, **flag for upstream-pin-bump** before
   using.

This caveat applies to **all PREP/ACT** sessions, not just this slug.
It is recorded here because the discovery occurred during this audit;
a future hermit/curator pass may want to lift it into the global
research playbook.

## 5. Alternative routes for full-rank safety actually present at v4.26.0

S2b §8.1 correctly notes Mathlib has no Hasse-Minkowski. This section
enumerates the **partial-route** infrastructure that **does** exist
at v4.26.0, with honest assessment of what each can and cannot do for
the full-rank safety question.

### 5.1. `QuadraticMap.Anisotropic` and `PosDef` (Mathlib/LinearAlgebra/QuadraticForm/Basic.lean)

Verified at v4.26.0:

```
:1099 def Anisotropic (Q : QuadraticMap R M N) : Prop :=
:1135 def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
:1149 theorem PosDef.anisotropic {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef) : Q.Anisotropic :=
:1160 theorem posDef_iff_nonneg {Q : QuadraticMap R₂ M N} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
```

**What this gives us for `Q_{2,5}(a,b,c) = a² + 2b² + 5c²`:** The form
is manifestly positive-definite over `ℤ`, `ℚ`, `ℝ` (each diagonal
coefficient is positive). Hence `Anisotropic Q_{2,5}` is provable
directly via:

```lean
have h_pd : Q_{2,5}.PosDef := by
  rw [posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · -- nonneg: each summand is nonneg
    intro x; positivity
  · -- anisotropic over ℝ trivially because squared-sum of nonneg
    -- terms is 0 iff each is 0 iff x = 0
    intro x hx; ...
have h_aniso : Q_{2,5}.Anisotropic := h_pd.anisotropic
```

**What this does NOT give us:** Anisotropy is `Q(v) = 0 ⟹ v = 0`.
The S1c safety condition we want to rule out is `Q(v) = Q(w) = N` (for
arbitrary `N ≠ 0`) AND `B(v, w) = 0` AND `v ≠ ±w`. Anisotropy
addresses the `N = 0` case only.

**Status of this route:** Useful as a **trivial preamble** (proves
the `N = 0` case is vacuous), but does not advance full-rank safety
for `N ≠ 0`.

### 5.2. `equivalent_signType_weighted_sum_squared` (Mathlib/LinearAlgebra/QuadraticForm/Real.lean)

Verified at v4.26.0 (file exists; theorem names):

```
:55 theorem equivalent_sign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
:65 theorem equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
:74 theorem equivalent_signType_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
:83 theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
```

**What this gives us:** Sylvester's law of inertia — every real
nondegenerate quadratic form is equivalent (over ℝ) to a `±1`-weighted
sum of squares. The signature of `Q_{2,5}` over ℝ is `(3, 0, 0)`
(definite, all positive). This collapses `Q_{2,5}` (as a real form)
into the standard Euclidean form on `ℝ³`.

**What this does NOT give us:** The equivalence is over **ℝ**, not
over **ℤ**. The S1c failure mode is integral — `v, w ∈ ℤ³` with
`B(v,w) = 0` mod arithmetic constraints. Reducing to standard
Euclidean ℝ³ loses the integral structure entirely. In other words,
**every** real positive-definite ternary form has integer
representations of large `N` with `B = 0`; what makes the S1c
condition meaningful is the **density** of those representations,
which is a number-theoretic question, not a real-analytic one.

**Status of this route:** Useful as **scaffolding** for showing the
form is in standard signature class, but the rate question is
orthogonal to signature theory.

### 5.3. `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` (verified §3.3)

Already used in S2b §3 / §5. The route is: for axis-vs-plane failure
modes, `QuadraticReciprocity` lets us close the descent. **Does not
address full-rank failures.** S2b §8.1 already noted this gap.

### 5.4. `Mathlib.NumberTheory.Zsqrtd` (verified at v4.26.0)

Contents:

```
Basic.lean         — ring `ℤ[√d]`, norm, universal property
GaussianInt.lean   — special case d = -1
QuadraticReciprocity.lean
ToReal.lean
```

**Relevance to `Q_{2,5}`:** The lattice `L_{2,5}` is **not** isomorphic
to `ℤ[√d]` for any single `d`; it's a rank-3 lattice with diagonal
form `(1, 2, 5)`, while `ℤ[√d]` is rank 2. So `Zsqrtd` does not embed
`L_{2,5}` directly.

**Partial use:** The 2-coordinate sublattices `{(0, b√2, c√5)}` ≅
`ℤ[√2] ⊕ ℤ[√5]` (additive only, not a ring), or `{(a, 0, c√5)}` etc.
For axis-vs-plane safety on the `(b√2, c√5)`-plane, Mathlib's
`ℤ[√(−10)]`-style infrastructure could be invoked, but **not** at the
ternary level.

**Status of this route:** Useful for **2-dim sub-cases** but does not
generalise to the 3-dim full-rank question.

### 5.5. `Mathlib.NumberTheory.Pell` (verified at v4.26.0)

Provides `Pell.Solution₁ d` for the equation `x² − d·y² = 1`
(signature `(1, 1)`, **hyperbolic**).

**Relevance to `Q_{2,5}`:** `Q_{2,5}(a, b, c) = a² + 2b² + 5c² = N` is
**elliptic** (signature `(3, 0)`, positive-definite). The unit-group
theory of Pell `(x² − dy² = 1)` is fundamentally different from the
representation theory of definite ternary forms. Pell counts an
infinite family of solutions (unit group is `ℤ` once non-trivial);
definite-ternary `r(Q, N)` is **finite** for each `N`.

**Status of this route:** Not applicable. The S1c failure mode is
**not** a Pell-style infinite family; it's a single-pair coincidence
within a finite shell `Q⁻¹(N)`.

### 5.6. Net conclusion on §5 enumeration

Of the **5 candidate routes** at v4.26.0:

| route | applicable to full-rank safety for `Q_{2,5}`? |
|---|---|
| §5.1 `PosDef`/`Anisotropic` | only `N = 0` case (trivial) |
| §5.2 Real signature | over ℝ only, loses integral structure |
| §5.3 QR (S2b's §3) | axis-vs-plane only (S2b §8.1 already noted) |
| §5.4 `Zsqrtd` | 2-dim sub-cases only |
| §5.5 Pell `Solution₁` | wrong signature class |

**None addresses the full-rank failure question.** S2b §8.1's
conclusion — "**`L_{2, 5}` is axis-vs-plane safe (theorem), and
empirically safe up to `R = 22` against all failure modes (computation,
not theorem)**" — is the strongest honest claim available at v4.26.0
without new infrastructure.

## 6. Two implications for S2 ACT

### 6.1. The axis-vs-plane-only formalisation is the **upper bound**, not lower bound

S2b §5 templates a ~140 LOC S2 ACT that proves `safeLattice_2_5_axis_vs_plane`.
The S2 ACT consumer should be **honest** that this theorem **does
not** discharge the S3 ACT axiom `safeLattice_fourPointProperty`
— that axiom continues to require a full-rank-safety supplementary
clause (axiom or empirically-anchored bound).

The honest typeclass signature is:

```lean
-- After S2 ACT (axis-vs-plane only):
theorem axisVsPlane_safe : SafePrimePair_AxisVsPlane 2 5 := ...

-- Still required as axiom for S3 ACT:
axiom fullRank_empirically_safe : SafePrimePair_FullRank 2 5
  -- justification: S2a §6.5 verified empirically to R = 22
  -- Mathlib at v4.26.0 has no Hasse-Minkowski to upgrade this to a theorem

def SafePrimePair (p q : ℕ) : Prop :=
  SafePrimePair_AxisVsPlane p q ∧ SafePrimePair_FullRank p q
```

This is **structurally** what S2b §8 already implies; this PREP makes
the type signature explicit.

### 6.2. S2 ACT should NOT import `Signature.lean` / `Radical.lean` / `AlgClosed.lean`

These files exist on the present Mathlib `main` (commit `defda893+`)
but **do not exist at v4.26.0** (the project's pinned Mathlib version).
Any `import Mathlib.LinearAlgebra.QuadraticForm.Signature` (or
`Radical`, `AlgClosed`) in `proofs/Proofs/Erdos659OQ01OQ02.lean` will
fail at the lake-build step.

If a future S2 ACT consumer wants `Sylvester.equivalent_signType_weighted_sum_squared`
specifically (per §5.2), they should import
`Mathlib.LinearAlgebra.QuadraticForm.Real` instead, which exists at
both v4.26.0 and present `main`.

## 7. Cross-slug pointer — sister-slug `erdos-659-oq-01-oq-01`

The parent OQ `erdos-659-oq-01-oq-01` (already in the gallery,
`status: axiomatized`, 2D version) **also** depends on `Q_{p, q}`-style
lattice constructions, but only for `d = 2` (i.e., `Q(a, b) = a² + pb²`
where `B(v, w) = v_1 w_1 + p v_2 w_2`).

For `d = 2`:
- 2-dim "axis-vs-plane" reduces to "axis-vs-axis" (trivial).
- "Full-rank" reduces to "both coordinates non-zero" (no symmetry).
- `Mathlib.NumberTheory.Zsqrtd` (§5.4) **does** directly apply.

A future sibling PREP `erdos-659-oq-01-oq-01-s?-prep-zsqrtd-bridge`
could mine `Zsqrtd.Basic` for a complete `d = 2` formalisation. That
work is **out of scope** for this slug's `d ≥ 3` rate question, but
would feed into the family's overall gallery presence.

## 8. Anti-targets (do NOT attempt now)

* ❌ **Do not write the Lean code for `Q_{2,5}`.** This S2c is doc-only.
  The Lean code in §5 of S2b is the template for S2 ACT.
* ❌ **Do not edit `problem.md`, `knowledge.md`, or `state.md`.** This
  is a PREP. Landscape edits remain S2 ACT's responsibility.
* ❌ **Do not edit any prior session file** (s1, s1b, s1c, s01d, s2a,
  s2b). Each has its own context; appending here is the right channel.
* ❌ **Do not extend the empirical search beyond `R = 22`.** S2b
  already anti-targeted this. The honest claim is the §6.1 typeclass
  signature with `fullRank_empirically_safe` as an axiom.
* ❌ **Do not propose a Hasse-Minkowski upstream Mathlib PR.** That is
  a significant undertaking, not appropriate for a PREP. If a future
  contributor decides to write `Mathlib/LinearAlgebra/QuadraticForm/Genus.lean`,
  the entry-point conversation should happen in the mathlib4 zulip,
  not in this repo.
* ❌ **Do not claim that `equivalent_signType_weighted_sum_squared`
  (§5.2) closes the full-rank gap.** §5.6 explicitly enumerates why
  each of the 5 candidate routes does NOT close the gap.

## 9. No-edit guarantee

This PR adds exactly **one** new file:

```
research/problems/erdos-659-oq-01-oq-02/sessions/
  2026-05-13-s2c-prep-mathlib-genus-and-hassemink-audit.md
```

It does **not** modify:
* `research/problems/erdos-659-oq-01-oq-02/problem.md`
* `research/problems/erdos-659-oq-01-oq-02/knowledge.md`
* `research/problems/erdos-659-oq-01-oq-02/state.md`
* any prior session file (`s1`, `s1b`, `s1c`, `s01d`, `s2a`, `s2b`)
* `proofs/Proofs/` (no Lean files for this slug exist yet)
* `src/data/research/problems/erdos-659-oq-01-oq-02.json` (gallery JSON)
* `src/data/proofs/` (no gallery integration exists yet)
* the candidate pool or any claim files

Conflict-free against #18322, #18421, #18431, #18442, #18494, #18554
(all merged). Conflict-free against any future S2 ACT that creates
`proofs/Proofs/Erdos659OQ01OQ02.lean`.

## 10. Honesty notes

1. **All Mathlib citations are verified at commit
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (the `inputRev: v4.26.0`
   pin in `proofs/lake-manifest.json`). Each file:line in §3 was
   fetched via `gh api ... /contents/<path>?ref=v4.26.0` and decoded
   from base64.

2. **The `gh api search/code` caveat (§4) is the most actionable
   finding.** Past PREPs (including some in adjacent slugs) cite
   `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean` or similar
   post-v4.26.0 paths without flagging the version drift. This PREP
   flags the issue explicitly for this slug and notes it could
   benefit from a global lift.

3. **The `equivalent_signType_weighted_sum_squared` line numbers
   in §5.2 are from `Mathlib/LinearAlgebra/QuadraticForm/Real.lean`
   at v4.26.0**, also verified via gh contents API.

4. **The `Anisotropic` and `PosDef` line numbers in §5.1 are from
   `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean` at v4.26.0**.
   The text says "verified at v4.26.0"; the verification was a `grep
   -n "def Anisotropic\|^def PosDef\b"` on the base64-decoded contents.

5. **The line-number errata in §3.3 are off by exactly 1.** This is
   most plausibly explained by S2b citing a slightly earlier or later
   commit of Mathlib, then a single-line insertion shifted the count.
   The errata are not blocking for S2 ACT consumers who use grep, but
   they should be noted.

6. **§5 routes are negative results.** §5.1-5.5 enumerate routes that
   exist in Mathlib v4.26.0 and are insufficient. The negative
   enumeration is itself the contribution — it tells S2 ACT not to
   waste time chasing these threads in pursuit of full-rank safety.

7. **No new mathematics.** All five candidate routes are standard
   Mathlib infrastructure; the contribution is the **adequacy
   classification** (which routes apply, which don't, for the
   specific S1c failure-mode question).

8. **§6.1's `SafePrimePair` typeclass refactor is a recommendation,
   not a requirement.** S2 ACT may choose a different decomposition
   if cleaner; the substantive point is the explicit
   `fullRank_empirically_safe` axiom, not the precise structure name.

9. **No empirical computation.** This PREP does no number-theoretic
   computation beyond what S2a / S2b already did. The contribution is
   bibliometric (verifying Mathlib v4.26.0 contents) and structural
   (the §5 enumeration / §6 typeclass).

## 11. References

- **S2b (PR #18554)**: QR-descent Mathlib audit for `(2, 5)`. §8.1
  is the source of the negative claim audited here.
- **S2a (PR #18494)**: extended Pell-safety search + mod-q descent.
  §6.5 (axis-vs-plane characterisation) is the source of S2b §8.1's
  "axis-vs-plane only" caveat.
- **S1c (PR #18431)**: Pell-safety conjecture for `L_{p, q}`.
- **S1b (PR #18421)**: 4-point square falsification at `(p, q) = (2, 3)`.
- **S1d (PR #18442)**: `weightedSumSquares` recasting.
- **S1 (PR #18322)**: rate-conjecture survey for ℝ^d, `d ≥ 3`.
- **Mathlib v4.26.0** at commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  authoritative source for §3, §5.1, §5.2, §5.4, §5.5 citations.
- **GitHub Code Search API** (Search Code endpoint): documented at
  `https://docs.github.com/rest/search/search#search-code`. The caveat
  in §4 is documented at `https://docs.github.com/rest/search` (search
  is over the latest indexed state, not historical refs).
- **`leanprover-community/mathlib4` `main`** at commit
  `defda893c008015592dbbf4e7d7c00a58aa62745` (as of this audit): the
  source of the divergent file paths in §4 (Signature.lean,
  Radical.lean, AlgClosed.lean).
