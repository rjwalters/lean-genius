# ehrhart-cube-proven-oq-03: Knowledge Base

## Problem Summary

Add a NEW gallery entry on **Barvinok's polynomial-time lattice-point
counting algorithm** for rational polytopes in fixed dimension.  Sister
to the existing `ehrhart-cube-proven*` family (which addresses
identity-type Ehrhart questions), focusing instead on the
**generating-function / algorithmic** angle.

**Status (S1 OBSERVE)**: workspace + survey only; no Lean changes.

## Existing Gallery Inventory

Pulled from `find src/data/proofs -maxdepth 1 -type d -name 'ehrhart*'`.

| Directory                            | Status     | Lean file path                     | Focus                                              |
|--------------------------------------|------------|------------------------------------|----------------------------------------------------|
| `ehrhart-cube-proven`                | verified   | `Proofs/EhrhartCubeProven.lean`    | First-principles `(n+1)ᵈ`, 26 theorems, 0 axioms.  |
| `ehrhart-cube-proven-oq-01`          | varies     | (see meta.json — not surveyed S1)  | Sibling                                            |
| `ehrhart-cube-proven-oq-02`          | COMPLETED  | (see workspace `ehrhart-cube-proven-oq-02.json`) | "Ehrhart polynomials without general existence theorem" |
| `ehrhart-cube-proven-oq-04`          | PROVED     | `Proofs/EhrhartCubeProvenOQ04.lean` | Eulerian h*-vector + Worpitzky + palindrome.       |

**Gap**: no Barvinok-style algorithmic / generating-function entry.

## Mathlib v4.26.0 Survey (training knowledge — S2 to probe)

Pinned at `proofs/lakefile.toml` line 8: `rev = "v4.26.0"`.

### Confirmed available (used by `EhrhartCubeProven.lean`)

- `Fintype.card_fun` — `Mathlib.Data.Fintype.Basic`.
- `Finset.sum_geometric_two_add_one` and related — geometric series.
- `Mathlib.Combinatorics.Polytope.*` — exists.
- `Mathlib.Combinatorics.Polytope.Ehrhart` — exists (used by other
  ehrhart-cube-proven entries).

### Plausibly available (S2 to verify)

- `Polynomial.geom_series` — `(1 − x^{n+1}) / (1 − x)` identities.
- `MvPolynomial.aeval` — for multi-variable generating functions.
- `RatFunc` — rational functions over a field, including the
  field-of-fractions construction.
- `MvPowerSeries` — multivariate formal power series.
- `LinearProgramming` infrastructure? Likely sparse; Mathlib's
  polytope theory is mostly geometric, not algorithmic.

### Almost-certainly absent (the gap Barvinok fills)

- **Signed simplicial-cone decomposition** of an arbitrary rational
  cone (Barvinok's signed-decomposition algorithm).
- **Short rational generating function** form
  `f(P; x) = ∑ᵢ ε_i · x^{u_i} / ∏ⱼ (1 − x^{v_{i,j}})` with
  bounded `i`, `ε_i ∈ {±1}`.
- **Polynomial-time complexity** statements (Mathlib has no formal
  complexity class library; would have to be axiomatised).

## Proof Strategy (proposed for S2)

### Tier 1 (minimum viable gallery entry, S2)

`proofs/Proofs/EhrhartCubeProvenOQ03.lean` — 200–350 lines:

- Define a **short rational generating function**: a finite formal
  expression `∑ᵢ ε_i · x^{u_i} / ∏ⱼ (1 − x^{v_{i,j}})` with
  `ε_i ∈ {±1}`, `u_i, v_{i,j} ∈ ℤᵈ`.
- State **Brion's theorem**: for a rational polytope `P`,
  `f(P; x) = ∑ᵥ f(tangentCone v P; x)` where the sum is over vertices
  `v` of `P`.
- State **Barvinok's theorem** (the polytime algorithm) as an axiom
  with the polytime complexity claim itself axiomatised (since
  Mathlib has no formal complexity-class library).
- **Corollary**: short generating function for `[0, n]ᵈ` cube:
  `f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)`.  This is a
  *first-principles* lemma that can be PROVED (not axiomatised) via
  Mathlib's geometric series + factorisation.

### Tier 2 (stretch, S3)

- Implement the 2-D Barvinok signed decomposition: every 2-D rational
  cone is a signed sum of unimodular cones, with the unimodular
  decomposition produced via continued-fraction-style descent.
  ~300–500 Lean lines.

### Tier 3 (long-term)

- Higher-dimensional signed decomposition (Barvinok's general
  algorithm).  Out of scope for any single PR; future OQ.

## Cross-Reference Plan

The new gallery entry should `import Proofs.EhrhartCubeProven` to
reuse the `(n+1)ᵈ` identity as a sanity check.  The relation:

```
(n+1)ᵈ      = #([0,n]ᵈ ∩ ℤᵈ)
            = lim_{x → 1} ∏ᵢ (1 - xᵢⁿ⁺¹) / (1 - xᵢ)
            = lim_{x → 1} f([0,n]ᵈ; x)
```

is the *bridge* lemma between OQ-03 and the parent.

## Recent Gallery Standards

- New gallery files use `theorem`/`lemma`/`axiom` mix; total `axiom`
  count goes in `meta.json -> axiomCount`.
- Sibling files (OQ-01/02/04) all live in `Proofs/EhrhartCubeProven*.lean`;
  OQ-03 should follow the same naming.
- Status mapping: `verified` if 0 axioms 0 sorries; `axiomatized` if
  ≥1 axiom; `formalized` if ≥1 sorry.

## Mathlib API Probes (deferred to S2)

S2.1 — Probe file `Proofs/EhrhartCubeProvenOQ03Probe.lean`:

```lean
import Mathlib.Combinatorics.Polytope.Ehrhart
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

-- Confirm presence of these (best-guess names):
#check @MvPolynomial
#check @RatFunc
#check @MvPowerSeries
#check @Polynomial.geom_series_def
```

If `Polynomial.geom_series_def` exists, the corollary
`f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)` reduces to a single-line
proof per dimension + `Finset.prod_pi_apply` or analogous.

## Next Action

Land S1 OBSERVE doc-only PR (this commit), then claim S2 ACT to
implement Tier 1.

## References

- Barvinok 1994 (canonical algorithm paper).
- Beck & Robins (2015) ch. 11.
- ~~Mathlib4 `Mathlib.Combinatorics.Polytope.Ehrhart`~~ — **does not
  exist** (see §S2 PREP Mathlib bearer audit below).
- Lean Genius `Proofs/EhrhartCubeProven.lean` (verified parent).

---

## S2 PREP — Mathlib bearer audit (2026-05-13, researcher-10)

The S1 OBSERVE plan above claims Mathlib v4.26.0 ships
`Mathlib.Combinatorics.Polytope.Ehrhart` and an Ehrhart-theory toolkit.
A bearer audit at the lake-pinned Mathlib SHA `2df2f0150c27`
(`proofs/lake-manifest.json`) shows this is **false**.

### Method

GitHub Search API + Contents API against
`leanprover-community/mathlib4` at `ref=2df2f0150c27` — the SHA the
worktree's `lake build` would resolve. Names are stable across Mathlib
HEAD and the pinned SHA (per project memory
`Mathlib bearer-audit PREPs frequently cite Mathlib HEAD instead of
lake-pinned SHA`), so absence at the pinned SHA implies absence on
HEAD as well; we verified the pinned SHA to be conservative.

### Findings

| Query | Result | Verdict |
|---|---|---|
| `q=Ehrhart` (whole repo, lean files) | 0 hits | **No Ehrhart support in Mathlib.** |
| `q=Polytope in:path` | 0 hits | **No `Polytope` directory in Mathlib.** |
| `q=LatticePolytope` | 0 hits | **No `LatticePolytope` type in Mathlib.** |
| `q=hStar` / `q=Eulerian filename:Eulerian` | 0 hits | **No h*-vector or Eulerian-polynomial Polytope link in Mathlib.** |
| `GET .../contents/Mathlib/Combinatorics/Polytope/Ehrhart.lean?ref=2df2f0150c27` | HTTP 404 | direct fetch confirms absence |
| `GET .../contents/Mathlib/Combinatorics?ref=2df2f0150c27` | 200, no `Polytope` subdir | confirms absence at the directory level |

The algebraic substrate the Barvinok plan ultimately rests on **does**
exist, with one path correction:

| Module | Status | Audit |
|---|---|---|
| `Mathlib.FieldTheory.RatFunc.Basic` | ✓ exists | 45 125 B, contents-API HTTP 200 |
| `Mathlib.Algebra.MvPolynomial.Basic` | ✓ exists | 41 370 B, contents-API HTTP 200 |
| `Mathlib.RingTheory.MvPowerSeries.Basic` | ✓ exists | search HTTP 200 |
| ~~`Mathlib.RingTheory.PowerSeries.Basic` (S1 plan)~~ | path drift | ✓ exists but the multivariate generating function for [0, n]^d lives in `MvPowerSeries`, not `PowerSeries`; S1 plan cited the univariate path. |

The dead doc-URL
`leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Polytope/Ehrhart.html`
listed in the JSON `references.urls` is removed in this PR (the
HTML mirrors a module that does not exist).

### Corrected Mathlib gap inventory

The S1 OBSERVE `mathlibGaps` list under-stated the gap. Corrected list:

1. **No Ehrhart-theory toolkit at all** — the S1 plan assumed a
   `Mathlib.Combinatorics.Polytope.Ehrhart` foundation to build on.
   There is none. Any retargeted Barvinok work must define its own
   `EhrhartFn` / `LatticePolytope` / `interiorEhrhartFn` shells from
   scratch over `MvPolynomial` / `RatFunc` / `MvPowerSeries`.
2. **No `LatticePolytope` type, no `Polytope` namespace.** The unit
   d-cube would need to be encoded as `Set (Fin d → ℝ)` or via
   `Fin d → Set.Icc (0 : ℝ) 1` and the lattice-point condition
   handled by hand.
3. **No signed simplicial-cone decomposition.** This is the
   algorithmic core of Barvinok-1994; defer to S3+ stretch or future
   sibling slug.
4. **No formal complexity-class library.** Polytime claim must be
   axiomatic.

### Slot-drift cross-reference

In parallel with the bearer audit, the S2 PREP also discovered the
slug slot is **already occupied on main** by an entirely orthogonal
hypersimplex scaffold (`proofs/Proofs/EhrhartCubeProvenOQ03.lean`,
119 LOC, 2 sorries, `namespace EhrhartCubeProvenOQ03`, gallery dir
populated). See `state.md` (§Findings 2–4) for the full description
of the drift and the deferred scope decision (Option A: continue
hypersimplex; Option B: spin off Barvinok as a new sibling `oq-05`).

### Implication for any future S2 ACT

Whichever scope option is chosen, the S2 ACT Lean file **cannot**
import `Mathlib.Combinatorics.Polytope.Ehrhart`. The S1 OBSERVE
"S2.1 probe" must be replaced with hand-rolled definitions over
`MvPolynomial` and `RatFunc` (or with `import Mathlib` to bring in
the full algebra substrate). The bearer audit gives the green list
of modules that actually work; the Docker probe is no longer
informational and can be skipped.

---

## S3 PREP — Hypersimplex-track Mathlib bearer audit (2026-05-13, researcher-4)

Complement to §S2 PREP above. S2 audited the **Barvinok** track (the
JSON-stated slug subject) and found Mathlib's Ehrhart toolkit
absent — bearer-blocked. This S3 audits the **hypersimplex** track
(the on-main scaffold's actual content) and finds Mathlib's
combinatorial toolkit fully sufficient — bearer-clean.

### Method

Same as S2: GitHub Contents + Search API against
`leanprover-community/mathlib4` at `ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Findings

| Sorry / role | Lemma | Path at pinned SHA | Line | Signature |
|---|---|---|---|---|
| `hypersimplex_count_k_one` primary | `Sym.card_sym_eq_choose` | `Mathlib/Data/Sym/Card.lean` | 113 | `card (Sym α k) = (card α + k - 1).choose k` |
| `hypersimplex_count_k_one` helper | `Sym.card_sym_fin_eq_multichoose` | `Mathlib/Data/Sym/Card.lean` | 94 | `card (Sym (Fin n) k) = multichoose n k` |
| `hypersimplex_palindrome_k_d_minus_1` primary | `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean` | 366 | `(i j : non-dependent) (MapsTo, MapsTo, LeftInvOn, RightInvOn) ⇒ #s = #t` |
| Palindrome (alt) | `Finset.card_image_of_injective` | `Mathlib/Data/Finset/Card.lean` | 242 | `[DecidableEq β] (Injective f) ⇒ #(s.image f) = #s` |
| Aux (both) | `Finset.sum_add_distrib` | `Mathlib/Algebra/BigOperators/*` (canonical lemma; 81 in-repo hits) | n/a | `∑ (f + g) = ∑ f + ∑ g` |
| Aux (palindrome) | `Nat.sub_add_cancel` | `Mathlib/Data/Nat/Defs.lean` | n/a | `n ≤ m ⇒ m − n + n = m` |
| Aux (k = 1 swap) | `Nat.choose_symm` | `Mathlib/Data/Nat/Choose/Basic.lean` | n/a | `k ≤ n ⇒ n.choose k = n.choose (n − k)` |

**Verdict.** Hypersimplex-track lemmas are all present at the pinned
SHA. The docstring proof sketches (file lines 70–88) cite the right
strategies; this audit certifies they are executable as cited.

### Caveat (matters for k = 1 sorry)

`Sym.card_sym_eq_choose` gives `#(Sym α k)`, not `#{x : Fin d → Fin (n+1) | ∑ x_i = n}` directly. The "x_i = multiplicity of i" bijection
between these two finite sets is **NOT** a one-liner in Mathlib — it
must be constructed (see state.md §Refined proof outline for
`hypersimplex_count_k_one`). The docstring sketch's claim that the
result follows by `Sym.card_sym_eq_choose` after "setting y_i = x_i
for i < d - 1 and absorbing the slack" elides this construction;
S5+ ACT would need to materialise it (≈ 50 LOC) before chaining
into `card_sym_eq_choose`.

### Implication for any future S4 ACT (Option A path)

S4 ACT can begin immediately on the **palindrome** sorry with
`Finset.card_nbij'` + a small involution + `Nat.sub_add_cancel` +
`omega`, in ≤ 60 LOC, with a single Docker build cycle. The k = 1
sorry should be deferred to S5+ pending Lean-4 idiom shake-out
during S4 ACT.
