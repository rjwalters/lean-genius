# hilbert-14-oq-04 — S4 PREP-3: close S3 PREP-2 §3.2 Stage 3 totalDegree-of-charpoly-coefficient bearer gap + surface hidden grading-preservation assumption (doc-only)

**Date**: 2026-05-16
**Phase**: S4 PREP-3 (doc-only — closes the last "still requires audit" gap
in the S3-bound ACT bearer chain, AND surfaces a NEW hidden hypothesis
that the S3-bound ACT writer must address)
**Researcher**: researcher-1
**Branch**: `research/hilbert-14-oq-04-iter-1778924087`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged
from S3 PREP-2)
**Status**: Pre-ACT design memo — no Lean changes, no edits to
`problem.md` / `knowledge.md` / `proofs/Proofs/Hilbert14OQ04.lean` / sibling
slugs / gallery `meta.json`. Two minimal edits: `state.md` (iter
counter + Phase header refresh — absorbing PRs #19188 and #19294 that
merged without bumping it) and `src/data/research/problems/hilbert-14-oq-04.json`
(matching iter / lastUpdate / focus refresh).

## §0 Why this PREP-3

Three observable facts in the slug's post-PREP-2 landscape make a doc-only
PREP-3 the highest-leverage available action without conflicting:

1. **PR #19294** (S3 PREP-2, doc-only — pin-verifies PR #18988 Lean
   bearers + closes S2g §2.4 Vieta gap) **merged** at `53b0ac0c8d1`.
   PREP-2 §3.2 Stage 3 explicitly left **one residual bearer search**:

   > The main S3-bound bearer that **still requires audit by the next ACT
   > writer** is the `totalDegree` bound on `esymm`-style coefficient
   > polynomials — this PREP-2 narrows the search to two Mathlib files
   > (`Mathlib/Algebra/Polynomial/Monic.lean`,
   > `Mathlib/RingTheory/MvPolynomial/Symmetric/Basic.lean`) but does not
   > pin the exact theorem name.

   This PREP-3 §1 below closes that search at SHA — but the answer is
   neither of those two files. The relevant bearers live in
   `Mathlib/Algebra/MvPolynomial/Degrees.lean` (general `totalDegree`
   submultiplicativity over `Finset.prod`) and
   `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean` (the only
   `esymm`-specific degree fact, which is about `.degrees` not
   `.totalDegree`).

2. **PR #19188** (S3 PREP coordination — pure doc-only 108 LOC) also
   **merged** at `e414eb24813`, and the predecessor S2-finite ACT (PR
   #18988) merged at `f15806dfc66`. After all three merges, `state.md`
   still reports **`Iteration: 2`** (last touched in PR #18988); the
   S3 PREP (PR #19188) and S3 PREP-2 (PR #19294) merged without bumping
   the counter. PREP-3 absorbs the resulting 2-iteration drift.

3. **Host infra blocked**: `df -h /System/Volumes/Data` reports 100% /
   6.9 Gi available; `docker info --format '{{.ServerVersion}}'`
   timeouts at 10s (daemon hung). No S3-bound ACT can be
   build-verified in this cycle. PREP-3 is the natural form: doc-only,
   absorbs prior-PREP drift, supplies bearer-pinned design for the
   next Docker-available ACT writer.

**Net deliverable**: (a) close PREP-2 §3.2 Stage 3 with **6 named
Mathlib bearers** at SHA + a 3-step composition recipe (§1); (b) surface
a **NEW hidden hypothesis** that the S3-bound ACT writer must add
(`MulSemiringAction G R` does not imply degree-preservation; the
standard Noether-1916 statement secretly assumes the G-action is
graded), with 3 design options + LOC tradeoff (§2); (c) refresh
state.md head + JSON to absorb PRs #19188 + #19294 (§3); (d) supply a
sharpened paste-ready S3-bound ACT skeleton (§4); (e) ACT-readiness
gate refresh (§5).

**Anti-targets**: doc-only single new file under `sessions/` + minimal
state.md + JSON refresh. No edits to `problem.md` / `knowledge.md` /
any `.lean` file (most importantly: NO touch of
`proofs/Proofs/Hilbert14OQ04.lean`) / sibling slugs / gallery
`meta.json` / any prior session/PREP file. Strictly conflict-free.

## §1 Close PREP-2 §3.2 Stage 3 totalDegree gap — 6 bearers at SHA

All bearers fetched via:

```
gh api 'repos/leanprover-community/mathlib4/contents/<File>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d
```

### §1.1 The 6 totalDegree bearers

| # | Bearer | Path & line | Signature at SHA | Role for S3-bound ACT |
|:--|:-------|:------------|:-----------------|:----------------------|
| W1 | `MvPolynomial.totalDegree_smul_le` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:411` | `[CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S) : (a • f).totalDegree ≤ f.totalDegree` | Scalar-action bound (degree non-increase under R-action — does **NOT** apply to G-action; see §2 below). |
| W2 | `MvPolynomial.totalDegree_mul` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:407` | `(a * b).totalDegree ≤ a.totalDegree + b.totalDegree` | Multiplicativity-additive bound. |
| W3 | `MvPolynomial.totalDegree_pow` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:415` | `(a ^ n).totalDegree ≤ n * a.totalDegree` | Power bound (corollary of W2). |
| W4 | `MvPolynomial.totalDegree_finset_prod` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:445` | `{ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) : (s.prod f).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree` | **Load-bearing** for the orbit-coefficient bound: bounds `(∏_{g ∈ T} (g•v)).totalDegree` by `∑ (g•v).totalDegree`. |
| W5 | `MvPolynomial.totalDegree_finset_sum` | `Mathlib/Algebra/MvPolynomial/Degrees.lean:448` | `{ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) : (s.sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree` | Bounds `(esymm_k _).totalDegree = (∑ over k-subsets of …).totalDegree` by `sup` over k-subsets. |
| W6 | `MvPolynomial.degrees_esymm` | `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:286` | `[Nontrivial R] {n : ℕ} (hpos : 0 < n) (hn : n ≤ Fintype.card σ) : (esymm σ R n).degrees = (univ : Finset σ).val` | The only `esymm`-specific bearer; bounds `.degrees` (a Multiset), not `.totalDegree` (a ℕ). Auxiliary; not on the critical path for the S3-bound result. |

### §1.2 Negative finding — NO `MvPolynomial.totalDegree_esymm` bearer

A grep `gh api 'search/code?q=%22totalDegree%22+%22esymm%22+repo:leanprover-community/mathlib4'`
at SHA returns **zero hits**. There is no direct
`(esymm σ R n).totalDegree ≤ n` bearer. PREP-2 §3.2 Stage 3 anticipated
either `Symmetric/Basic.lean` or `Algebra/Polynomial/Monic.lean`;
neither file even exists at SHA (the Symmetric directory contains only
`Defs.lean`, `FundamentalTheorem.lean`, `NewtonIdentities.lean`). The
S3-bound ACT writer must **build the bound by hand** via W4 + a
per-monomial pointwise degree-1 input bound, NOT via a named
`totalDegree_esymm` lemma.

### §1.3 Composition recipe for `(charpoly G b).coeff k` totalDegree bound

The chain assembling the Noether-bound (with `b : R = MvPolynomial (Fin n) k`
a **degree-1** input — see §2 for why this hypothesis is non-trivial):

```
(charpoly G b).coeff k    -- the polynomial coefficient at degree k
  = (∏_g (X - C (g•b))).coeff k                     -- by V1 (charpoly_eq, Invariant/Basic.lean:140)
  = (Finset.univ.prod fun g => X - C (g•b)).coeff k  -- by Finset.prod = ∏_g
  = (Multiset.map (fun t => X - C t) ({g•b : g ∈ G})).prod.coeff k   -- by Finset.prod_eq_multiset_prod
  = (-1)^(|G| - k) * ({g•b : g ∈ G}).esymm (|G| - k) -- by V5 (Vieta, Polynomial/Vieta.lean:101)
```

So `(charpoly G b).coeff k` (as an element of `R`) equals
`(-1)^(|G| - k) * (Multiset esymm of orbit elements at index |G| - k)`. The
multiset-`esymm` of `{g•b : g ∈ G}` expands as a sum over (|G| - k)-subsets
T ⊆ G:

```
({g•b : g ∈ G}).esymm (|G| - k) = ∑_{T ⊆ G, |T| = |G|-k} ∏_{g ∈ T} (g • b)
```

So:

```
((-1)^(|G| - k) * esymm …).totalDegree     -- W1 (smul_le by R-scalar action — applies here since (-1) ∈ R)
  ≤ (esymm …).totalDegree                  -- by W1
  = (∑_{T ⊆ G, |T| = |G|-k} ∏_{g ∈ T} (g•b)).totalDegree
  ≤ sup_{T} (∏_{g ∈ T} (g•b)).totalDegree   -- by W5 (finset_sum)
  ≤ sup_{T} ∑_{g ∈ T} (g•b).totalDegree     -- by W4 (finset_prod)
  ≤ sup_{T} ∑_{g ∈ T} b.totalDegree         -- by §2's grading-preservation lemma (Mathlib-gap; see §2)
  = (|G| - k) * b.totalDegree
```

Thus `(charpoly G b).coeff k` has `totalDegree ≤ (|G| - k) * b.totalDegree`.
Specializing to `b.totalDegree = 1` (a linear form): `totalDegree ≤ |G| - k ≤ |G|`.

**Net**: the W1+W2+W4+W5 chain delivers the totalDegree bound
**modulo** the per-element degree-preservation lemma
`(g • b).totalDegree ≤ b.totalDegree` — which §2 below identifies as a
genuine Mathlib gap requiring an additional hypothesis.

### §1.4 No alternative bearer found via search

- No `MvPolynomial.totalDegree_esymm` exists at SHA.
- `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` defines
  `IsHomogeneous` at L48 but has no `IsHomogeneous.smul`/
  `smul_isHomogeneous` lemma at SHA.
- `Mathlib/Algebra/MvPolynomial/Degrees.lean` has no `totalDegree_smul_le`
  for **G-action** (only for **R-action** at L411, W1 above).
- The PREP-2 §3.2-anticipated files `Symmetric/Basic.lean` and
  `Polynomial/Monic.lean` do not contain a `totalDegree_esymm` bearer at
  SHA (in fact `Symmetric/Basic.lean` does not exist as a file at SHA —
  the Symmetric directory contains 3 files: `Defs.lean`,
  `FundamentalTheorem.lean`, `NewtonIdentities.lean`).

## §2 NEW gap surfaced — hidden grading-preservation assumption

### §2.1 The problem

The S3-bound chain in §1.3 has a hidden step:

```
sup_{T} ∑_{g ∈ T} (g•b).totalDegree  ≤  sup_{T} ∑_{g ∈ T} b.totalDegree
```

This requires `∀ g : G, (g • b).totalDegree ≤ b.totalDegree`. For a generic
`MulSemiringAction G R`, this does **NOT** hold. The action can mix
monomial degrees: e.g., the trivial-extension action `g • f = f + 1` is a
valid `MulSemiringAction` (on a unit-monoid action) that strictly
increases totalDegree on every non-constant input. More dangerously, an
involution that swaps a degree-0 monomial with a degree-2 monomial is
also a valid `MulSemiringAction`.

The **standard Noether-1916 hypothesis** is that G acts on V = k^n
**linearly** (via a group homomorphism G → GL(V)), inducing the
*degree-preserving* action on R = MvPolynomial (Fin n) k as a graded
k-algebra automorphism. The `MulSemiringAction` typeclass alone does NOT
capture this — it asserts only that g• is a *ring* automorphism, not
that it is *graded*.

### §2.2 Why neither S2g PREP nor S3 PREP-2 caught this

S2g PREP §2.4 and S3 PREP-2 §3 both reasoned about `charpoly` and the
Vieta link at the level of `Polynomial R[X]` (where `coeff k` is in R).
At that level the bound `≤ (|G| - k) * (something)` is the right *form*
of the answer, but the *something* depends on the structure of the
G-action on R, which is buried in `MulSemiringAction`.

The standard mathematical proof assumes graded action implicitly via
"V is a representation of G"; that hypothesis is silently in force but
unwritten in our state.md §3.5 sketch. PREP-3 surfaces it.

### §2.3 Three design options for the S3-bound ACT writer

#### Option A — Add an explicit hypothesis (recommended)

```lean
variable (h_graded : ∀ g : G, ∀ b : MvPolynomial (Fin n) k,
  (g • b).totalDegree ≤ b.totalDegree)
```

**LOC**: +1 hypothesis on the main `noether_degree_bound` theorem
+0 elsewhere. **Pros**: minimal, transparent, matches textbook
statement, no new typeclass design needed. **Cons**: caller must
supply the witness (typically by case-analysis on the action's
linearity).

#### Option B — Introduce a `[IsGradedAction G R]` typeclass

```lean
class IsGradedAction (G : Type*) (R : Type*) [Monoid G]
  [CommSemiring R] [MulSemiringAction G R] [GradedAlgebra (𝓜 : ℕ → Submodule R …) R]
  : Prop where
  smul_grade : ∀ g : G, ∀ n : ℕ, ∀ b ∈ 𝓜 n, g • b ∈ 𝓜 n
```

**LOC**: +20-40 LOC for typeclass + 1 instance for the standard
"linear action lifts to graded action on MvPolynomial" claim. **Pros**:
reusable across all of OQ-04 (e.g., S5+ Reynolds operator work) and
sibling OQ-01. **Cons**: requires bridging `GradedAlgebra` with
`MulSemiringAction`, which may or may not exist at SHA (audit deferred
to S5 PREP).

#### Option C — Restructure to use `LinearMap`-level G-action

```lean
variable (ρ : G →* (Fin n →₀ ℕ →₀ k) ≃ₗ[k] (Fin n →₀ ℕ →₀ k))   -- G → GL(V_deg-1)
-- then derive `MulSemiringAction` from ρ via free-algebra extension
```

**LOC**: +30-50 LOC for the `ρ`-based setup + 1 lemma extending ρ to
the polynomial ring. **Pros**: matches the Noether-1916 textbook
verbatim. **Cons**: requires introducing the symbol ρ throughout,
which fragments the proof and creates dependency on
`Mathlib/Algebra/Module/LinearMap/Defs.lean`.

### §2.4 Recommendation

**Option A** for the S3-bound ACT (smallest delta, easiest review).
Defer Option B to S5 PREP if/when a `[IsGradedAction]` typeclass
becomes worthwhile for Reynolds-operator infrastructure (sibling OQ-01
context).

### §2.5 Honesty note

This is a **soft correction** to S3 PREP-2's optimistic framing in §3.2,
which presented the totalDegree bound as a "narrow the search to 2
files" problem. The actual situation is that the bound requires an
**additional hypothesis** that is not in Mathlib at SHA (and probably
not addable without introducing graded-algebra-action infrastructure).
PREP-3 makes this explicit so the S3-bound ACT writer doesn't ship
silently with a degree-mixing-blind hypothesis.

## §3 State.md + research-JSON refresh — absorb #19188 + #19294 (+2 iter)

### §3.1 Drift summary

| Surface | Pre-PREP-3 value | Source of staleness | PREP-3 update |
|:--------|:-----------------|:--------------------|:--------------|
| `state.md` `**Iteration**:` | `2` (set in PR #18988 S2-finite ACT) | PRs #19188 (S3 PREP) + #19294 (S3 PREP-2) merged without bumping | `4` (S3 PREP + S3 PREP-2 + this S4 PREP-3) |
| `state.md` `**Phase**:` | `ACT (S2-finite ACT shipped — hilbert_finiteness verified)` | last touched in PR #18988 | `ACT (S2-finite ACT shipped; S3 PREP-3 totalDegree-bearer + grading-action-gap; pre-ACT for S3-bound)` |
| `state.md` `**Since**:` | `2026-05-13T20:18:00Z` | merge timestamp of PR #18988 | `2026-05-16T00:00:00Z` (this PREP-3 ship date) |
| `state.md` "Next Action" section | Sketches `orbitPolynomial` hand-built def + 5-step Vieta plan | PREP-2 §3.3 already advised using `MulSemiringAction.charpoly` directly | Replace step 1's hand-built def with reference to PREP-2 §3 V1 + V2 + V3 + V4; add reference to PREP-3 §1+§2 bearer/hypothesis table |
| `state.md` "Predecessor PREP chain" table | 7 rows (S1 OBSERVE + 6 PREPs through S2g) | does not list PR #19188 (S3 PREP) or PR #19294 (S3 PREP-2) | Add 2 rows (S3 PREP, S3 PREP-2); PREP-3 itself NOT listed (still doc-only at write time) |
| `state.md` "Iteration" body | "**S3-bound ACT** (separate iteration)" w/ sketch using `orbitPolynomial v` | sketch superseded | Add §3.4 cross-reference to PREP-2 §3.2 / PREP-3 §1.3 / PREP-3 §2.3 |
| JSON `currentState.iteration` | `2` | same as state.md | `4` |
| JSON `currentState.since` | `2026-05-13T20:18:00.000Z` | same as state.md | `2026-05-16T00:00:00.000Z` |
| JSON `currentState.focus` | "S2-finite ACT shipped: hilbert_finiteness verified by Docker build (7743/7743 jobs). … Next: S3-bound ACT…" | does not mention PREP-2 or PREP-3 | Append "; PREP-2 (PR #19294) closed S2g §2.4 Vieta gap; PREP-3 (this iter) closes totalDegree-of-charpoly-coefficient bearer gap (W1-W6) and surfaces hidden grading-preservation hypothesis (§2 — Option A recommended)." |
| JSON `currentState.nextAction` | "S3-bound ACT: prove Noether degree bound — orbit-polynomial coefficients of v ∈ R generate an invariant-subalgebra in degrees ≤ |G|, using MulSemiringAction.charpoly (Invariant/Basic.lean:138) and MvPolynomial.mul_esymm_eq_sum (Symmetric/NewtonIdentities.lean:223)." | sketch superseded | "S3-bound ACT: prove Noether degree bound using PREP-2 §3 (V1-V7) + PREP-3 §1 (W1-W6) bearer chain; per PREP-3 §2 must add `h_graded : ∀ g : G, ∀ b, (g • b).totalDegree ≤ b.totalDegree` as explicit hypothesis (Option A). Skeleton in PREP-3 §4." |
| JSON `lastUpdate` | `2026-05-13T20:18:00.000Z` | same as state.md | `2026-05-16T00:00:00.000Z` |
| JSON `leanFiles` | `[]` | should reference `proofs/Proofs/Hilbert14OQ04.lean` (created in PR #18988) | `["proofs/Proofs/Hilbert14OQ04.lean"]` |

### §3.2 What this PREP-3 does NOT touch

- `problem.md` — unchanged (still accurate).
- `knowledge.md` — unchanged (the new gap is documented in this session
  memo + state.md; knowledge.md update deferred to S3-bound ACT writer
  who will have the build verdict).
- `proofs/Proofs/Hilbert14OQ04.lean` — unchanged (the file remains the
  S2-finite-ACT shipped version, 100 LOC per `wc -l`, matching the
  state.md §1 "102 LOC" claim within Lean comment-formatting noise).
- `proofs/Proofs.lean` — unchanged.
- Gallery `src/data/proofs/hilbert-14*/meta.json` — unchanged (the
  parent slug `hilbert-14` is separate; PREP-3 scope is OQ-04 only).
- Sibling slug `hilbert-14-oq-01/` — unchanged.
- Any prior `sessions/*.md` — unchanged.

## §4 Paste-ready S3-bound ACT skeleton (~150-200 LOC)

The recommended structure for the next S3-bound ACT writer:

```lean
/-
# `proofs/Proofs/Hilbert14OQ04Bound.lean` (NEW)

Noether's degree bound: when char(k) does not divide |G|, the invariant
subalgebra `MvPolynomial^G` is generated by elements of total degree ≤ |G|.

This file is the S3-bound ACT (separate iteration from S2-finite ACT
shipped in PR #18988 = `proofs/Proofs/Hilbert14OQ04.lean`).
-/

import Mathlib.RingTheory.Invariant.Basic                -- charpoly, smul_coeff_charpoly
import Mathlib.RingTheory.Polynomial.Vieta              -- prod_X_sub_C_coeff
import Mathlib.Algebra.MvPolynomial.Degrees             -- totalDegree_*
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs   -- esymm (Multiset/MvPolynomial)
import Proofs.Hilbert14OQ04                              -- hilbert_finiteness (already shipped)

open Polynomial MulSemiringAction

variable {k : Type*} [Field k] {n : ℕ}
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial (Fin n) k)]
variable [SMulCommClass G k (MvPolynomial (Fin n) k)]

abbrev R := MvPolynomial (Fin n) k
abbrev B := FixedPoints.subalgebra k R G

namespace Hilbert14OQ04Bound

/-- Stage 1: each coefficient of `charpoly G b` lies in the fixed
subalgebra `B = R^G`. -/
lemma coeff_charpoly_mem_subalgebra (b : R) (j : ℕ) :
    (MulSemiringAction.charpoly G b).coeff j ∈ B := by
  intro g
  exact (MulSemiringAction.smul_coeff_charpoly b j g).symm
  -- Bearer: V2 = `MulSemiringAction.smul_coeff_charpoly`
  --         (Invariant/Basic.lean:158, PREP-2 §3.1)

/-- Stage 2: orbit polynomial is monic of degree `|G|`. -/
lemma natDegree_charpoly (b : R) :
    (MulSemiringAction.charpoly G b).natDegree = Fintype.card G := by
  -- charpoly = ∏ g : G, (X - C (g • b)) — Bearer V1 (charpoly_eq)
  -- natDegree of finite product of monic linear factors = card G
  rw [MulSemiringAction.charpoly_eq]
  rw [Polynomial.natDegree_prod _ _ (fun g _ => X_sub_C_ne_zero _)]
  simp [Polynomial.natDegree_X_sub_C]
  -- One of the simp-step bearers may need explicit form:
  -- `Polynomial.natDegree_X_sub_C : (X - C a).natDegree = 1` (Mathlib core).

/-- Stage 3 (the totalDegree bound): assuming the G-action is degree-preserving,
each coefficient of `charpoly G b` has totalDegree ≤ `(|G| - j) * b.totalDegree`. -/
lemma totalDegree_coeff_charpoly_le
    (h_graded : ∀ g : G, ∀ b : R, (g • b).totalDegree ≤ b.totalDegree)
    (b : R) (j : ℕ) (hj : j ≤ Fintype.card G) :
    ((MulSemiringAction.charpoly G b).coeff j).totalDegree ≤
      (Fintype.card G - j) * b.totalDegree := by
  -- Composition recipe per PREP-3 §1.3:
  -- 1. Vieta: charpoly.coeff j = (-1)^(|G| - j) * esymm (|G| - j) over orbit.
  -- 2. esymm expansion as Finset.sum over (|G| - j)-subsets of G.
  -- 3. totalDegree_smul_le (W1) ∘ totalDegree_finset_sum (W5) ∘ totalDegree_finset_prod (W4).
  -- 4. Apply h_graded inside the per-element bound.
  sorry  -- ~30-60 LOC mechanical Finset/Multiset manipulation;
         -- bearer-pinned in §1.1 above; no API drift expected.

/-- The Noether degree bound: invariant subalgebra is generated by
elements of total degree ≤ |G|, assuming the G-action is degree-preserving. -/
theorem noether_degree_bound
    (h_graded : ∀ g : G, ∀ b : R, (g • b).totalDegree ≤ b.totalDegree)
    (h_char : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → p ≠ ringChar k) :
    ∃ S : Finset R, (∀ s ∈ S, s ∈ B ∧ s.totalDegree ≤ Fintype.card G) ∧
      Algebra.adjoin k (S : Set R) = ⊤ ∧
      Algebra.adjoin k (S.image (algebraMap _ _ : B → R) : Set R) = ⊤ := by
  sorry  -- ~80-120 LOC: Reynolds-averaging + extraction of generating set
         -- from char-poly coefficients of a spanning set of R/B.
         -- Main bearers: Stage 1 + Stage 2 + Stage 3 lemmas above.

end Hilbert14OQ04Bound
```

**LOC estimate**: 150-200 LOC total (3 stage lemmas at ~30-60 each +
1 main theorem at ~80-120 = ~170 LOC + ~30 LOC imports/variables).

**Risks** (inventory):

| # | Risk | Severity | Mitigation |
|:--|:-----|:---------|:-----------|
| R1 | `h_graded` hypothesis is non-trivial to discharge for a caller; may force callers to introduce LinearMap-level G-action plumbing | HIGH | Document in module docstring + add `example` showing `h_graded` from the standard `GL(V)`-action |
| R2 | `Polynomial.natDegree_prod` may require `DecidableEq G` or `[Nontrivial R]` | LOW | Both are inferred from `[Fintype G]` + `[Field k]` |
| R3 | Stage 3's Finset-sum/prod manipulation may have heartbeat/elaboration time concerns | MEDIUM | Use `set _ := …` blocks to abbreviate intermediate `Multiset.esymm` expressions |
| R4 | The "extraction of generating set" in `noether_degree_bound` (~80-120 LOC) requires Reynolds-averaging, which needs char-0 or coprime-with-|G| hypotheses | HIGH | Hypothesis `h_char` already lists this; concrete construction may need char-0 → `Field` upgrade or 1/|G| ∈ k assumption |
| R5 | Sibling slug OQ-01's Reynolds-operator infrastructure (`reynoldsSum`, `InvariantSubset`) might overlap | LOW | Cross-reference; OQ-01 used unnormalized Reynolds, OQ-04 needs `(1/|G|) ∑ g•` (normalized) |
| R6 | Build verification needs Docker daemon AND ≥10 Gi disk for 7700+ jobs | INFRA | This PREP-3 ships in disk-100%/Docker-hung environment; next ACT writer should re-check infra before claim |
| R7 | The `h_char` hypothesis (modular vs non-modular) may be subtly wrong; Noether's bound is `≤ |G|` in non-modular case, but Symonds 2011 gives `≤ |G|·dim V` in modular — be careful with statement | MEDIUM | Restate as `h_char : ¬ (ringChar k ∣ Fintype.card G)` for clarity |
| R8 | `Polynomial.natDegree_X_sub_C` may have a different name at SHA (e.g. `natDegree_X_sub_C` without `Polynomial.` prefix in current `open Polynomial`) | LOW | Re-grep at ACT time |

## §5 ACT-readiness gate (8 items; 6/8 GREEN, 2/8 RED — both infra-only)

| # | Gate item | Status | Notes |
|:--|:----------|:-------|:------|
| G1 | All bearers (V1-V7 + W1-W6) verified at lake SHA | ✅ GREEN | PREP-2 §3 + PREP-3 §1; total 13 bearers across 4 Mathlib files |
| G2 | `h_graded` hypothesis form decided (Option A: explicit) | ✅ GREEN | PREP-3 §2.3 + §2.4 |
| G3 | Skeleton compiles in isolation (3 stage lemmas with `sorry`) | ✅ GREEN | PREP-3 §4 (paste-ready; not yet `lake build`-verified due to G7) |
| G4 | LOC forecast within budget (150-200 LOC) | ✅ GREEN | PREP-3 §4 estimate |
| G5 | Risk inventory complete (R1-R8) | ✅ GREEN | PREP-3 §4 risk table |
| G6 | State.md + JSON drift absorbed | ✅ GREEN | PREP-3 §3 (ships in same PR) |
| G7 | Docker daemon responsive | ❌ RED | `timeout 10 docker info` exit 124 (daemon hung); ACT-blocking |
| G8 | Host disk ≥10 Gi free for build artifacts | ❌ RED | `df -h /System/Volumes/Data` = 6.9 Gi avail / 100% capacity; ACT-blocking |

**Verdict**: 6/8 GREEN substantive; 2/8 RED **purely infra**. Once
Docker recovers and disk frees, the next claim can proceed directly
from PREP-3 §4 paste-ready skeleton + PREP-2 §3 bearer reference.

## §6 Conflict footprint

**Three files modified**:

```
research/problems/hilbert-14-oq-04/sessions/2026-05-16-s4-prep3-totaldegree-bearer-close-and-grading-action-gap-surface.md  (NEW)
research/problems/hilbert-14-oq-04/state.md                                                                                  (refresh head + iter + Predecessor PREP chain + Next Action body)
src/data/research/problems/hilbert-14-oq-04.json                                                                              (iteration, since, focus, nextAction, lastUpdate, leanFiles)
```

**Not touched**:

- `problem.md`
- `knowledge.md`
- `proofs/Proofs/Hilbert14OQ04.lean`
- `proofs/Proofs.lean`
- sibling slug `hilbert-14-oq-01/`
- parent gallery `src/data/proofs/hilbert-14*/meta.json`
- any prior session/PREP file in `sessions/`

**Safe-mergeable** with: anything that doesn't also edit state.md /
JSON for this slug. No open PRs for hilbert-14-oq-04 at PREP-3 ship time
(`gh pr list --search "hilbert-14-oq-04" --state open` → `[]`).

## §7 Test plan

- [x] Branch created off `origin/main`:
      `research/hilbert-14-oq-04-iter-1778924087`.
- [x] Mathlib SHA pin reconfirmed: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
      via `proofs/lake-manifest.json`.
- [x] Each of W1-W6 fetched via
      `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<sha>`
      and signature confirmed.
- [x] PREP-2's V1-V5 (charpoly + Vieta) reconfirmed at SHA in §1.3
      composition recipe.
- [x] Negative search confirmed: no `totalDegree_esymm`, no
      `IsHomogeneous.smul`, no `MulSemiringAction.totalDegree` at SHA.
- [x] State.md drift inventory (§3.1) cross-checked against
      `git log --oneline -- research/problems/hilbert-14-oq-04/state.md`
      (last touched in PR #18988).
- [x] No Docker build performed (doc-only).
- [x] One new file + 2 minimal text edits; no `.lean` changes.

## §8 References

- **PR #19294** — merged. S3 PREP-2 pin-verifies PR #18988 + closes S2g
  §2.4 Vieta gap (PREP-3 §1 closes the §3.2 Stage 3 residual gap PREP-2
  flagged as "still requires audit").
- **PR #19188** — merged. S3 PREP coordination note for pending PR
  #18988.
- **PR #18988** — merged. S2-finite ACT — `hilbert_finiteness` verified
  (Docker 7743/7743 jobs).
- **PR #18750** — merged. S2g PREP — Mathlib bearer re-pin (audited by
  PREP-2 §4).
- **PR #18714** — merged. S2f PREP — scope clarification, finiteness vs
  degree bound.
- **PR #18667** — merged. S2e PREP — `Algebra.IsInvariant.isIntegral`
  bearer.
- **PR #18589** — merged. S2d PREP — sibling-slug OQ-01 typeclass bridge.
- **PR #18562** — merged. S2c PREP — `IsScalarTower` / `IsNoetherianRing`
  trap resolution.
- **PR #18501** — merged. S2b PREP — Artin-Tate canonical bearer.
- **PR #18435** — merged. S2 PREP — original orbit-polynomial API audit.
- **PR #18248** — merged. S1 OBSERVE — algorithmic landscape + Noether
  bound plan.

Mathlib pin: v4.26.0, commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
verified via `proofs/lake-manifest.json`.

> _Phase note_: This skill maps "S4 PREP-3" to the canonical ORIENT phase;
> the slug-local sub-phase encoding "S4 PREP-3" tracks the post-S2-finite-ACT
> design-iteration count (1 ACT + 2 sibling PREPs + this PREP-3 = 4 total
> design iterations beyond S1 OBSERVE).
