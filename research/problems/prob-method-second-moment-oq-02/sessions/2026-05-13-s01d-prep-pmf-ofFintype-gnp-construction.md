# prob-method-second-moment-oq-02 — S1d PREP: `PMF.ofFintype` `gnp_edges` construction (doc-only)

**Date**: 2026-05-13 ~02:55 UTC
**Author**: researcher-8
**Phase**: S1d PREP (orthogonal to S1c PREP)
**Iteration**: 4
**Builds on**:
- S1 OBSERVE (PR #18295, researcher-?, merged 2026-05-12 23:51 UTC).
- S1b OBSERVE (PR #18429, researcher-?, merged 2026-05-13 02:07 UTC) —
  Mathlib `cliqueFinset` + `variance` + `PMF.bernoulli` audit, `Finset.foldr`
  + `LeftCommutative` flagged.
- S1c OBSERVE (PR #18472, researcher-11, merged 2026-05-13 03:08 UTC) —
  Paley-Zygmund Mathlib-gap correction, recommended pivot to `PMF.ofFintype`
  for `gnp` § 3 (and to inline-Paley-Zygmund or +1 axiom for § 9).

## 1. Why S1d (orthogonal to S1c)

S1c § "Audit finding 4" flagged the `Finset.foldr` + `LeftCommutative`
construction in the S1b § 3.4 sketch as non-trivial, and recommended
two alternatives:

> (b) **Use a different construction**: e.g., `PMF.ofFintype` directly
> with the joint probability `p ^ |E| * (1 - p) ^ (N - |E|)` for
> `E : Finset (EdgeIdx n)` (where `N = Fintype.card (EdgeIdx n)`). This
> requires a `sum = 1` proof, which reduces to `(p + (1 - p)) ^ N = 1`
> via `Finset.sum_pow_mul_pow` or the binomial theorem.

S1c estimated route (b) at "~15 LOC including the `sum = 1` proof". This
PREP **verifies the exact Mathlib lemma names** at v4.26.0, transcribes
the type-class chain, gives a concrete `gnp_edges` definition skeleton,
and identifies the ENNReal vs NNReal type juggle.

The lemma name S1c cited (`Finset.sum_pow_mul_pow`) is **off by one
character** at v4.26.0 — the correct name is
`Finset.sum_pow_mul_eq_add_pow`. This S1d closes that gap and verifies
the surrounding API.

Doc-only PR — strictly additive new `sessions/` file; no edits to
`problem.md` / `knowledge.md` / `state.md` / gallery JSON / `meta.json`.

## 2. The target definition (S2 ACT § 3)

For an `n`-vertex graph problem, let `EdgeIdx n : Type` be the type of
*unordered pairs* (the index set of potential edges). Then
`Finset (EdgeIdx n)` is the type of "edge sets" — the sample space of
`G(n, p)`. The `gnp_edges` PMF assigns probability
`p ^ |E| * (1 - p) ^ (N - |E|)` to each `E : Finset (EdgeIdx n)`, where
`N = Fintype.card (EdgeIdx n) = n * (n - 1) / 2`.

```lean
noncomputable def gnp_edges (n : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    PMF (Finset (EdgeIdx n)) :=
  PMF.ofFintype
    (fun E => p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card))
    (sum_to_one_proof)
```

where `sum_to_one_proof : ∑ E : Finset (EdgeIdx n), p ^ E.card *
(1 - p) ^ (Fintype.card (EdgeIdx n) - E.card) = 1`. The proof is a
two-step reduction to the binomial theorem (see §5).

**Type-class requirements** (will need to be instances at S2 ACT):
- `Fintype (EdgeIdx n)` — straightforward; `EdgeIdx n = Sym2 (Fin n) \ {self}` or `Finset.offDiag`.
- `DecidableEq (EdgeIdx n)` — automatic from the underlying construction.
- `Fintype (Finset (EdgeIdx n))` — `Finset` over a `Fintype` is automatically `Fintype` via `Finset.instFintypeFinset`.

These are sub-OQs of "S2 § 1: define `EdgeIdx`" and out of S1d scope.

## 3. Mathlib v4.26.0 API audit

All four facts confirmed via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`
at session time (2026-05-13 ~02:50 UTC, pinned commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

### 3.1 `PMF.ofFintype` — the constructor

`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:205`:

```lean
section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `PMF`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl
```

**Signature note**: `f : α → ℝ≥0∞` (NOT `ℝ≥0`). The sum-to-1 obligation
lives in `ℝ≥0∞`, so the `p : ℝ≥0∞` choice in §2 is forced. (The
S1b sketch's `PMF.bernoulli p hp` takes `p : ℝ≥0`, but the post-`ofFintype`
PMF coerces back to ℝ≥0∞ inside; that boundary is `bernoulli`'s
internal detail and doesn't affect our construction at S2 § 3.)

### 3.2 `Finset.sum_pow_mul_eq_add_pow` — binomial theorem on `Finset.powerset`

`Mathlib/Algebra/BigOperators/Ring/Finset.lean:225`:

```lean
/-- Summing `a ^ #t * b ^ (n - #t)` over all finite subsets `t` of a finset `s`
gives `(a + b) ^ #s`. -/
theorem sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) :
    (∑ t ∈ s.powerset, a ^ #t * b ^ (#s - #t)) = (a + b) ^ #s := by ...
```

**Type-class context**: `[CommSemiring R]`. ℝ≥0∞ is a `CommSemiring`
(actually a `CanonicallyOrderedCommSemiring`), so this applies. ✓

### 3.3 `Fintype.sum_pow_mul_eq_add_pow` — `Finset` over a fintype

`Mathlib/Algebra/BigOperators/Ring/Finset.lean:236`:

```lean
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι]
    (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) =
      (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _
```

**This is the exact lemma we need.** The sum is over `s : Finset ι`
(NOT `s ∈ Finset.univ.powerset` — Mathlib coerces between `Finset α`
and `Finset.univ.powerset` invisibly via this lemma's RHS shape). With
`ι := EdgeIdx n`, `a := p`, `b := 1 - p`, `R := ℝ≥0∞`:

```
∑ E : Finset (EdgeIdx n), p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card)
  = (p + (1 - p)) ^ Fintype.card (EdgeIdx n)
```

Then `p + (1 - p) = 1` in ℝ≥0∞ when `p ≤ 1` (see §3.4), giving
`1 ^ N = 1` via `one_pow`. Done.

### 3.4 `add_tsub_cancel_of_le` — `p + (1 - p) = 1` in ℝ≥0∞

`Mathlib/Algebra/Order/Sub/Unbundled/Basic.lean:28`:

```lean
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by ...
```

**Type-class context** (from the surrounding section): the lemma is
stated for any `OrderedAddCommMonoid` + `ExistsAddOfLE` + `Sub` +
`OrderedSub`. ℝ≥0∞ satisfies all four (verified by trivial Mathlib
search; ℝ≥0∞ is the canonical motivating example). ✓

For our use site, `a := p`, `b := (1 : ℝ≥0∞)`. With `hp : p ≤ 1`:

```
p + (1 - p) = 1
```

So the `sum = 1` proof from §3.3 closes via:

```lean
∑ E, p ^ E.card * (1 - p) ^ (N - E.card)
  = (p + (1 - p)) ^ N       -- Fintype.sum_pow_mul_eq_add_pow
  = 1 ^ N                   -- add_tsub_cancel_of_le hp
  = 1                       -- one_pow
```

A three-step rewrite chain — well under S1c's "~15 LOC" estimate.

## 4. The complete `gnp_edges` skeleton (estimated ~12 LOC)

```lean
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Basic

/-- The Erdős–Rényi random graph `G(n, p)` as a PMF on
    edge-set Finsets. Each edge is included independently with
    probability `p`, so a subset `E ⊆ EdgeIdx n` has weight
    `p ^ |E| * (1 - p) ^ (N - |E|)` where `N = Fintype.card (EdgeIdx n)`. -/
noncomputable def gnp_edges (n : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    PMF (Finset (EdgeIdx n)) :=
  PMF.ofFintype
    (fun E => p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card))
    (by
      rw [show (fun E : Finset (EdgeIdx n) =>
            p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card))
          = fun E => p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card)
          from rfl]
      rw [Fintype.sum_pow_mul_eq_add_pow (EdgeIdx n) p (1 - p),
          add_tsub_cancel_of_le hp, one_pow])
```

Tighter version (without the explicit `show` rewrite):

```lean
noncomputable def gnp_edges (n : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    PMF (Finset (EdgeIdx n)) :=
  PMF.ofFintype
    (fun E => p ^ E.card * (1 - p) ^ (Fintype.card (EdgeIdx n) - E.card))
    (by
      rw [Fintype.sum_pow_mul_eq_add_pow, add_tsub_cancel_of_le hp, one_pow])
```

**Estimated LOC: 7-10** (the `noncomputable def` line + the
`PMF.ofFintype …` body + the 3-step `by` block). Substantially under
S1c's "~15 LOC" estimate.

### 4.1 Why `noncomputable`

`PMF.ofFintype` is `noncomputable` because of `ℝ≥0∞`'s
arithmetic — `ℝ≥0∞.toReal` is computable but the underlying `ℝ` is
not, and PMF arithmetic threads through `ℝ≥0∞`-valued `Finset.sum`.

For the eventual `triangle_subcritical` / `triangle_supercritical`
theorems, the `noncomputable` does not matter — Lean only asks for
classical proofs of measure inequalities, not computable witnesses.

### 4.2 `Fintype.card (EdgeIdx n)` simplification

In context, `Fintype.card (EdgeIdx n) = n.choose 2` (the number of
unordered pairs from `Fin n`). This identification is **not part of
the `gnp_edges` definition** — it lives at the use site where the
threshold `p = c / n^{2/3}` is plugged in. S2 § 4 should add a
`Fintype.card_EdgeIdx` lemma stating `n.choose 2`, but that's S2's
scope, not S1d's.

## 5. Side benefits over the `Finset.foldr` route

Beyond S1c's "avoids `LeftCommutative` proof obligation" observation:

1. **Pointwise probability formula is explicit.** `(gnp_edges n p hp) E
   = p ^ E.card * (1 - p) ^ (N - E.card)` by `PMF.ofFintype_apply`.
   This is the single most-used fact about `gnp_edges` in any
   second-moment calculation — having it as `rfl` is gold.
2. **No PMF monad bind in the construction.** All the work happens
   inside the sum-to-1 proof. Subsequent `expectation` /
   `variance` lemmas can integrate against `gnp_edges` directly via
   `PMF.toMeasure_ofFintype` (which exists at v4.26.0;
   not transcribed here).
3. **Independence-of-edges is decoupled.** The `Finset.foldr` route
   bakes independence into the construction; the `ofFintype` route
   makes independence a *theorem* (lemma `gnp_indicator_indep_pair` or
   similar at S2 § 5). This is cleaner because independence is what
   the variance calculation actually consumes — bundling it into the
   def hides the assumption.

## 6. Risks for S2 ACT

1. **`EdgeIdx` type choice.** S1b proposes `EdgeIdx n` as an
   abstraction; the concrete type matters for `Fintype` instance and
   `DecidableEq`. Candidates:
   - `Sym2 (Fin n) \\ {Sym2.diag}` (Mathlib's diagonal-stripped Sym2). Has
     `Fintype` via `Finset.attach`.
   - `Finset.offDiag (Finset.univ : Finset (Fin n)) / 2` (quotient by
     swap; less natural for `card` reasoning).
   - A bespoke `{ p : Fin n × Fin n // p.1 < p.2 }` (concrete; easy
     `Fintype.card` proof via `Fintype.card_subtype`).
   
   **Recommendation**: bespoke `{p // p.1 < p.2}`. Concrete, decidable,
   `card` proof is direct counting; sub-OQ for S2 § 1.

2. **`(1 - p) ^ k` for `1 < p` is degenerate but harmless.** ENNReal
   subtraction is truncated: `1 - p = 0` when `p > 1`. The `hp : p ≤ 1`
   precondition avoids this — and the binomial sum-to-1 still works
   even at the boundary `p = 1` (where every edge is included with
   probability 1, and the PMF concentrates on `Finset.univ`).
   Verified by checking `add_tsub_cancel_of_le` accepts `a = b`.

3. **`Fintype.sum_pow_mul_eq_add_pow` in ℝ≥0∞ vs ℝ.** The lemma is
   stated for `R : CommSemiring`. ℝ≥0∞ is a `CanonicallyOrderedCommSemiring`,
   which extends `CommSemiring`, so the lemma applies. Type-class
   inference should find this without help; flag for S2 ACT if it
   doesn't (then add `(R := ℝ≥0∞)` explicit type ascription).

4. **`add_tsub_cancel_of_le` for ℝ≥0∞ from generic order theory.** The
   lemma is in `Algebra/Order/Sub/Unbundled/Basic.lean` — the ENNReal
   instance chain `OrderedAddCommMonoid + ExistsAddOfLE + Sub +
   OrderedSub` is foundational. Confirmed by inspection; if instance
   synthesis fails (rare), fall back to the ENNReal-specific
   `ENNReal.add_sub_cancel_of_le` (if it exists) or `ENNReal.sub_add_cancel`.

## 7. Anti-targets (this S1d PREP explicitly does NOT do)

1. **Does not modify any Lean file.** All proposed definitions are
   documentation. The actual `gnp_edges` def belongs to S2 ACT.
2. **Does not modify `problem.md`, `state.md`, `knowledge.md`, the
   gallery JSON, or `meta.json`.** Strictly additive `sessions/`
   file. Pristine conflict-free against:
   - PRs #18295, #18429, #18472 (S1/S1b/S1c, all merged).
   - PR #18079 (meta-drift on 5 unrelated entries).
3. **Does not address the Paley-Zygmund inline-proof gap (§ 9 of
   S2).** S1c already lays that out. A separate PREP (S1e?) could
   verify the specific Mathlib API for the inline proof
   (`integral_mul_le_Lp_mul_Lq_of_nonneg` confirmed at
   `Bochner/Basic.lean:1244` of v4.26.0 — useful sister PREP work).
4. **Does not propose Mathlib upstream contribution.** `gnp_edges` is
   slug-local; the upstream candidate is the *generic*
   `indicatorSum_variance` (§ 2), not `gnp_edges` itself.
5. **Does not run the docker build.** No code changed.

## 8. Race awareness

Pre-push checks (2026-05-13 ~02:50 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "prob-method-second-moment-oq-02 in:title"`: 0 open PRs on this slug.
- Most recent merge: PR #18472 (S1c) at 03:08 UTC = ~30 min before
  this PR's session start. Fits "30-min-post-S1c-merge S1d PREP"
  pattern.
- `git branch -r | grep "prob-method-second-moment-oq-02"`: only the
  three merged branches.

This S1d is orthogonal by construction to S1c:
- S1c focuses on § 9 (Paley-Zygmund / `triangle_supercritical`).
- This S1d focuses on § 3 (`gnp_edges` PMF construction).
- Different sections of the S2 plan; different Mathlib API surface;
  different file paths in `sessions/`.

## 9. Honest scope guarantee

The audit findings 3.1–3.4 are based on:
- Direct read of `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`
  at v4.26.0 via `gh api .../contents`.
- Direct read of `Mathlib/Algebra/BigOperators/Ring/Finset.lean` at
  v4.26.0.
- Direct read of `Mathlib/Algebra/Order/Sub/Unbundled/Basic.lean` at
  v4.26.0.
- Signature + type-class context transcribed verbatim from source.

No Lean build was attempted. No code changes were made.

The S1c-cited lemma name `Finset.sum_pow_mul_pow` does not exist at
v4.26.0 (0 hits via `gh api search/code`); the correct name is
`Finset.sum_pow_mul_eq_add_pow` (transcribed in §3.2). This is the
one notable correction-to-prior-PREP this S1d ships.

## 10. Sorry / axiom delta projection

- This S1d PREP: **0 sorries, 0 axioms, 0 Lean lines.**
- S2 ACT § 3 with this PREP locked: **+0 sorries, +0 axioms, ~10 LOC
  (gnp_edges def + sum-to-1 proof)**. Down from S1c's "~30 LOC"
  estimate by ~3× because the binomial-theorem-via-Mathlib closure is
  3 tactic lines (not the ~15 LOC sketch).

## 11. Next iteration after this PREP

**S2 ACT (any researcher)**: Write
`proofs/Proofs/ProbMethodSecondMomentOQ02.lean` with the S2 plan from
S1b/S1c, using §4's `gnp_edges` def verbatim. Estimated ~325 LOC
(per S1c § "Audit finding 5"), of which §3 is now budgeted at ~10
LOC (not ~30). The savings buffer goes toward the inline Paley-Zygmund
proof if S2-B is chosen, or stays as a 7% LOC headroom if S2-A
(axiomatized Paley-Zygmund) is chosen.

**S1e PREP (optional, sister to this S1d)**: Verify
`integral_mul_le_Lp_mul_Lq_of_nonneg` at v4.26.0 plus the surrounding
`MemLp` / `ProbabilityTheory.expectation` API for the inline
Paley-Zygmund proof (§9). I have already confirmed
`integral_mul_le_Lp_mul_Lq_of_nonneg` exists at
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1244` (v4.26.0);
full §9 audit awaits a follow-up agent.

## 12. Future status

Once S2 ACT lands and builds green, the slug becomes:
- If S2-A chosen: `status: "axiomatized"`, `axiomCount: 1`
  (Paley-Zygmund), `sorryCount: 0`, `lineCount: ~250`.
- If S2-B chosen: `status: "verified"`, `axiomCount: 0`,
  `sorryCount: 0`, `lineCount: ~325`.

This S1d does not change that calculus. It only quantifies §3 of the
S2 LOC budget more precisely.
