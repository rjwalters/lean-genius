# S4 PREP — Besicovitch (1940) sibling slug design memo

**Date**: 2026-05-12
**Researcher**: researcher-12
**Phase**: PREP (scoping for the **future** sibling slug
`sqrt2-plus-sqrt3-irrational-oq-02`; does **not** modify any `.lean`
file and does **not** create the sibling slug — that is a seeker job)
**Conditional on**: state.md S4 (stretch) bullet, problem.md
"Bridge to Besicovitch" subsection, and parent gallery
`sqrt2-plus-sqrt3-irrational` openQuestions[1].

This document is **doc-only**. It scopes the formalisation of
Besicovitch (1940) — the parent gallery's open question OQ-02 — as
a complement to the three-summand instance closed by the in-flight
S2 ACT (PR #18369). The deliverable is a **design memo**, not Lean
code; the goal is to lower the activation energy for whoever
eventually claims `sqrt2-plus-sqrt3-irrational-oq-02`.

The memo is intentionally tactical: it surveys three Lean encodings,
ranks them by Mathlib coverage, sketches the inductive proof
skeleton, and identifies the single missing Mathlib lemma blocking
the most direct route.

## 1. Statement of Besicovitch (1940)

**Theorem** (Besicovitch, *J. London Math. Soc.* **15** (1940), 3–6).
Let `a₁, …, aₙ` be distinct positive squarefree integers, with all
`aᵢ > 1`. Then `√a₁, …, √aₙ` are **linearly independent over ℚ**.

Equivalently: the **2ⁿ** Boolean-subset products

```
{ √(∏ a_i : i ∈ S) : S ⊆ {1, …, n} }      (1)
```

are linearly independent over ℚ — i.e. they form a ℚ-basis of the
field

```
K_n := ℚ(√a₁, …, √aₙ)                     (2)
```

so `[K_n : ℚ] = 2ⁿ`.

**Corollary (3-summand instance, this entry's S2 target).**
`a = 2, b = 3, c = 5` are squarefree, distinct, all `> 1`; therefore
`{1, √2, √3, √5, √6, √10, √15, √30}` is ℚ-lin-ind, hence in
particular `√2 + √3 + √5 ∉ ℚ`.

(That corollary is what PR #18369 proves directly, bypassing the
inductive Besicovitch route; this memo plans the inductive route as
the OQ-02 deliverable.)

## 2. Three Lean encodings — ranked

We compared three candidate Lean statements for the Besicovitch
theorem. Each has different Mathlib coverage and different proof
strategy. Ranked by **formalisation tractability** (least → most
work):

### Encoding A — *Sum-of-radicals never rational unless trivial*

```lean
/-- Besicovitch (1940), positive-coefficient form. -/
theorem besicovitch_sum_irrational
    (n : ℕ) (a : Fin n → ℕ)
    (h_sf : ∀ i, Squarefree (a i))
    (h_gt1 : ∀ i, 1 < a i)
    (h_distinct : Function.Injective a)
    (r : Fin n → ℚ)
    (h_nontrivial : ∃ i, r i ≠ 0) :
    Irrational (∑ i, (r i : ℝ) * Real.sqrt (a i)) := …
```

**Pros:** Mirrors the 3-summand target with `r i = 1` and `n = 3`;
proof reduces to a single `Irrational` discharge.

**Cons:** Requires the full inductive lift (n+1 case from n case);
no Mathlib infrastructure on linear-independence-as-irrationality.

### Encoding B — *Linear independence of √-vectors over ℚ*

```lean
/-- Besicovitch (1940), linear-algebra form. -/
theorem besicovitch_linearIndependent
    (n : ℕ) (a : Fin n → ℕ)
    (h_sf : ∀ i, Squarefree (a i))
    (h_gt1 : ∀ i, 1 < a i)
    (h_distinct : Function.Injective a) :
    LinearIndependent ℚ (fun i : Fin n => (Real.sqrt (a i) : ℝ)) := …
```

**Pros:** Maps onto Mathlib's `LinearIndependent` infrastructure
(`Mathlib.LinearAlgebra.LinearIndependent.Basic`), reuses tooling
like `LinearIndependent.image`, `linearIndependent_iff`, etc.
Mathlib already has a sister statement for `Real.log α_i` in
`Proofs/AlgebraicNumbersCountableOQ04.lean` (the `LinearIndependent
ℚ (fun i => Real.log (α i))` shape) — so the *vocabulary* exists.

**Cons:** Cleanest *statement* but the proof still requires the
inductive subset-Galois argument from §4 below. Encoding A is
equivalent (via `linearIndependent_iff`) but cheaper to apply at
call sites.

### Encoding C — *Field degree `[K_n : ℚ] = 2ⁿ`*

```lean
/-- Besicovitch (1940), field-theoretic form. -/
theorem besicovitch_finrank
    (n : ℕ) (a : Fin n → ℕ)
    (h_sf : ∀ i, Squarefree (a i))
    (h_gt1 : ∀ i, 1 < a i)
    (h_distinct : Function.Injective a) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      (Set.range (fun i : Fin n => (Real.sqrt (a i) : ℝ)))) = 2 ^ n := …
```

**Pros:** The "right" abstract statement; matches the textbook
proof closest (Galois group ≅ `(ℤ/2ℤ)ⁿ`, then dimension counting).
Sister minpoly proof `Proofs/Sqrt2PlusSqrt3IrrationalOQ03.lean`
already exhibits the `adjoin … finrank = 4` pattern for n=2 in
`adjoin_sqrt2_plus_sqrt3_finrank` (verified, 0 sorries, 0 axioms).

**Cons:** Requires the **most** Mathlib machinery: `IntermediateField.adjoin`,
`Module.finrank`, `IsGalois`, plus the Kummer-extension tower
`ℚ ⊂ ℚ(√a₁) ⊂ ℚ(√a₁, √a₂) ⊂ …`. Each step needs
`minpoly_sqrt_squarefree` (likely missing — see §6).

### Recommendation

**Start with Encoding B (linear independence).** It is the natural
input shape for downstream applications (any "α is irrational"
corollary unwraps via `linearIndependent_iff` or
`LinearIndependent.ne_zero`), and the proof can route through
**either** Encoding A's induction **or** Encoding C's field-degree
counting, whichever is cheaper for a given subset structure.

A subsequent `oq-02b` slug, if desired, can lift Encoding B to
Encoding C via `Module.finrank_eq_card_basis` once Encoding B is
in place.

## 3. Concrete k = 3 instance plan (OQ-02 first iteration)

The first iteration of `sqrt2-plus-sqrt3-irrational-oq-02` should
prove the **k = 3 special case**:

```lean
/-- Besicovitch (1940), three-summand instance. -/
theorem besicovitch_three
    {a b c : ℕ}
    (h_sf_a : Squarefree a) (h_sf_b : Squarefree b)
    (h_sf_c : Squarefree c) (h_sf_ab : Squarefree (a * b))
    (h_sf_ac : Squarefree (a * c)) (h_sf_bc : Squarefree (b * c))
    (h_sf_abc : Squarefree (a * b * c))
    (h_gt1_a : 1 < a) (h_gt1_b : 1 < b) (h_gt1_c : 1 < c)
    (h_ne_ab : a ≠ b) (h_ne_ac : a ≠ c) (h_ne_bc : b ≠ c) :
    LinearIndependent ℚ
      (fun i : Fin 3 => ![(Real.sqrt a : ℝ),
                          Real.sqrt b, Real.sqrt c] i) := …
```

(One can equivalently bundle the squarefreeness of products into a
`Squarefree.prod_distinct` hypothesis if Mathlib has it; see §6.)

**Strategy (mirrors the OQ-01 S2 quartic identity, generalised):**

1. **Setup.** Assume `r₁ · √a + r₂ · √b + r₃ · √c = 0` with
   `rᵢ ∈ ℚ`, not all zero.
2. **Isolation by iterated squaring.** Move `r₃ √c` to RHS, square:
   ```
   (r₁ √a + r₂ √b)² = r₃² c
   r₁² a + 2 r₁ r₂ √(ab) + r₂² b = r₃² c
   ```
   so `√(ab) ∈ ℚ` unless `r₁ r₂ = 0`.
3. **Squarefreeness contradiction.** `Squarefree (a * b)` ⇒
   `¬ IsSquare (a * b)` ⇒ `√(ab) ∉ ℚ` via
   `irrational_sqrt_natCast_iff`. Hence `r₁ r₂ = 0`. Case-split.
4. **Recursion.** Each branch reduces to a 2-summand statement,
   already discharged by the parent `sqrt2-plus-sqrt3-irrational`
   gallery proof (or a slight generalisation).

The plan reuses **exactly** the squaring-isolation technique from
OQ-01 — Besicovitch's own induction step.

**Estimated Lean LOC for `besicovitch_three`**: ~120 lines, plus
~60 lines for two intermediate `besicovitch_two_general` and
`besicovitch_one_squarefree` lemmas. Total ~200 LOC,
0 sorries / 0 axioms targeted.

## 4. Full inductive proof skeleton (Encoding B, n general)

```lean
/-- Inductive proof of Besicovitch's linear-independence theorem. -/
theorem besicovitch_linearIndependent_induction
    (n : ℕ) :
    ∀ (a : Fin n → ℕ),
      (∀ i, Squarefree (a i)) → (∀ i, 1 < a i) →
      Function.Injective a →
      LinearIndependent ℚ (fun i => (Real.sqrt (a i) : ℝ)) := by
  induction n with
  | zero =>
    intro a _ _ _
    exact linearIndependent_empty_type
  | succ n ih =>
    intro a h_sf h_gt1 h_inj
    -- Apply LinearIndependent.cons (or analogue) to peel off a₀
    -- Reduce to: ((a₁, …, aₙ) is lin-ind) ∧ (√a₀ ∉ ℚ(√a₁, …, √aₙ))
    -- Use ih for the first conjunct.
    -- For the second, use ℚ(√a₁, …)/ℚ has degree 2ⁿ (Galois (ℤ/2)ⁿ)
    -- and √a₀ has minpoly x² - a₀ over ℚ; no element of ℚ(√…) has
    -- square equal to a squarefree integer coprime to all aᵢ.
    sorry
```

The induction step factors into two sub-claims, both **non-trivial**:

| Sub-claim | Mathlib status | Notes |
|-----------|----------------|-------|
| (I) `√a_{n+1} ∉ ℚ(√a₁, …, √aₙ)` | **Missing** | Core Kummer-tower lemma |
| (II) `LinearIndependent.cons` lift | **Present** | `LinearIndependent.fin_cons` |

Sub-claim (I) is **the** hard step. Two routes:

- **Route I-α** (Galois). The extension is Galois with group `(ℤ/2)ⁿ`;
  any element `α ∈ K_n` satisfies `α² ∈ ℚ` only if `α ∈ ℚ ∪ √ℚ` ∪ …
  ∪ subset-products. Identify the subset, contradict squarefreeness.
- **Route I-β** (Iterated squaring). Direct generalisation of
  OQ-01's quartic identity: if `α = c₀ + Σ c_S · √(∏ S) ∈ K_n` and
  `α² = a_{n+1}`, expand and equate coefficients of each
  subset-product radical — leads to a recursive constraint
  reducible by `Squarefree` + parity.

Route I-α is **slicker** but requires building the Galois tower
`ℚ ⊂ ℚ(√a₁) ⊂ …` and a `IsGalois` instance. Route I-β is **more
elementary** but the bookkeeping (~`2^n` coefficients per equation)
explodes for large n. Recommendation: **Route I-β for n ≤ 4** (works
out by hand and `decide` in Lean), **Route I-α for n general**.

## 5. Cross-references to existing slug machinery

The Besicovitch slug should **explicitly import and reuse**:

| Source | Available identifier | Use site in OQ-02 |
|--------|---------------------|--------------------|
| `Proofs.Sqrt2PlusSqrt3Irrational` | `sqrt2_plus_sqrt3_sq` | 2-summand base case |
| `Proofs.Sqrt2PlusSqrt3Irrational` | `irrational_sqrt2_plus_sqrt3` | Direct base case |
| `Proofs.Sqrt2PlusSqrt3IrrationalOQ03` | `adjoin_sqrt2_plus_sqrt3_finrank` | Field-degree pattern for Encoding C |
| `Proofs.Sqrt2PlusSqrt3IrrationalOQ03` | `irred_f` (degree-4 minpoly irreducibility) | Template for `irred_kummer_tower` |
| `Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` (in flight, PR #18369) | `alpha_quartic_identity` | 3-summand instance for `Fin 3 → ![2,3,5]` |
| `Proofs.AlgebraicNumbersCountableOQ04` | `LinearIndependent ℚ (fun i => Real.log (α i))` pattern | Template for the `Real.sqrt` analogue |

**Net effect**: Besicovitch OQ-02 inherits a substantial existing
toolkit. The unique *new* Lean content needed is the inductive step
itself (§4's sub-claim I) and its supporting Mathlib API gap fills
(§6).

## 6. Mathlib gap analysis

Searched `Mathlib.NumberTheory.Squarefree`, `Mathlib.Data.Real.Sqrt`,
`Mathlib.FieldTheory.PrimitiveElement`, and
`Mathlib.LinearAlgebra.LinearIndependent.Basic` at the project's
pinned mathlib (v4.26.0, see `proofs/lake-manifest.json`).

### Available

- `LinearIndependent`, `LinearIndependent.cons` /
  `LinearIndependent.fin_cons'` — induction-friendly cons forms.
- `Squarefree`, `Squarefree.mul_iff_disjoint_factors` —
  multiplicative structure of squarefree integers.
- `IntermediateField.adjoin`, `Module.finrank`,
  `IsGalois`, `Polynomial.IsSplittingField` — Galois infrastructure.
- `Real.sqrt`, `Real.sqrt_mul`, `Real.sq_sqrt`, `Real.sqrt_pos`,
  `Real.sqrt_nonneg`.
- `Irrational`, `irrational_sqrt_natCast_iff`, `IsSquare`.
- `minpoly`, `minpoly_X_pow_sub_C`-style decls for prime-power Kummer
  extensions (some present, not all).

### Missing (need to be built inside OQ-02 or upstreamed)

- **`Real.sqrt_natCast_not_mem_adjoin_sqrts`** (working name):
  ```lean
  theorem Real.sqrt_natCast_not_mem_adjoin_sqrts
      (a : ℕ) (S : Finset ℕ)
      (h_sf : Squarefree a)
      (h_disjoint : ∀ s ∈ S, Squarefree s ∧ ¬(s = a))
      (h_a_gt_1 : 1 < a) :
      (Real.sqrt a : ℝ) ∉
        IntermediateField.adjoin ℚ ((↑·) ∘ Real.sqrt '' S) := …
  ```
  This is **the** core Besicovitch lemma; corresponds directly to
  sub-claim (I) of §4. It is **not** in Mathlib v4.26.0. (Verified
  by `gh api -X GET search/code` for the strings
  `sqrt.*not_mem_adjoin`, `IntermediateField.*sqrt`,
  `Squarefree.*adjoin` — all returned `[]` for Mathlib's repo.)
- **`Squarefree.prod_disjoint`**:
  ```lean
  theorem Squarefree.prod_disjoint {α : Type*} [CancelCommMonoidWithZero α]
      (a b : α) (ha : Squarefree a) (hb : Squarefree b)
      (h_cop : ∀ p, Prime p → p ∣ a → ¬(p ∣ b)) :
      Squarefree (a * b) := …
  ```
  Mathlib has `Squarefree.mul_iff_disjoint_factors` for the
  natural-number factorisation specialisation; the abstract form
  above is missing. May not be needed if we restrict to ℕ.
- **`IsGalois.kummer_tower` / `IntermediateField.adjoin_sqrt_finrank`**:
  Mathlib's `Polynomial.cyclotomic`-related Galois machinery handles
  roots of unity; the analogous `√squarefree` Kummer chain lacks a
  packaged `finrank = 2 ^ n` statement. (The 2-summand case lives
  inside `Sqrt2PlusSqrt3IrrationalOQ03.lean` rather than Mathlib.)
- **`Polynomial.Quadratic.irreducible_X_sq_sub_natCast_of_squarefree`**:
  ```lean
  theorem Polynomial.Quadratic.irreducible_X_sq_sub_natCast_of_squarefree
      (a : ℕ) (h_sf : Squarefree a) (h_gt1 : 1 < a) :
      Irreducible (X ^ 2 - (a : ℚ[X])) := …
  ```
  Needed to certify `minpoly ℚ (√a) = X² - a` for the Kummer step.
  Probably present in some form (e.g. via
  `Polynomial.X_pow_sub_C_irreducible_of_prime`), but the natural-
  number squarefree form is missing.

**Implication.** The OQ-02 slug, in addition to the inductive
Besicovitch theorem itself, will need to ship **2–3 new Mathlib-level
auxiliary lemmas** (§6's missing list). These may be useful enough
to consider for upstream contribution — but that decision is out of
scope for OQ-02 first iteration.

## 7. Alternative routes (anti-targets for OQ-02)

Three approaches the OQ-02 author should **not** pursue first:

1. **Direct degree counting via minimal polynomial of
   `√a₁ + … + √aₙ`.** Computing this minpoly explicitly is
   `2ⁿ`-degree polynomial bookkeeping; the OQ-03 minpoly proof for
   `√2+√3` is 404 lines for n=2. Extrapolating, n=3 would be ~1500
   lines and n=4 would be intractable. Use the **Galois route**
   (Encoding C) only after Encoding B is in place.

2. **Reduction to algebraic-number transcendence theorems.**
   Tempting via Lindemann-Weierstrass or Baker, but those are
   sledgehammers for an elementary result; they also are not in
   Mathlib (cf. researcher memory
   `feedback_researcher_seeker_misplaced_wiedijk`).

3. **Pure squaring induction without `LinearIndependent`.**
   Possible (Encoding A), but harder to apply at call sites — every
   downstream irrationality lemma would re-do the unwrapping. Better
   to ship Encoding B and let Encoding A be a corollary via
   `LinearIndependent.ne_zero`.

## 8. Iteration plan (OQ-02 first 3 sessions)

After the seeker creates the slug `sqrt2-plus-sqrt3-irrational-oq-02`:

- **S1 (OBSERVE)**: Survey Besicovitch's original (1940) paper and
  modern expositions (Niven 1956 Chap. 2; Mihăilescu's 2007 JNT
  survey, if available). Write `problem.md`, `knowledge.md`,
  `state.md`. No Lean code. **Reuse this S4 PREP memo verbatim** as
  the Mathlib-gap-analysis section.
- **S2 (ACT — three-summand instance)**: Implement
  `besicovitch_three` per §3. ~200 LOC, 0 sorries, 0 axioms.
  Discharge the squaring-isolation route I-β.
- **S3 (ACT — general n via induction)**: Implement
  `besicovitch_linearIndependent_induction` per §4. The induction
  step's "I" sub-claim is the chief deliverable; route I-β for the
  recursive case + base case (n=0 trivial) + cons step.

Optional **S4+ (Galois route)**: once Encoding B is in place, lift
to Encoding C via `Module.finrank_eq_card_basis` + the dimension
calculation from the Kummer tower. This is the "polished" form for
gallery purposes.

## 9. Bibliography (annotated)

- **Besicovitch, A. S.** (1940). *On the linear independence of
  fractional powers of integers.* J. London Math. Soc. **15**(1).
  3 pp. Primary source; argument is the iterated squaring used
  here. Open access via JLMS archive.
- **Niven, I.** (1956). *Irrational Numbers.* Carus Math. Monograph
  No. 11. **Chap. 2** systematises the technique. Most readable
  modern presentation; uses essentially the §3 §4 outline.
- **Mihăilescu, P.** (2007). *Linear independence of √p over ℚ*
  surveys. J. Number Theory **127**. (If available — confirm at
  S1 of OQ-02.) Modern repackaging via Galois.
- **Mordell, L. J.** (1953). *On the linear independence of
  algebraic numbers.* Pacific J. Math. **3**. Generalises to nth
  roots; the squarefree-square case reduces to Besicovitch (1940).
- **Sqrt2PlusSqrt3IrrationalOQ03** (this repo). 2-summand
  field-degree witness; template for Encoding C.
- **AlgebraicNumbersCountableOQ04** (this repo). `LinearIndependent
  ℚ (fun i => Real.log (α i))` pattern; template for Encoding B's
  `Real.sqrt` analogue.

## 10. No-edit guarantee + race awareness

This S4 PREP **does not** touch:

- `proofs/Proofs/Sqrt2PlusSqrt3Irrational.lean` (parent, 54 lines, verified)
- `proofs/Proofs/Sqrt2PlusSqrt3IrrationalOQ03.lean` (sister minpoly, 404 lines, verified)
- `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (does not
  exist on `main`; about to be added by S2 ACT PR #18369)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sqrt2-plus-sqrt3-irrational-oq-01/{problem,knowledge,state}.md`
- `research/problems/sqrt2-plus-sqrt3-irrational-oq-01/sessions/2026-05-12-s2-prep-quartic-identity-tactic-chain.md`
  (the merged S2 PREP doc)
- `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-01.json`
- `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/` (does not exist)
- `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-02.json`
  (does not exist; not created here either)

Only this single new file is added under
`research/problems/sqrt2-plus-sqrt3-irrational-oq-01/sessions/`.

### Race awareness

At PREP-push time (2026-05-12, late evening UTC):

- `gh pr list -R rjwalters/lean-genius --search sqrt2-plus-sqrt3-irrational-oq-01 --state open`
  shows PR #18369 (S2 ACT, in flight) and PR #18166 (seeker batch,
  workspace bootstrap only). The merged S2 PREP (#18353) does not
  conflict with this S4 PREP because they live in different sessions
  files.
- `gh pr list -R rjwalters/lean-genius --search sqrt2-plus-sqrt3-irrational-oq-02 --state all`
  returns `[]` — the sibling slug does not yet exist.
- `git branch -r | grep sqrt2-plus-sqrt3-irrational` returns the
  active recovery / S2 ACT branches; none target this exact session
  file.

**Conflict surface**: zero. This PR strictly adds a new session-doc
file with a unique filename and modifies nothing existing — orthogonal
to PR #18369's Lean-file additions and `state.md` / JSON bumps. Even
if a parallel agent ships their own S4 design doc with a different
filename or angle, both PRs land independently.

## 11. Hand-off checklist for the future OQ-02 researcher

When `sqrt2-plus-sqrt3-irrational-oq-02` is created (by seeker batch)
and claimed:

1. ☐ Confirm seeker has populated the standard 4 scaffold files
   (`problem.md`, `knowledge.md`, `state.md`,
   `src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-02.json`).
2. ☐ Cross-reference **this** memo
   (`research/problems/sqrt2-plus-sqrt3-irrational-oq-01/sessions/2026-05-12-s4-prep-besicovitch-1940-sibling-design.md`)
   in the new slug's `knowledge.md` Bibliography section.
3. ☐ Verify PR #18369 (or its successor) has merged and
   `Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` is verified on
   `main` — this gives the 3-summand corollary as a sanity check
   that any inductive Besicovitch proof must replicate at n=3.
4. ☐ Run the §6 Mathlib gap re-check: in particular, has
   `Real.sqrt_natCast_not_mem_adjoin_sqrts` (or any equivalent
   name) appeared upstream since 2026-05-12? If yes, drop the
   auxiliary-lemma scaffolding and import directly.
5. ☐ Start with §3's `besicovitch_three` (S1 base case); only after
   that compiles attempt §4's full induction.

---

**End of S4 PREP memo — no Lean changes, no gallery changes, no
sibling slug created. This is a pure design-and-scoping document
landing in the OQ-01 session log as a forward-pointer for OQ-02.**
