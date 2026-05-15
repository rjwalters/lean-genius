# Knowledge: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01

**S1 OBSERVE — researcher-8, 2026-05-14, doc-only (no Lean changes)**

## 1. Inheritance from the parent

The parent slug
`angle-trisection-oq-02-oq-01-oq-02-incomplete-01` (file
`proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`) shipped
to `main` at **0 sorries / 0 axioms / 639 LOC** with 21 declarations
including:

| Symbol | Status | Role |
|---|---|---|
| `IsConstructible : ℂ → Prop` | inductive | `rational` + `sqrt_ext` constructors |
| `isConstructible_rat / _zero / _one / _sqrt2` | proved | base elements |
| `isConstructible_map (σ : ℂ →ₐ[ℚ] ℂ)` | proved | **Galois invariance** |
| `isConstructible_algebraic` | proved (private) | constructible ⇒ algebraic over ℚ |
| `isConstructible_sup_degree` | proved (private) | stronger IH: `∀ K, finrank K (K ⊔ ℚ⟮α⟯) ∣ 2^n` |
| `isConstructible_algebraic_degree` | proved (private) | `finrank ℚ ℚ⟮α⟯ ∣ 2^n` |
| `isConstructible_minpoly_pow2` | proved | `natDeg(minpoly_ℚ α) = 2^m` |
| `isConstructible_irred_degree_pow2` | proved | for irreducible `p` with constructible root: `natDeg p = 2^m` |
| `not_constructible_of_bad_degree` | proved | contrapositive of degree-pow2 |
| `angle_trisection_impossible_degree` | proved | classical impossibility (cos 20°) |
| `doubling_cube_impossible_degree` | proved | classical impossibility (∛2) |
| `regular_7gon_construction_impossible` | proved | classical impossibility (7-gon) |

All three classical results are dispatched via the degree-of-minimal-polynomial
criterion alone — no abstract Galois group reasoning is needed for the
gallery's headline statements. `wantzel_galois_iff` (full ↔) appears in
the parent docstring only and is explicitly labeled
"out-of-scope: 500+ lines of new Galois theory infrastructure".

## 2. The OQ-01 question

This slug is a seeker-generated extension. The natural reading of
"OQ extension (01)" given the parent's state is: **state and prove
`wantzel_galois_iff` (or one of its two directions) using the
infrastructure already present in the parent file.**

### Direction split

| Direction | Statement | Estimated LOC | Risk |
|---|---|---|---|
| ⇒ | constructible ⇒ Gal is 2-group | ~200 | moderate (Mathlib `IsAlgClosed.lift` ergonomics) |
| ⇐ | Gal is 2-group ⇒ constructible | ~300+ | high (needs FTGT + Sylow + degree-2-as-√-adjoin) |
| ↔ | bidirectional `wantzel_galois_iff` | ~500+ | high (sum of both) |

Parent's Session 36 notes already document a proof plan for the ⇒
direction:

> "For each root β of p in ℂ, use `IsAlgClosed.lift` to extend
> ℚ(α)→ℂ (sending α↦β) to σ: ℂ→ℂ; then `isConstructible_map σ` gives
> `IsConstructible β`. Tower law: each step [K(βᵢ):K] ≤ [ℚ(βᵢ):ℚ] | 2^n,
> product = 2-power = |p.Gal|."

For this OQ-01 extension we tentatively scope to **the ⇒ direction
only** (`isConstructible_galois_two_group`). Whether to attempt ↔ in
this slug, or to spin out a dedicated `oq-02` for the ⇐ direction, is
an S2 PREP decision once we audit `Mathlib.FieldTheory.Galois` ergonomics
in v4.26.0.

## 3. Mathlib API surface — preliminary scan

The proof of ⇒ direction will rely on the following Mathlib lemmas (none
are yet imported by the parent file beyond what is already present
under `import Mathlib.FieldTheory.Galois.Basic`):

| Lemma | Path (Mathlib v4.26.0) | Role |
|---|---|---|
| `IsAlgClosed.lift` | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` | Extend ℚ⟮α⟯ → ℂ to all of ℂ → ℂ when target is algebraically closed. |
| `IntermediateField.normalClosure_le_iff` | `Mathlib/FieldTheory/Normal.lean` | Characterize splitting field via normal closure. |
| `Polynomial.SplittingField` | `Mathlib/FieldTheory/SplittingField/*.lean` | Abstract splitting-field type. |
| `Polynomial.roots_def`, `Polynomial.SplittingField.adjoin_roots` | `…/SplittingField/Construction.lean` | Splitting field is `ℚ⟮roots⟯`. |
| `Polynomial.Gal` | `Mathlib/FieldTheory/Galois/GaloisCard.lean` | `Gal(p)` as `p.SplittingField ≃ₐ[ℚ] p.SplittingField`. |
| `Polynomial.Gal.card_eq_finrank_splittingField` | same | `|Gal(p)| = [splittingField : ℚ]` when separable. |
| `IntermediateField.adjoin.finrank` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` | `[ℚ⟮α⟯:ℚ] = natDeg(minpoly_ℚ α)`. |
| `Module.finrank_mul_finrank` | `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean` | Tower-law multiplicativity. |

**Pre-claim grep warnings**: the parent file builds clean at v4.26.0 as
of the latest merge (per `Status: 0 sorries, 0 axioms` line 50), but
v4.26.0-era memory entries note several Mathlib renames in this area
(see e.g.
`feedback_researcher_mathlib_v426_matrix_isdiag_inv_one_squarefree_kit`
for `Mathlib.Algebra.Polynomial.Squarefree` removal). S2 PREP should
verify each lemma path above by `gh search code` before writing Lean.

### Specific bearer-API uncertainties (queued for S2 PREP)

1. **`Polynomial.Gal` vs `SplittingField ≃ₐ[ℚ] SplittingField`** — is
   `Polynomial.Gal` the canonical Mathlib name in v4.26.0 (vs e.g.
   `Polynomial.gal`)? Need to confirm.
2. **`IsAlgClosed.lift` signature** — what exactly does it produce? An
   `AlgHom` or a full `AlgEquiv`? The parent's `isConstructible_map`
   takes a `ℂ →ₐ[ℚ] ℂ` (AlgHom, not necessarily Equiv), which is the
   weaker requirement, so this should align.
3. **`Polynomial.separable_iff_*`** — the Galois-cardinality formula
   `|Gal| = [splittingField:ℚ]` requires separability; over a field of
   characteristic 0 this is automatic. Verify the Mathlib lemma name.

## 4. Proof sketch for the ⇒ direction

Following the parent's Session 36 plan, in full detail:

```
Goal: IsConstructible α  →  ∃ n, |Gal(minpoly_ℚ α)| = 2^n.

Let p = minpoly ℚ α.

Step 1: p is the minimal polynomial — by definition irreducible over ℚ,
        and α is a root. (Mathlib: minpoly.irreducible, minpoly.aeval_eq_zero.)

Step 2: |Gal(p)| = [splittingField p : ℚ]   -- separable polynomial,
        char 0. (Mathlib: Polynomial.Gal.card_eq_finrank_splittingField
        or equivalent.)

Step 3: splittingField p = ℚ⟮β₁, ..., βₖ⟯ where {β₁, ..., βₖ} = roots of p
        in some algebraic closure. (Mathlib: SplittingField.adjoin_roots.)

Step 4: Each βᵢ is constructible. — For each i, there is a ℚ-algebra
        map ℚ⟮α⟯ → ℂ sending α to βᵢ (universal property of minpoly).
        Extend via IsAlgClosed.lift to σᵢ : ℂ →ₐ[ℚ] ℂ with σᵢ(α) = βᵢ.
        Apply `isConstructible_map σᵢ h` to get `IsConstructible βᵢ`.

Step 5: For each βᵢ, [ℚ⟮βᵢ⟯ : ℚ] ∣ 2^nᵢ for some nᵢ. — Directly from
        `isConstructible_algebraic_degree`.

Step 6: [ℚ⟮β₁, ..., βₖ⟯ : ℚ] ∣ 2^(n₁ + ... + nₖ). — By repeated
        application of `isConstructible_sup_degree` (the stronger IH
        which gives a *relative* bound `∀ K, [K ⊔ ℚ⟮βᵢ⟯ : K] ∣ 2^nᵢ`).
        Tower-law product.

Step 7: Therefore |Gal(p)| = [splittingField : ℚ] = [ℚ⟮β₁,...,βₖ⟯ : ℚ]
        divides 2^N for some N; by Nat.dvd_prime_pow this means
        |Gal(p)| = 2^n for some n ≤ N.
```

LOC budget: each step is 10–40 LOC, total ~200 LOC. The riskiest piece
is Step 4 (`IsAlgClosed.lift` chain): the parent file does not currently
use this lemma, so its ergonomics in v4.26.0 are unknown to us.

## 5. Parallel-work check

| Slug | Status | Overlap risk |
|---|---|---|
| `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` (parent) | merged 0-sorry, no open PRs as of 2026-05-14 21:00 UTC | low — we add a NEW file or a NEW `Part 7` to the parent |
| `angle-trisection-oq-02-oq-04-oq-01` | uses explicit `QuadraticTower` | low — different framework |
| `angle-trisection-cos-20-gal-oq-01-*` | family of OQ slugs about cos 20° Galois | low — different `α` |
| `angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01` (this slug) | pre-claim `gh pr list … in:title` → **0 open PRs** at 21:00 UTC | clear |

S1 OBSERVE pre-claim check (2026-05-14T21:00:00Z):
```
gh pr list -R rjwalters/lean-genius \
  --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01 in:title" \
  --state open --limit 5
# → 0 results
```

## 6. Candidate routes for S2

| Route | Description | Pros | Cons |
|---|---|---|---|
| **R1: extend parent file** | Add Part 7 to `AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` containing `isConstructible_galois_two_group` (⇒ only) | Reuses all existing infra by name without imports; simple to review | Bloats parent file from 639 → ~840 LOC |
| **R2: new companion file** | Create `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean` importing the parent | Keeps OQ extension self-contained, easy to revert | Need to expose private lemmas (`isConstructible_algebraic_degree`, `isConstructible_sup_degree`) — they are currently `private` |
| **R3: companion + parent surface lift** | Like R2, but first promote select `private` lemmas to public in a separate doc-only or surface-only PR | Cleanest layering | Two PRs needed; sequencing risk |

**S1 recommendation**: R2 (new file `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`)
is the lowest-risk option. The `private` lemma access can be addressed
by re-deriving the bound from the public `isConstructible_minpoly_pow2`
which already exposes the same fact (`finrank ℚ ℚ⟮α⟯ = natDeg(minpoly) = 2^m`).

## 7. Honest assessment

- Significance: closes the "out-of-scope" entry from parent's docstring.
  Useful gallery completion, not a research frontier result.
- Tractability: the ⇒ direction is moderately tractable (parent already
  has all the building blocks). The ⇐ direction adds 300+ LOC of FTGT
  infrastructure and is genuinely hard within a single session — likely
  spin out to its own OQ-02 slug if attempted at all.
- Single-session reach for an ACT phase: realistic target is **the ⇒
  direction's full statement + 1-2 key auxiliary lemmas with strategic
  sorries**, NOT a complete ⇒ proof. Full ⇒ likely takes 2–3 ACT
  sessions.

## 8. Next phase (S2 PREP)

S2 PREP should:

1. **Audit Mathlib v4.26.0 paths** for the 8 lemmas in §3 above. Run
   `gh search code` for each, record path:line citations.
2. **Audit `private` decisions** in the parent. For each private lemma
   in `Part 2` (the tower-degree section), decide: re-derive from public
   surface, or promote to public in a separate small PR.
3. **Decide R1 vs R2 vs R3** based on the private-surface audit outcome.
4. **Refine `wantzel_galois_iff` statement**: confirm whether `Polynomial.Gal`
   is the canonical v4.26.0 name and whether to use `Fintype.card` or
   `Cardinal.mk` for the cardinality.
5. **Stretch consideration**: is the ⇐ direction worth attempting in
   this slug, or should we spin it out to a dedicated `oq-02` slug?
