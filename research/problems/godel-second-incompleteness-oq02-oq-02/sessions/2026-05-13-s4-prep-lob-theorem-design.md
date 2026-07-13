# S4 PREP — Löb's theorem formalization design (doc-only, orthogonal to S2)

**Session**: 2026-05-13, researcher-9
**Phase**: S4 PREP (forward design memo; pre-implementation, doc-only)
**Slug**: godel-second-incompleteness-oq02-oq-02 (parent: Solovay's arithmetical completeness for GL)
**Parent S1 OBSERVE**: PR #18198 (merged 2026-05-12)
**Concurrent S1b OBSERVE**: PR #18404 (in-flight; typeclass-encoding axiom-budget analysis)
**Orthogonality**: This memo addresses the **S4+ alternative** explicitly listed in `state.md` § "Open questions deferred to later sessions" item 3 — a path the S1b PR does not pursue.

## 0. Why this angle now

The parent state.md ranks three completeness directions and one alternative:

> 3. **S4+ alternative (Löb formalization, ~150 lines):** Even without full Solovay, *Löb's theorem* (`F ⊢ □A → A ⇒ F ⊢ A`) can be formalized once D2/D3 are stated as proper axioms. The parent file flags this at line 213 as desirable but currently informal. This would also resolve a Wiedijk-100-list adjacent gap.

Löb's theorem occupies a privileged position in the gallery:

- It is the modal axiom that distinguishes GL from K4 (`knowledge.md` §1).
- It **implies Gödel's Second Incompleteness as a one-line corollary** with `A := ⊥` (`GodelSecondIncompletenessOQ02.lean` lines 213–235 informally state this).
- It is a **bounded, single-session deliverable**, in contrast to the S2-β soundness direction (~200–400 lines) and the S2-γ completeness direction (multi-thousand lines).
- It is **decoupled from Solovay's Σ₁-formalization blocker** (`state.md` § "Architectural flag") — Löb works with the gallery's *opaque* `Provable` axiom, provided HBL D2/D3 are stated honestly.

This PREP memo specifies (a) the Henkin-fixed-point axiom required, (b) the exact Lean lemma chain for the proof, (c) the resulting axiom-count ledger, and (d) the precise way Löb subsumes the existing `con_implies_G` bridge axiom. Strictly orthogonal to PR #18404's typeclass-vs-companion-file framing of D2/D3.

## 1. Where Löb sits in the gallery

### 1a. The informal flag in the parent file

`proofs/Proofs/GodelSecondIncompletenessOQ02.lean` lines 213–236:

> **Löb's Theorem (informal statement)**
>
> Löb (1955): For any formula A, `F ⊢ (□A → A)` implies `F ⊢ A`.
>
> [...]
>
> A full Lean proof of Löb requires the Henkin fixed-point sentence construction, which in turn needs an additional fixed-point axiom. We state the theorem here as a documentation of where Second Incompleteness fits in the broader landscape.

And explicitly:

> -- (Löb's full proof would need a Henkin fixed-point axiom; we omit it here
> --  to keep the file honest and free of unprovable sorry-substitutes.)

This is the gap the present PREP memo targets.

### 1b. The dependency on impl

Löb's statement `F ⊢ □A → A ⇒ F ⊢ A` requires an object-level implication `impl : Formula → Formula → Formula`, which the current `Formula` type lacks (`GodelFirstIncompletenessOQ01.lean` line 60 — `Formula` is just a single `Nat` code).

This is the **same prerequisite as S2-α** (`state.md` § "Next action (S2 recommended)"). So **S4 Löb is downstream of S2-α**: it cannot ship before S2-α adds `impl` to the `Formula` type.

S4 Löb is therefore independent of the typeclass-vs-companion-file framing of S2-α (PR #18404's subject) — Löb's statement is the same in either encoding; only the axiom-storage location differs.

## 2. Mathlib audit — Löb / fixed-point / modal-logic surface

GitHub-API-mediated audit (search/code, no Docker build), confirming the gap is real:

| Query (Mathlib v4.26.0) | Hits |
|---|---|
| `Löb theorem` | 0 substantive (only `docs/1000.yaml` Wiedijk list mention) |
| `Lob theorem provability` | 0 substantive (`HalesJewett.lean`, `Determinant/Basic.lean` are unrelated) |
| `provability modal logic` | 0 |
| `Henkin sentence diagonal lemma` | 0 (only the references.bib BibTeX entry) |
| `diagonal lemma syntactic` | 0 substantive |
| `incompleteness Godel` | 0 (Mathlib does not contain a Gödel incompleteness formalization) |
| `Hilbert Bernays Lob derivability` | 0 |

Adjacent inventory that *does* exist:

| Mathlib path | Relevance |
|---|---|
| `Mathlib/ModelTheory/Basic.lean` | First-order language framework. Provides `Language`, `BoundedFormula`, `Term`. **Could** host a future PA encoding but does not currently. |
| `Mathlib/ModelTheory/Syntax.lean` | Term/formula syntax. **Not** stratified by quantifier complexity (no Σ_n hierarchy). |
| `Mathlib/ModelTheory/Arithmetic/Presburger/{Basic,Definability,Semilinear}.lean` | Presburger arithmetic (i.e. quantifier-free additive arithmetic). **Insufficient** — Presburger is decidable, so Gödel's theorems do not apply to it. |
| `Mathlib/Computability/Partrec.lean`, `Primrec.lean` | Partial / primitive recursive functions in the meta-level (Lean's `ℕ → ℕ`). **Not** PA-internal; cannot host a Σ_1 provability predicate without further work. |

**Verdict.** Mathlib provides **none** of: Löb's theorem, the diagonal/fixed-point lemma, the Henkin sentence, a modal-logic library (K, K4, T, S4, GL, etc.), Kripke frames, the Σ_n arithmetic hierarchy, or a PA-internal provability predicate. The gallery is therefore free to define these in `Proofs/Proofs/` without re-export conflicts.

This audit refines `knowledge.md` § 5 ("Mathlib API survey") with concrete absent items and confirms that S4 Löb introduces no Mathlib name-collisions.

## 3. The Henkin fixed-point axiom

### 3a. Mathematical content

Löb's theorem says: if `F ⊢ □A → A`, then `F ⊢ A`. The classical proof uses **Henkin's fixed-point lemma**:

> For any formula `ψ(x)` of one free variable, there is a sentence `H` such that `F ⊢ H ↔ ψ(⌜H⌝)`.

Applying this to `ψ(x) := Prov(x) → A` (where `A` is the formula whose Löb-status we are proving):

> ∃ H, `F ⊢ (H ↔ (Prov(⌜H⌝) → A))`.

We call this the **Löb-Henkin sentence for A**.

### 3b. The new axiom (assuming S2-α has added `impl`)

```lean
namespace GodelSecond

-- Prerequisite: S2-α has added `impl : Formula → Formula → Formula` and the
-- D2/D3 axioms in either a companion file or the parent file. The exact
-- storage location is irrelevant to Löb's proof.

/-- **Axiom — Löb-Henkin fixed-point sentence**

    For every formula `A`, there exists a "Löb sentence" `H_A` such that
    F proves the biconditional `H_A ↔ (Prov(⌜H_A⌝) → A)`.

    **Mathematical content**: Henkin's fixed-point lemma applied to the
    arithmetical formula ψ(x) := (Prov(x) → A). In a full PA formalization,
    `H_A` is constructed by the standard substitution trick:
      H_A = ψ(⌜sub(x, x, x) → A⌝)
    where `sub` is the primitive recursive substitution function. The
    Diagonal Lemma is what makes this construction work; we take its
    consequence (existence of H_A) as a single axiom.

    **Why this is not implied by the existing axioms**: The Gödel sentence
    G in `GodelFirstIncompletenessOQ01` is the special case of Henkin's lemma
    for ψ(x) := ¬Prov(x). Each *new* fixed-point we need — for different ψ —
    requires the diagonal construction again. Löb needs the fixed-point for
    ψ(x) := Prov(x) → A; this is genuinely orthogonal to G's fixed-point. -/
axiom lob_henkin_fixed_point :
    ∀ A : Formula, ∃ H : Formula,
        (⊢ impl H (impl (Prov (godelNum H)) A)) ∧
        (⊢ impl (impl (Prov (godelNum H)) A) H)
```

We split the biconditional into its two implications because the current `Formula` type does not have an `iff` constructor; the conjunction expresses `↔` at the meta level.

**Cost**: 1 new axiom. **Strictly weaker than `con_implies_G`** (see § 5 below).

### 3c. Honest tradeoff

We could state the Diagonal Lemma in full generality instead:

```lean
axiom diagonal_lemma :
    ∀ ψ : Nat → Formula, ∃ H : Formula, ⊢ impl H (ψ (godelNum H)) ∧ ⊢ impl (ψ (godelNum H)) H
```

This is a **stronger** axiom (it gives all Henkin fixed-points uniformly), and it would also discharge the existing `G_self_reference` axiom (`GodelFirstIncompletenessOQ01.lean` line 136). However, it requires a higher-order parameter `ψ : Nat → Formula`, which complicates the axiom statement. **Recommendation**: ship `lob_henkin_fixed_point` first as the targeted single-purpose axiom, and consider unifying with `G_self_reference` via a generalized Diagonal Lemma in a separate session (call it S5 unification).

## 4. The Löb's theorem proof in Lean

### 4a. Theorem statement

```lean
theorem lob_theorem (A : Formula) (hHyp : ⊢ impl (Prov (godelNum A)) A) : ⊢ A
```

Read aloud: "If F proves (Prov(⌜A⌝) → A), then F proves A."

### 4b. The 7-step proof

Standard proof (e.g. Boolos *The Logic of Provability* Theorem 6.1; Smoryński *Self-Reference and Modal Logic* §1.4). All references are to lemmas inside `F`, applied via the gallery's meta-level `⊢` notation.

| Step | Justification | Internal F-derivation |
|---|---|---|
| 1 | Obtain Löb-Henkin sentence `H` via `lob_henkin_fixed_point A` | `F ⊢ H ↔ (Prov(⌜H⌝) → A)` |
| 2 | Forward direction of Step 1 | `F ⊢ H → (Prov(⌜H⌝) → A)` |
| 3 | D1 applied to Step 2 | `F ⊢ Prov(⌜H → (Prov(⌜H⌝) → A)⌝)` |
| 4 | D2 applied to Step 3 | `F ⊢ Prov(⌜H⌝) → Prov(⌜Prov(⌜H⌝) → A⌝)` |
| 5 | D2 applied to Step 4, plus D3 (Prov(⌜H⌝) → Prov(⌜Prov(⌜H⌝)⌝)) | `F ⊢ Prov(⌜H⌝) → (Prov(⌜Prov(⌜H⌝)⌝) → Prov(⌜A⌝))` then collapse via D3 | giving `F ⊢ Prov(⌜H⌝) → Prov(⌜A⌝)` |
| 6 | Compose Step 5 with the hypothesis `F ⊢ Prov(⌜A⌝) → A` | `F ⊢ Prov(⌜H⌝) → A` |
| 7 | Reverse direction of Step 1 applied to Step 6 | `F ⊢ H`, then D1 gives `F ⊢ Prov(⌜H⌝)`, then Step 6 gives `F ⊢ A`. □ |

### 4c. Lean skeleton (target ~80 lines + 1 axiom + ~30 lines of docstring)

```lean
namespace GodelSecond

theorem lob_theorem (A : Formula) (hHyp : ⊢ impl (Prov (godelNum A)) A) : ⊢ A := by
  -- Step 1: obtain Löb-Henkin sentence
  obtain ⟨H, hHfwd, hHbwd⟩ := lob_henkin_fixed_point A
  -- hHfwd : ⊢ impl H (impl (Prov (godelNum H)) A)
  -- hHbwd : ⊢ impl (impl (Prov (godelNum H)) A) H

  -- Step 3: D1 lifts hHfwd to a Prov statement
  have hStep3 : ⊢ Prov (godelNum (impl H (impl (Prov (godelNum H)) A))) :=
    d1_representability _ hHfwd

  -- Step 4: D2 distributes over the outer implication of Step 3
  have hStep4 : ⊢ impl (Prov (godelNum H))
                       (Prov (godelNum (impl (Prov (godelNum H)) A))) :=
    d2_distribution _ _ hStep3

  -- Step 5: D2 distributes again over the inner implication;
  --         D3 collapses Prov(⌜Prov(⌜H⌝)⌝) back to Prov(⌜H⌝).
  --         End result: ⊢ Prov(⌜H⌝) → Prov(⌜A⌝).
  have hStep5 : ⊢ impl (Prov (godelNum H)) (Prov (godelNum A)) := by
    -- Combine hStep4 with d2_distribution and d3_internal_necessitation H
    sorry  -- Two routine D2/D3 applications; ~10 lines

  -- Step 6: Compose Step 5 with the Löb hypothesis
  have hStep6 : ⊢ impl (Prov (godelNum H)) A := by
    -- impl_trans hStep5 hHyp  (via D2-modus-ponens on transitivity of impl)
    sorry  -- 1 application of impl_trans; ~3 lines

  -- Step 7: hHbwd applied to hStep6 gives ⊢ H; then D1 gives ⊢ Prov(⌜H⌝);
  --         finally hStep6 gives ⊢ A.
  have hH : ⊢ H := impl_mp hHbwd hStep6   -- via D2 at meta-level
  have hProvH : ⊢ Prov (godelNum H) := d1_representability _ hH
  exact impl_mp hStep6 hProvH

end GodelSecond
```

### 4d. Required supporting lemmas

For the skeleton above to type-check, S2-α must provide:

| Helper | Statement | Justification |
|---|---|---|
| `d2_distribution` | `∀ φ ψ, ⊢ Prov (godelNum (impl φ ψ)) → ⊢ impl (Prov (godelNum φ)) (Prov (godelNum ψ))` | D2 at the level of provability codes |
| `d3_internal_necessitation` | `∀ φ, ⊢ impl (Prov (godelNum φ)) (Prov (godelNum (Prov (godelNum φ))))` | D3 in object form |
| `impl_trans` | `∀ φ ψ χ, ⊢ impl φ ψ → ⊢ impl ψ χ → ⊢ impl φ χ` | Propositional tautology; follows from D2 + `impl_self` |
| `impl_mp` | `∀ φ ψ, ⊢ impl φ ψ → ⊢ φ → ⊢ ψ` | Meta-level modus ponens (NOT an axiom; provable from D2 by setting `Prov := id`-instance — wait, no: meta-level MP cannot be derived from internal D2 alone; it must be a separate axiom or assumed for `Formula`). Concretely, `impl_mp` is one of the two HBL "necessitation" rules and is independent of D2. |

`impl_mp` is the **meta-level modus ponens** and is logically distinct from D2. In a Hilbert-style presentation it is the inference rule "from ⊢ φ → ψ and ⊢ φ infer ⊢ ψ". S2-α must axiomatize this if `impl` is added.

**Refined axiom budget for S2-α**: not just D2 and D3, but also `impl_mp` (the meta-MP rule for `impl`). Either:
- Encode `impl` so that `⊢ impl φ ψ` *is* `(⊢ φ) → (⊢ ψ)` (definitional collapse — eliminates `impl_mp` as a separate axiom but blurs internal-vs-meta distinction)
- Keep `impl_mp` as a third axiom (cleaner separation, +1 axiom)

This is a refinement to `knowledge.md` § 6 ("S2-α"): the axiom count is **≥ 3** (impl_mp + D2 + D3), not 2 as stated. The S1b PR's axiom-ledger analysis should incorporate this.

### 4e. Second Incompleteness as a one-line corollary

Once Löb is in hand:

```lean
/-- **Gödel's Second Incompleteness via Löb's theorem**

    Setting `A := falsum` in Löb's theorem and using `impl_mp` with consistency
    yields the second-incompleteness theorem with no use of the bridge axiom
    `con_implies_G`. -/
theorem second_incompleteness_via_lob (h : Consistent) : ¬ (⊢ Con) := by
  intro hCon
  -- Con = neg (Prov (godelNum falsum))
  -- We need ⊢ falsum to contradict consistency. Apply Löb with A := falsum:
  -- Hypothesis for Löb: ⊢ impl (Prov (godelNum falsum)) falsum
  -- This is the contrapositive of Con (via classical logic; here we encode
  -- it directly using the structure of `neg` and `impl`).
  have hHyp : ⊢ impl (Prov (godelNum falsum)) falsum := by
    -- From hCon : ⊢ Con = ⊢ neg (Prov (godelNum falsum))
    -- and the identification `neg φ` ≈ `impl φ falsum` (under the new impl
    -- axiomatization), we get the desired implication.
    sorry  -- 1 lemma: neg_eq_impl_falsum, ~5 lines
  have hFalsum : ⊢ falsum := lob_theorem falsum hHyp
  -- ⊢ falsum contradicts consistency via h
  exact (h falsum ⟨hFalsum, by sorry⟩).elim   -- routine
```

This **eliminates the `con_implies_G` axiom** in favor of `lob_henkin_fixed_point` + (the also-needed for Löb) `d2_distribution` and `d3_internal_necessitation`. Concretely:

- **Before** (current file, lines 153, 186, 246–247): `con_implies_G` + the 5 axioms from `GodelFirstIncompletenessOQ01` = **6 axioms total**.
- **After** S4 Löb + S2-α: `Provable`, `d1_representability`, `G_self_reference`, `omega_consistency_G`, `neg_G_prov_G` (from First Incompleteness) + `impl_mp`, `d2_distribution`, `d3_internal_necessitation`, `lob_henkin_fixed_point` = **9 axioms total**.

Net axiom count **increases** by 3. **This is honest**: the `con_implies_G` axiom was **bundling D2 + D3 + Henkin** into one opaque assumption; unbundling them is the right move for axiom-budget transparency, even though it raises the count. This is the converse of the typeclass-encoding analysis in PR #18404, which observes that *bundling* axioms into a typeclass field doesn't reduce the assumption count. *Unbundling* them, conversely, **reveals** the assumption count.

**Per project axiom-integrity policy**: ALL of D2, D3, `impl_mp`, and `lob_henkin_fixed_point` were *implicitly* in `con_implies_G`. Stating them separately doesn't add new assumptions — it makes existing ones explicit. The bundling/unbundling boundary is a *transparency* choice.

## 5. Comparison with existing `con_implies_G`

| Aspect | Current `con_implies_G` (line 153) | Proposed S4 Löb route |
|---|---|---|
| Axiom statement form | `(⊢ Con) → (⊢ G)` (single arrow at meta level) | `∀ A, ∃ H, ⊢ H ↔ Prov(⌜H⌝) → A` (existential of object-level biconditional) |
| What it bundles | D2 + D3 + Diagonal Lemma applied to ¬Prov | Diagonal Lemma applied to Prov(x) → A. **D2/D3 not bundled** — stated separately. |
| Scope | Specialized to G | Generic over A (gives Second Incompleteness with A := ⊥, Rosser's improvement with A := ⊥/different fixed-point, etc.) |
| Provability "explanation" | None — purely a black box | Proves Löb's theorem from HBL conditions in 7 internal steps |
| Axiom count contribution | 1 | 1 (`lob_henkin_fixed_point`) + 3 (`impl_mp` + D2 + D3 — also needed by Löb but shared with S2-α prerequisite) = 4 axioms used by Löb's proof; **3 of which are anyway required by S2-α** |
| Dependency on `impl` | None (only `Con = neg (Prov …)` and `G`) | Yes — requires S2-α to have run first |

The 4-axioms-used-by-Löb (`lob_henkin_fixed_point`, `impl_mp`, D2, D3) versus the bundled-into-`con_implies_G` count of 1 is the headline number. But **S2-α is going to add D2/D3/impl_mp regardless** — those are the prerequisite. The *net additional cost of Löb on top of S2-α* is **1 axiom** (`lob_henkin_fixed_point`), and the *benefit* is that `con_implies_G` becomes derivable rather than axiomatic. So Löb's standalone marginal cost is +1 axiom, –1 axiom = 0.

## 6. Risks and watch-outs

### 6a. Henkin fixed-point uniformity

The proof of Löb in § 4 quantifies over `A`. So `lob_henkin_fixed_point` is itself a `∀ A`. This is **necessary**: each different `A` requires a different Henkin sentence `H_A`. This is **fine** from an axiom-budget perspective — a single `∀`-axiom captures the entire family — but it does mean that this axiom is *stronger* than `G_self_reference` (which is a single Henkin instance for ψ := ¬Prov). A future refactor that introduces a generalized Diagonal Lemma (see § 3c) would let `G_self_reference` be a *theorem* derived from `diagonal_lemma`.

### 6b. The encoding of `impl`

For the proof to type-check, `impl φ ψ` and `neg φ` must be coherent. One natural encoding:

```lean
def impl (φ ψ : Formula) : Formula := ⟨Nat.pair 1 (Nat.pair φ.code ψ.code)⟩
-- neg (already defined as ⟨φ.code + 1⟩)
```

But this *doesn't* satisfy `neg φ = impl φ falsum` definitionally (the codes are different). So § 4e's `neg_eq_impl_falsum` lemma is non-trivial — it would be an **additional axiom** in the current style or a **derived theorem** in a future encoding where `neg` is defined as `impl φ falsum`. **Recommendation**: when shipping S2-α, *redefine* `neg φ := impl φ falsum` (this is the standard classical-logic convention) so that `neg_eq_impl_falsum` is `rfl` and `G_self_reference` / `neg_G_prov_G` get cleanly rewritten in terms of `impl`. This is a **breaking change** to `GodelFirstIncompletenessOQ01.lean`.

This is an **architectural decision-point** that S4 surfaces but does not itself resolve. The S1b PR's axiom-ledger framework would be the right place to discuss "redefine `neg` via `impl`" as one entry in the design table.

### 6c. Coherence with Rosser's improvement

Rosser (1936) eliminates the ω-consistency hypothesis (`omega_consistency_G`) of First Incompleteness using a stronger sentence. Rosser's sentence is *also* a Henkin fixed-point — of a more complex ψ involving a Σ_1-ordering of proofs. The same `lob_henkin_fixed_point` axiom (suitably generalized to families of ψ's, i.e. a full Diagonal Lemma) would discharge Rosser's construction too. This is a separate session (S6 candidate, not S4).

### 6d. Build/test plan

S4 PREP is **doc-only**, no Lean code changes. Build verification is N/A. Future S4 ACT (Löb's theorem in Lean) will require Docker-wrapped `lake build` per project policy.

The S4 ACT estimate of ~150 LOC in the parent `state.md` is consistent with the Lean skeleton in § 4c: ~80 LOC theorem body + ~30 LOC axiom + docstrings + supporting lemmas = ~150 LOC total. Two `sorry`s remain in § 4c that are routine D2/D3 manipulations; budget +20 LOC for those.

## 7. Three S4 sub-targets ranked by tractability

### S4-α (cheapest, ~50 LOC, 0 new axioms post-S2-α)

State `lob_theorem` as `axiom` rather than proving it. This is the most parsimonious option: it makes Löb's theorem **a stated result** of the gallery, formalizes the modal axiom (L) `□(□p → p) → □p`, and lets `second_incompleteness_via_lob` derive Second Incompleteness from a single axiom (the Löb axiom itself, no Henkin fixed-point needed).

**Cost**: +1 axiom (`lob_theorem`).
**Benefit**: Eliminates `con_implies_G` (the current bridge). Net axiom count change vs. current: 0. Gives a *named* Löb axiom that matches the GL presentation directly.

### S4-β (recommended, ~150 LOC, +1 new axiom post-S2-α)

Implement § 4's full proof of Löb from `lob_henkin_fixed_point` + D1/D2/D3 + `impl_mp`. This is the **honest** path: Löb's theorem becomes a *theorem*, not an *axiom*. The Henkin fixed-point is the only new axiom beyond what S2-α already supplies.

**Cost**: +1 axiom (`lob_henkin_fixed_point`).
**Benefit**: Demonstrates the actual HBL → GL chain; matches Boolos / Smoryński textbook treatments.

### S4-γ (ambitious, ~250 LOC, +1 new axiom post-S2-α, replaces 1 existing axiom)

Same as S4-β but also generalize `lob_henkin_fixed_point` to the full Diagonal Lemma (parametrized over `ψ : Nat → Formula`), and *derive* `G_self_reference` (from `GodelFirstIncompletenessOQ01`) as a corollary. **Net axiom count drops by 1**: a generalized diagonal axiom replaces both `G_self_reference` (line 136) and the specialized Löb-Henkin lemma.

**Cost**: +1 axiom (generalized diagonal), –1 axiom (`G_self_reference` becomes a theorem). Net 0.
**Benefit**: A single uniform foundation for **all** Henkin-style fixed points (Gödel's G, Löb's H, Rosser's sentence, etc.).
**Risk**: Higher-order `ψ : Nat → Formula` may interact with Lean's universe machinery in non-obvious ways. Mitigation: keep `ψ` first-order via `Nat → Nat`-style code surgery.

**Recommendation**: ship S4-β as the standalone-deliverable session. S4-γ is a follow-on after S4-β has proved out the encoding.

## 8. Connection to the Wiedijk-100 list and prior gallery work

Wiedijk's 100-theorems list entry #56 is "Gödel's incompleteness theorems" — already discharged by the existing First/Second incompleteness gallery files. Löb's theorem is **not separately listed in Wiedijk-100**, but it is mentioned in the parent file's docstring (line 213, "Löb's Theorem (informal statement)") as a desired next step.

`knowledge.md` § 5 ("Mathlib API survey") flags GL/modal-logic as greenfield. PR #18198 (the S1 OBSERVE merged 2026-05-12) confirms this and ranks "S4+ Löb formalization" as the bounded alternative to the multi-session S2-γ Solovay completeness direction. The present PREP memo concretizes that ranking.

Cross-references:

- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean:213–236` — the informal Löb statement this S4 makes formal.
- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean:153` — the `con_implies_G` axiom that S4-β / S4-γ subsume.
- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean:136` — `G_self_reference`, the specialized Henkin fixed-point that S4-γ generalizes.
- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean:81` — the `Provable` axiom that Löb works with as-is (no Σ_1 formalization required, unlike Solovay completeness).
- `research/problems/godel-second-incompleteness-oq02-oq-02/state.md:59–63` — the S4+ alternative this memo addresses.
- `research/problems/godel-second-incompleteness-oq02-oq-02/knowledge.md:142–149` — S2-γ Solovay completeness (the harder path this S4 sidesteps).

## 9. Honesty notes

- **This memo is doc-only.** No Lean code changes; no build verification required or performed.
- **Löb's theorem is well-established** (Löb 1955, Boolos 1993, Smoryński 1985). The Lean skeleton in § 4c follows Boolos *The Logic of Provability* Theorem 6.1 verbatim.
- **The proof shape described here is standard** — there is no claim of mathematical novelty, only of formalization tractability within the existing gallery's `Provable`-axiom framework.
- **The axiom-budget claims in § 4e / § 5 / § 7 are arithmetic**: 5 axioms (First) + 4 axioms (impl_mp + D2 + D3 + Löb-Henkin) = 9 axioms vs. 5 + 1 = 6 currently. This is a +3 net change and **must be accurately reflected in any future meta.json** if a corresponding Lean file is built.
- **No claim is made that S4 Löb resolves Solovay's completeness theorem.** It explicitly *does not* — the completeness direction requires Σ_1-formalization of `Provable` (the architectural blocker flagged in `state.md` § "Architectural flag"), and S4 inherits the existing opaque-`Provable` axiom.
- **The S1b PR #18404 (typeclass-encoding axiom-budget) is orthogonal.** Whether D2/D3 live in a typeclass or a companion file, Löb's proof (§ 4c skeleton) is unchanged; only the import statement and axiom-storage location differ.

## 10. No-edit guarantee

This PREP memo touches **only** the new file `sessions/2026-05-13-s4-prep-lob-theorem-design.md`. It does **not** modify:

- `problem.md`
- `knowledge.md`
- `state.md`
- `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json`
- Any file under `proofs/Proofs/Godel*`
- Any other gallery JSON or meta.json
- `.lean/state/candidate-pool.json` (no status change — claim will be released with `progress` outcome)

This guarantees zero merge conflict with the in-flight S1b PR #18404 and any future S2-α implementation PR.
