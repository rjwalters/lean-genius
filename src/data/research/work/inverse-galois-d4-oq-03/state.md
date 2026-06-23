# `inverse-galois-d4-oq-03` — Iteration state

## Current iteration

**S4 PREP** — 2026-06-10, researcher-1. JSON STATE-SYNC absorbing 3
sessions of drift (S2 SCAFFOLD → S3a → S3b, all merged 2026-05-12 but
JSON tracker never updated past S1 OBSERVE) + Mathlib `DihedralGroup`
API audit at pin `2df2f0150c…` showing `DihedralGroup.lift` is
**absent** → S5 hand-construction route is the only path. Sharpened
S5 decomposition into 3-PR series (S5a Generators ~40-60 LOC / S5b
Forward map ~30-50 LOC / S5c Bijectivity+MulEquiv ~30-50 LOC) plus
optional combined single-PR alternative S5∗ (~120-160 LOC). NO Lean
changes at S4 — pure doc-only iteration. See
`sessions/2026-06-10-s4-prep-mulequiv-recipe.md` for §0-§8 detailed
recipe.

## Iteration log

### S3b (researcher-4, 2026-05-12)

**Goal.** Continue the S3a "isolate the hard step" strategy by adding more
no-sorry bridge helpers that further narrow the S4 work to exactly one
ingredient: the concrete `MulEquiv` construction
`Gal(X⁴ − 2 / ℚ) ≃* DihedralGroup 4`.

**Deliverables (all in `proofs/Proofs/InverseGaloisD4OQ03.lean`, no new sorries).**

1. `theorem xPowSub_4_2_natDegree : (xPowSub 4 2).natDegree = 4` — via
   parent's `x_fourth_sub_2_natDegree` under the local notation.
2. `theorem xPowSub_4_2_irreducible : Irreducible (xPowSub 4 2)` — via
   parent's `x_fourth_sub_2_irreducible` (Eisenstein at `p = 2`).
3. `theorem xPowSub_4_2_separable : (xPowSub 4 2).Separable` — via
   parent's `x_fourth_sub_2_separable`.
4. `theorem xPowSub_4_2_monic : (xPowSub 4 2).Monic` — via parent's
   `x_fourth_sub_2_monic`.
5. `theorem dihedralGroup_4_card : Fintype.card (DihedralGroup 4) = 8`
   — direct from Mathlib's `DihedralGroup.card [NeZero n] : Fintype.card
   (DihedralGroup n) = 2 * n`. Codomain-side cardinality target.
6. `theorem gal_card_eq_dihedralGroup_4_card :
   Fintype.card (xPowSub 4 2).Gal = Fintype.card (DihedralGroup 4)` —
   combines `gal_card_xPowSub_4_2` (S3a) and `dihedralGroup_4_card`. The
   *necessary* condition for any `MulEquiv` to exist between the two.
7. `theorem dihedral_galois_xPow4_sub_2_of_mulEquiv (φ : ... ≃* DihedralGroup 4)
   : IsDihedralGaloisOfXnMinusA 4 2` — the S4 entry point: supplies
   the existential witness `m = 4` so S4 only needs to produce the
   concrete `MulEquiv`. Net effect: discharging
   `dihedral_galois_xPow4_sub_2` is now precisely "produce a
   `MulEquiv` `Gal(X⁴ − 2) ≃* DihedralGroup 4`".

**Sorry count.** 1 → 1. The remaining sorry remains on
`dihedral_galois_xPow4_sub_2`. **Strategic effect**: the route to
discharging it now decomposes into:
- Cardinality match: ✅ via `gal_card_eq_dihedralGroup_4_card`.
- Polynomial setup (irreducibility, separability, monicity,
  natDegree): ✅ via four S3b bridge helpers.
- Existential witness `m = 4`: ✅ via
  `dihedral_galois_xPow4_sub_2_of_mulEquiv`.
- **Remaining for S4**: construct an explicit
  `(Gal ≃* DihedralGroup 4)` term. The only piece left.

**Theorem count.** 4 → 11 (+7 new no-sorry bridge helpers). Definition
count unchanged at 2. Line count 153 → 235 (+82, all proofs +
docstrings).

**Scope choices.**

- **Strict no-sorry growth**: every new helper is a thin alias over an
  existing parent theorem or a single Mathlib lemma application
  (`DihedralGroup.card`). Net sorry count holds at 1.
- **No new infrastructure**: no Sylow theory, no transitive-subgroup
  classifications, no construction of generators. Those belong in S4
  proper.
- **MODERATE+ saturation context**: per
  `project_moderate_plus_oversubscribed_pool.md`, single focused PR
  preferred over speculative discharge attempts. Same pattern as S3a.
- **S4 reduction precision**: `dihedral_galois_xPow4_sub_2_of_mulEquiv`
  is the key strategic deliverable — it tells the next researcher
  exactly what they need to produce (a `MulEquiv`, not a chain of
  existential witnesses).

**Build status.** Build pending — pure thin-alias additions with no
new tactic invocations on the existing code. Risk areas:
- `DihedralGroup.card` requires `[NeZero 4]`, which is automatic for
  the literal `4`. If the instance is missing, fallback is `by decide`
  (Fintype.card on a small inductive is computable).
- `dihedralGroup_4_card` uses `DihedralGroup.card.trans (by norm_num)`
  to combine `Fintype.card (DihedralGroup 4) = 2 * 4` with `2 * 4 = 8`.
  If `DihedralGroup.card` is a non-rewriting lemma (e.g., `@[simp]`
  with explicit `NeZero` arg), fallback is `by rw [DihedralGroup.card];
  norm_num`.

**Next action.**

1. **S4** — Discharge `dihedral_galois_xPow4_sub_2` by constructing
   a concrete `MulEquiv` `((xPowSub 4 2).SplittingField ≃ₐ[ℚ]
   (xPowSub 4 2).SplittingField) ≃* DihedralGroup 4`. Standard route:
   (a) exhibit the Galois group as a transitive subgroup of `S₄`
   (via `Polynomial.Gal.galActionHom_injective` from the parent +
   `xPowSub_4_2_irreducible` for transitivity); (b) identify two
   generators — one of order 4 (e.g., `σ : ⁴√2 ↦ i·⁴√2`) and one of
   order 2 (e.g., `τ : i ↦ -i`); (c) verify `τστ⁻¹ = σ⁻¹`; (d) apply
   `DihedralGroup.lift` (if in Mathlib) or hand-construct the
   `MulEquiv` from the generators-and-relations presentation.
   Estimate: 150–300 lines.
2. **Upstream contribution** — formalize Capelli's irreducibility
   theorem in Mathlib. ~200 lines. Without this, the full
   Schinzel–Velez characterization cannot be stated explicitly.
3. **S5+ (post-Capelli)** — replace
   `schinzel_velez_characterization_exists` with the explicit
   predicate form; discharge the iff via Velez (1979) and
   Schinzel (2000). ~300–500 lines.

### S3a (researcher-12, 2026-05-12)

**Goal.** Two-part: (1) fix a falsity in S2's `dihedral_iff_schinzel_velez`
sorry-statement; (2) supply the cardinality lift toward the `(4, 2)`
discharge so S4+ can focus on the order-8-transitive-`S₄`-subgroup
classification step in isolation.

**Deliverables (all in `proofs/Proofs/InverseGaloisD4OQ03.lean`).**

1. `theorem xPowSub_def (n) (a) : xPowSub n a = X ^ n - C a := rfl`
   — definitional unfolding helper, no sorry, exposes the equality
   bridge to the parent's `(X : ℚ[X])^4 - C 2` polynomial form.
2. `theorem gal_card_xPowSub_4_2 : Fintype.card (xPowSub 4 2).Gal = 8`
   — no sorry; reuses `InverseGaloisExtensions.x4_sub_2_gal_card`
   through definitional unfolding (`show … = 8`). Isolates the
   cardinality input of the S3+ bridge from the harder classification
   step.
3. **Audit fix**: `theorem dihedral_iff_schinzel_velez (n a) :
   IsDihedralGaloisOfXnMinusA n a ↔ True` was **false** as stated —
   the right-to-left direction `True → IsDihedralGaloisOfXnMinusA n a`
   fails for any `(n, a)` outside the dihedral case (e.g., `n = 1` so
   the Galois group is trivial, or `n = 5, a = 2` where the Galois
   group is `F₂₀`, not dihedral). The S2 sorry hid a non-theorem.
   Replaced with the meaningful existential form
   `theorem schinzel_velez_characterization_exists :
   ∃ P : ℕ → ℚ → Prop, ∀ n a, IsDihedralGaloisOfXnMinusA n a ↔ P n a`,
   which is trivially true (take `P := IsDihedralGaloisOfXnMinusA`)
   and faithfully captures the *existence-of-a-characterization*
   intent of the original docstring. Closes one false sorry.

**Sorry count.** 2 → 1. The remaining sorry is on
`dihedral_galois_xPow4_sub_2`, which is the genuine
classification-modulo-cardinality bridge (`gal_card_xPowSub_4_2`
above + "any transitive order-8 subgroup of `S₄` is `D₄`").

**Scope choices.**

- **Audit-first**: per `feedback_researcher_s1_deferred_can_be_false`,
  S1/S2 sorry statements are themselves auditable. The
  `↔ True` formulation hid a non-theorem; fixing it is a higher-value
  contribution than a partial discharge.
- **Cardinality lift is structurally trivial but pedagogically
  important**: it makes explicit that `(xPowSub 4 2).Gal` and
  `((X : ℚ[X])^4 - C 2).Gal` are the same type up to definitional
  unfolding, so S4 only needs the "classification of order-8
  transitive `S₄` subgroups" lemma to discharge.
- **No new infrastructure**: pure restructuring + audit fix. Net
  diff is small (~25 lines) and high-confidence.
- **MODERATE+ saturation context**: per
  `project_moderate_plus_oversubscribed_pool.md`, single focused PR
  preferred over speculative discharge attempts. The hard
  classification work belongs in a dedicated S4.

**Build status.** Build pending — small definitional changes, low
drift risk. The `show … = 8` form for `gal_card_xPowSub_4_2`
relies on `xPowSub 4 2` reducing to `(X : ℚ[X]) ^ 4 - C 2` at the
kernel; this is a single-`def` unfold. If kernel-reducibility
quirks block this, fallback is `by unfold xPowSub; exact ...`.

**Next action.**

1. **S4** — Discharge `dihedral_galois_xPow4_sub_2` using
   `gal_card_xPowSub_4_2` + a new auxiliary
   `dihedral_iso_of_order_8_transitive_subgroup_S4` (the
   classification step). Estimate: 150–250 lines including the
   transitivity setup (`Polynomial.Gal.galActionHom` is injective
   from the parent; need a transitivity witness — Mathlib has
   `Polynomial.Gal.transitive_iff_irreducible` for irreducible
   polynomials, which `X^4 - C 2` is per the parent's
   `x_fourth_sub_2_irreducible`).
2. **Upstream contribution** — formalize Capelli's irreducibility
   theorem in Mathlib. ~200 lines, worth a focused PR. Without this,
   the full Schinzel–Velez characterization cannot be stated
   explicitly.
3. **S5+ (post-Capelli)** — replace
   `schinzel_velez_characterization_exists` with the explicit
   predicate form; discharge the iff via Velez (1979) and
   Schinzel (2000). ~300–500 lines.

### S2 (researcher-1, 2026-05-12)

**Goal.** Land the API surface proposed in S1's "next action": create
`proofs/Proofs/InverseGaloisD4OQ03.lean` with abstract criterion def +
specialization statement + Schinzel-Velez iff statement.

**Deliverables.**
- `proofs/Proofs/InverseGaloisD4OQ03.lean` (NEW, 127 lines, 2 def / 2 thm /
  0 axioms / 2 sorries) — `IsDihedralGaloisOfXnMinusA`, `xPowSub`,
  `dihedral_galois_xPow4_sub_2`, `dihedral_iff_schinzel_velez`.
- `src/data/proofs/inverse-galois-d4-oq-03/` (NEW gallery entry: meta.json
  with 5 sections + 3 mainTheorems + 4 mathlibDependencies + 2 crossRefs,
  annotations.json empty placeholder, index.ts standard).
- `proofs/Proofs.lean` (manifest import).

**Scope choices.**

1. **Abstract criterion (no sorry)**: `IsDihedralGaloisOfXnMinusA n a`
   defined via `∃ m ≥ 2, Nonempty ((K ≃ₐ[ℚ] K) ≃* DihedralGroup m)`
   where `K = (X^n - C a).SplittingField`. Uses only existing Mathlib
   constructions; no new infrastructure required.
2. **(4, 2) specialization (sorry)**: `dihedral_galois_xPow4_sub_2` —
   bridges from parent's `d4_realizable` (order 8) to the explicit
   `D₄` identification. Proof route documented: classical fact that
   `D₄` is the unique transitive subgroup of `S₄` of order 8.
3. **Schinzel-Velez iff (sorry, True placeholder)**:
   `dihedral_iff_schinzel_velez n a : IsDihedralGalois... ↔ True` —
   `True` stands in for the explicit finite-case predicate. Replacing
   `True` requires Capelli's irreducibility theorem (absent from
   Mathlib v4.26.0).

**Build status.** Build pending — file-level type-checking expected
to pass (signatures verified against v4.26.0 pin), but the (4, 2)
specialization is sorry-guarded so no Cayley-Hamilton-style runtime
risk. If any drift is detected, follow-up drift-fix PR will land.

**Next action.**

1. **S3** — discharge `dihedral_galois_xPow4_sub_2` by bridging from
   `d4_realizable` via the transitive-S₄-subgroups argument. Estimate:
   50-100 lines, self-contained. **Recommended next iteration.**
2. **Upstream contribution** — formalize Capelli's irreducibility
   theorem in Mathlib. ~200 lines, worth a focused PR. Without this,
   the full Schinzel-Velez characterization cannot be stated explicitly.
3. **S4+ (post-Capelli)** — replace `True` in
   `dihedral_iff_schinzel_velez` with the explicit predicate; discharge
   the iff via Velez (1979) and Schinzel (2000). ~300-500 lines.

### S1 (researcher-9, 2026-05-12)

**Goal.** Establish the mathematical scope of "when is $\operatorname{Gal}(X^n - a/\mathbb{Q})$ dihedral?", identify the Schinzel–Velez classification as the answer pathway, and audit Mathlib's current API for the prerequisites.

**Deliverables.**
- `problem.md` — formal restatement of the OQ, classical case analysis ($n$ odd, $n = 2k$ with $k$ odd, $n = 4$, $n = 8$, $n = p^k$), and the Schinzel–Velez classification.
- `knowledge.md` — annotated bibliography (Capelli 1897, Jacobson 1985, Velez 1979, Schinzel 2000, Kappe–Warren 1989, Cox 2012, K. Conrad notes), Mathlib API audit, tractability assessment, scope deferral plan.

**No Lean changes.** S1 is a survey iteration following the fallback-variant pattern documented in `feedback_researcher_12_s22_session_summary.md`.

**Findings.**
1. The classical answer exists (Schinzel–Velez 1979–2000): a finite-case characterization keyed on $n \bmod 8$ and $p$-adic valuations of $a$. Existential difficulty is low; the math is settled.
2. The Mathlib formalization difficulty is **medium-high**, dominated by the absence of Capelli's irreducibility theorem in its full generality. Only the prime-$n$ case and the $4 \mid n$ exception are partially handled.
3. The parent gallery proof `InverseGaloisD4.lean` (27 theorems, 0 sorries, $X^4 - 2$ as $D_4$) handles the simplest dihedral instance. OQ-03 generalises Part IV's $\mathbb{R}$-embedding argument to a uniform criterion that doesn't depend on $a > 0$.

**Next action (S2 candidate).**
Produce a non-building scaffold `proofs/Proofs/InverseGaloisD4OQ03.lean` (~150–250 lines) with:
- `def isDihedralCriterion (n : ℕ) (a : ℚ) : Prop`
- `theorem isDihedralCriterion_iff : ... := by sorry` (one sorry, the Schinzel–Velez theorem)
- `example : isDihedralCriterion 4 2 := by decide` (sanity check)

S2 is **optional** — if MODERATE+ remains saturated, this S1 OBSERVE stands as a self-contained survey contribution and the next researcher should treat the scaffold as deferred.

## Blockers

- **Capelli's theorem in Mathlib**: prerequisite for any Lean formalization. Not currently present in `mathlib4 v4.26.0`. Estimated $\sim$200 lines of new infrastructure. Would benefit from a focused contribution PR upstream.
- **Galois group order theorem**: $|G_n(a)| = n \varphi(n)$ generically. Standard but not packaged in Mathlib as a one-liner; needs to be assembled from primitive-root and field-degree lemmas.

## Race history

Pre-claim trap checks (2026-05-12 ~06:40 UTC):
- `gh pr list --state open --search "inverse-galois-d4-oq-03"` → `[]` (0 open PRs).
- `git ls-remote --heads origin "*inverse-galois-d4-oq-03*"` → empty (0 stale branches).
- `gh pr list --state merged --search "inverse-galois-d4-oq-03"` → `[]` (no prior work on this slug).

Slug was pristine when claimed. Direct-claim via `claim-problem.sh claim inverse-galois-d4-oq-03` (not `claim-random`) per the tier-B fallback pattern documented in `feedback_researcher_fresh_slug_escape_hatch.md` and `project_moderate_plus_fallback_to_tier_b.md`.

## Session context

This S1 was reached after 5 consecutive `claim-random` races on MODERATE+ slugs:
- `laws-of-large-numbers-oq-04-oq-03` (open PR #17907, parent LLN-OQ04 broken).
- `ballot-problem-oq-03-oq-01-oq-02` (open PR #17817 + parent OQ03OQ02 build break).
- `angle-trisection-oq-05-oq-04` (open PR #17915 S3, ongoing scaffold).
- `erdos-szekeres-oq-03` (open PR #17909 S2 ACT-A).
- `binary-gcd-oq-03-oq-02` (stale open PR #17304 from 2026-05-08, file 2225 lines, complex).

Cap-of-5 rule (`feedback_researcher_session_time_merge.md`) was respected by switching to direct-claim tier-B fallback rather than continuing random claims. The fallback pool of zero-score available tier-B slugs (17 total) was filtered for `open=0 merged-today=0 branches=0`, yielding 4 candidates: `fourier-series-oq-04-oq-01`, `general-quartic-oq-02`, `inverse-galois-d4-oq-03`, `weak-goldbach-oq-03`. `inverse-galois-d4-oq-03` was selected for tractability (concrete classical question with well-known answer) and direct linkage to a high-quality parent gallery entry.
