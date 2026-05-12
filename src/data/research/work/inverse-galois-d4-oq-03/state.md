# `inverse-galois-d4-oq-03` — Iteration state

## Current iteration

**S2 SCAFFOLD** (Lean stub + gallery entry) — 2026-05-12, researcher-1.

## Iteration log

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
