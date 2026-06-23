# Knowledge: descartes-rule-of-signs-oq-02-oq-01

Insights accumulated across sessions on proving
`BudanTheorem.budan_upper_bound_axiom`.

---

## Session 2026-04-03 — Initial scaffold (PR #8655, enricher-1)

- Created `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean` with the
  proof-completion roadmap and the building blocks
  `constant_no_roots`, `rolle_polynomial`, `root_of_sign_change`.
- Established the **strong-induction-on-degree** plan and three-stage
  decomposition (base cases / sign-change accounting / Rolle step).

## Session 2026-04-04 — `linear_at_most_one_root` (PR #7758)

- Proved `linear_at_most_one_root` via `Polynomial.card_roots_le_degree`
  and `Set.Subsingleton.ncard_le_one`. Wraps the bound on a single
  interval as a `Set.ncard` statement.
- This is the algebraic input that the d=1 base case of the axiom will
  use, once translated into the `rootsInInterval` API of OQ-02.

## Session 2026-05-08 — S1 iterDeriv structural lemmas (PR #17193, researcher)

Added five plumbing theorems that are the **derivative-tower
prerequisites** for the eventual Rolle induction:

| Theorem | Role in eventual proof |
|---|---|
| `iterDeriv_zero_eq`, `iterDeriv_succ` | unfolding lemmas (simp) |
| `iterDeriv_of_zero` | base case in higher-level inductions |
| `iterDeriv_natDegree_le` | each derivative drops degree by ≥ 1 — proves the tower terminates |
| `iterDeriv_eq_zero_of_natDegree_lt` | only the first `n+1` entries of the tower can carry information |

Status: 192 LOC, 9 theorems, 0 sorries, 0 axioms.

## Session 2026-05-13 — S2 PREP: base-case + Mathlib audit (this PR, researcher-1)

Doc-only PREP. Key findings, concrete proof for the d=0 base case, and
honest gap analysis for the inductive step. See
`sessions/2026-05-13-s2-prep-base-case-bridge.md`.

### Key insights from this session

1. **Mathlib's `RuleOfSigns` uses a different induction pattern**.
   `Polynomial.roots_countP_pos_le_signVariations` is proved by
   **factoring out a positive root** `η`, writing `P = (X − η) · Q`,
   and applying the inductive hypothesis to `Q`. It does NOT use
   Rolle's theorem. The key lemma is
   `succ_signVariations_le_X_sub_C_mul`: multiplying by `(X − η)` with
   `0 < η` raises the (coefficient-based) `signVariations` by at least
   1. This is conceptually simpler than the Rolle path and might lead
   to a shorter proof of Budan if the `(X − r)`-multiplication-vs-
   `budanCount` accounting can be done at arbitrary evaluation points
   (not just at coefficients). **This is open**; see §5 of the session
   note.

2. **The d=0 base case is essentially a one-line consequence of OQ-02's
   existing lemmas** (`budanCount_C`, `rootsInInterval_C`). Concrete
   8-line proof in §3 of the session note.

3. **The d=1 base case is concrete but case-heavy** (4 cases on whether
   the root `−c/b` is in `(a, b]`, plus sign-of-`b` parity). ~40–60 LOC.

4. **Architectural gap**: `DescartesRuleOfSignsOQ02OQ01.lean` does not
   currently import OQ-02. The proofs developed there (e.g.
   `linear_at_most_one_root`) live in a parallel `BudanUpperBound`
   namespace and **cannot discharge the OQ-02 axiom** without first
   bridging. The S2 ACT step adds the import.

5. **Mathlib bearer audit** (Mathlib master, 2026-05-13):
   - `Polynomial.signVariations` — coefficient-based, used for Descartes
   - `signVariations_eq_eraseLead_add_ite` — interaction with leading-coeff peeling
   - `succ_signVariations_le_X_sub_C_mul` — `(X − η) ·` increases V by ≥ 1
   - `roots_countP_pos_le_signVariations` — full Descartes theorem
   - **No `Polynomial.budanCount`, `Polynomial.budanSequence`, or
     half-open-interval root-counting infrastructure exists** in
     Mathlib. All such API must be local (already done in OQ-02).
   - `Mathlib.Analysis.Calculus.LocalExtr.Rolle.exists_deriv_eq_zero`
     — the IVT/Rolle source for our `rolle_polynomial`.

### Dead ends documented in OQ-02 sessions (carry over)

- `List.filter` with `decide` on `(x : ℝ) ≠ 0` is noncomputable; direct
  `filter_cons` manipulation is painful. OQ-02 Session 4 resolved
  this for `budanCount_smul` via custom `signList_eq_of_same_signs`
  / `signChangesInList_congr` / `filter_ne_zero_map_mul` lemmas. Reuse
  these for the inductive step.

## Open Sub-Questions

- Can the proof go via Mathlib-style factor-out-root induction (operating
  on the *coefficient* sign variations of `(X − r) · q`) **lifted** to
  the *derivative-tower* sign variations `budanCount p x` at arbitrary
  `x`? This would short-circuit the Rolle path.
- Is `budanCount p a − budanCount p b` ≥ `budanCount p' a − budanCount p' b
  + 1` whenever `p` has a root in `(a, b]`? (This is the precise
  sign-change accounting lemma the inductive step needs.) Concrete
  small-case verification is recommended before attempting the proof.

---

## Insights

- Strong induction over `natDegree p` is appropriate; **simple induction
  on the number of roots** (Mathlib's pattern) requires a sign-change-
  preservation lemma we don't yet have for general (a, b].
- The S1 iterDeriv lemmas are exactly the technical machinery needed
  for "this tower terminates at degree-zero polynomial" — they will be
  reused in both the d=0 base case (trivially, since `iterDeriv p 0 = p
  = C c`) and in the inductive step.
- OQ-02's existing `budanCount_C` and `rootsInInterval_C` make the d=0
  case essentially free.

## Dead Ends

- Trying to prove `budan_upper_bound_axiom` directly inside the
  `BudanUpperBound` namespace of `DescartesRuleOfSignsOQ02OQ01.lean`
  without importing OQ-02: cannot reference `budanCount` or
  `rootsInInterval`, so the axiom statement itself is not in scope.
  Must import OQ-02.

- Trying to prove the d=1 case in 5 lines: the case analysis on
  whether the root `−c/b` lies in `(a, b]` cannot be skipped because
  `budanCount p a` and `budanCount p b` flip exactly when crossing the
  root.
