# Knowledge Base: schroeder-bernstein-oq-03 (Myhill Isomorphism Theorem)

## Problem Understanding

Target: `OneOneEquiv p q ↔ ∃ e : ℕ ≃ ℕ, e.Computable ∧ ∀ n, p n ↔ q (e n)`.
The `←` (easy) direction is proved (`myhill_easy`). The `→` (hard) direction —
two computable injections yield a *computable* permutation — is the OPEN target
(one `sorry` in `myhill_isomorphism`).

## Insights

- Mathlib provides `OneOneReducible` (`≤₁`), `OneOneEquiv`, `ManyOneEquiv`
  (`Mathlib/Computability/Reduce.lean`) but does **not** contain Myhill's
  isomorphism theorem. The only "Myhill" file is `MyhillNerode.lean` (regular
  languages, unrelated). This is a genuine gap.

- **Core obstruction (why naive SB fails).** `isGFree g n := ∀ k, g k ≠ n` is
  exactly `n ∉ Set.range g` (proved: `isGFree_iff_not_mem_range`). For a merely
  *computable* injection `g`, `range g` is only c.e. (`Σ₁`), so its complement
  `isGFree g` is `Π₁` and undecidable. The classical Schröder–Bernstein orbit-type
  classification needs to decide, for each `n`, whether the backward chain leaves
  `range g` — i.e. it needs `isGFree`, which is not computable. Hence the classical
  orbit construction does **not** give a computable bijection, and the Section-4
  "Type A/B/C" sketch in the Lean file is the *wrong* (non-computable) approach.

- **Correct route.** The stage-wise finite back-and-forth (priority) construction
  (Rogers §7.4): at each stage extend a finite partial injection by one element,
  using `f` on the domain side and `partialInverse g` on the range side. Each stage
  is a *bounded* search — it never decides `range g` — so the result is computable.

- `p, q` are arbitrary predicates, **not** computable. The construction must route
  membership through the computable reductions `f, g` structurally; it must never
  test `p n`/`q v` directly. `f` maps `p`-membership to `q`-membership and `g` the
  reverse, so the correspondence is preserved by construction.

## Built 07-01 (researcher-11) — Σ₁/Π₁ complexity made machine-checked

The docstrings repeatedly assert "`range g` is c.e. (`Σ₁`), so `isGFree g` is `Π₁`"
purely in prose. Turned that into actual theorems (all VERIFIED, 0-axiom: only
propext/Classical.choice/Quot.sound; no sorryAx, no ofReduceBool):

- `partialInverse_dom_iff_mem_range` — `(partialInverse g m).Dom ↔ m ∈ range g`
  (no injectivity needed; identifies `range g` with a partrec function's domain).
- `mem_range_re` — `Computable g → REPred (· ∈ range g)`, i.e. `range g` is c.e.
  Proof: `(partialInverse_partrec hg).dom_re.of_eq …`. `REPred`/`Partrec.dom_re`
  live in `Mathlib.Computability.Halting` (added to imports).
- `not_isGFree_re` — `Computable g → REPred (¬ isGFree g ·)`; combined with
  `isGFree_iff_not_mem_range`, this says `isGFree g` is co-c.e. (`Π₁`).

This substantiates *why* the naive orbit classification is non-computable with a
Lean proof rather than a comment. The main hard-direction sorry (`myhill_isomorphism`,
the stage-wise back-and-forth) remains OPEN — NOT closed this session.

Caution on the "decidable ranges → computable SB" partial win (old Next Step #4):
even with `range f`, `range g` decidable the backward chain can be genuinely infinite,
and distinguishing "infinite chain" from "eventually hits an f-free element" needs an
unbounded search — so decidable ranges alone do NOT obviously give a computable
classification. Treat that suggested milestone with care.

## Built earlier (all proved, file compiles clean)

- `partialInverse_unique` — partial inverse is single-valued under injective `g`
  (collision-freeness for range-side extension).
- `fwdOrbit_eq_iterate` — `fwdOrbit f g n k = (g∘f)^[k] n`; forward orbit is
  computable (difficulty is entirely backward).
- `isGFree_iff_not_mem_range` — the Π₁ obstruction lemma (see above).

## Dead Ends

- Reading the computable bijection off the classical SB orbit decomposition:
  blocked by the Π₁ undecidability of `isGFree`/`range g` membership.

## Next Steps

1. Formalize the stage-wise partial-bijection builder (`List (ℕ × ℕ)` by recursion
   on the stage index), extending by `f` (domain) / `partialInverse g` (range).
2. Prove stage invariants: injectivity (via `partialInverse_unique` + `f` injective),
   correspondence `p ↔ q` preserved, domain/range exhaustion (`n` covered by stage
   `2n+1`).
3. Computability of the permutation from the computable builder + bounded search for
   the entering stage.
4. Tractable partial win to consider first: classical SB bijection *is* computable
   when `range f` and `range g` are decidable — isolates the obstruction cleanly.
