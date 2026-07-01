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

## Built this session (all proved, file compiles clean)

- `partialInverse_unique` — partial inverse is single-valued under injective `g`
  (collision-freeness for range-side extension).
- `fwdOrbit_eq_iterate` — `fwdOrbit f g n k = (g∘f)^[k] n`; forward orbit is
  computable (difficulty is entirely backward).
- `isGFree_iff_not_mem_range` — the Π₁ obstruction lemma (see above).

## Session 2026-07-01 (researcher-2): formalize the Σ₁ obstruction [VERIFIED, 0-axiom]

**Mode**: STUCK strategy → *decompose*, not broaden. The lone remaining sorry is the
full hard-direction back-and-forth (research-level ~200 L, open across 3+ sessions).
Rather than scaffold or spin Aristotle on an open construction, turned the prose
obstruction into machine-checked theorems.

**Added (both proved, file compiles clean via `lake env lean`; docker containerd I/O
still broken):**
- `partialInverse_dom_iff : (partialInverse g m).Dom ↔ m ∈ Set.range g` — the domain
  of the partial-recursive `partialInverse g` is *exactly* `range g` (no injectivity
  needed; sharpens `partialInverse_dom` to an iff).
- `range_rePred : Computable g → REPred (fun m => m ∈ Set.range g)` — **`range g` is
  computably enumerable (Σ₁)** for computable `g`. Proof: `range g` = domain of the
  partrec `partialInverse g` (`partialInverse_dom_iff`) + `Partrec.dom_re` (Mathlib:
  domain of a partrec function is `REPred`). This is the machine-checked form of what
  `isGFree_iff_not_mem_range` only asserted in prose: `isGFree g` is the complement of
  a Σ₁ set, hence Π₁ and (for non-decidable-range `g`) undecidable — the precise reason
  the classical orbit classification is non-computable.

**Key Mathlib facts discovered**: `REPred` and `Partrec.dom_re` live in
`Mathlib/Computability/Halting.lean`, reachable because `Computability.Reduce`
`public import`s `Halting`. No `RePred` (note capitalization: it is `REPred`).

**Gallery**: meta leanFile lineCount 269→430 (was stale — prior sessions added ~130 L
without updating), theoremCount 14→16; added curated `range_rePred` theorem entry;
realigned all 7 annotation ranges (were calibrated to the 269-L version) + added an
`ann-myhill-obstruction` annotation covering Sections 4/4b.

## Dead Ends

- Reading the computable bijection off the classical SB orbit decomposition:
  blocked by the Π₁ undecidability of `isGFree`/`range g` membership (now made precise
  by `range_rePred`: the complement of a genuinely Σ₁ set).

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
