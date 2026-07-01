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

## Session (researcher-1, 2026-07-01)

- `fwdOrbit_computable` — PROVED (0-axiom): `fwdOrbit f g` is `Computable₂` for
  computable `f, g`, via `Computable.nat_rec` (identify the orbit with `Nat.rec` on
  the iteration count; step `IH ↦ g (f IH)` is computable). This closes the prose
  gap on `fwdOrbit_eq_iterate` with an actual machine-checked `Computable` certificate
  and confirms the computability obstruction is *entirely* in the backward direction
  (`isGFree`/`range g`, Π₁). File: 396→422 lines, +1 theorem; main hard-direction
  sorry (`myhill_isomorphism` →) UNCHANGED — still needs the stage-wise back-and-forth
  builder (knowledge Next Steps 1–3). Build: Docker down; verify via
  `elan run leanprover/lean4:v4.26.0 lean` with LEAN_PATH→main oleans (NOT homebrew
  lean 4.31, which gives incompatible-header errors).

## Built 07-01 (researcher-1) — finite-matching layer + atomic back-and-forth steps

Added Section 4c to SchroederBernsteinOQ03.lean (all VERIFIED, 0-axiom: propext/Quot.sound
only; no sorryAx, no ofReduceBool). Formalizes the finite partial injection the stage-wise
construction maintains, as an association `List (ℕ × ℕ)`:

- `IsMatching L` := `(mDom L).Nodup ∧ (mRan L).Nodup` — partial injection in both coords.
- `matching_functional` / `matching_cofunctional` — domain (resp. range) determines the
  partner; proved via `List.inj_on_of_nodup_map` (v4.26). So a matching IS a partial bijection.
- `MatchingCorr p q L` := every recorded pair satisfies `p ab.1 ↔ q ab.2`; `matchingCorr_cons`.
- `isMatching_cons` — prepending a pair fresh on both sides preserves the matching property.
- `matching_step_f` (even-stage domain step): add `(a, f a)` when `a ∉ dom`, `f a ∉ ran`;
  correspondence preserved by the f-reduction `p a ↔ q (f a)`.
- `matching_step_g` (odd-stage range step): add `(g c, c)` when `c ∉ ran`, `g c ∉ dom`;
  correspondence preserved by the g-reduction `q c ↔ p (g c)` (used as `.symm`).
- `matching_length_cons` — each step grows length by 1 (the well-founded measure).

The correspondence is preserved *structurally* — the map is never tested against the
(possibly non-computable) predicates `p`, `q` directly; membership routes through `f`/`g`.

REMAINING OPEN (unchanged): `myhill_isomorphism` hard-direction sorry. What's isolated now
is precisely the **scheduler** that resolves a COLLISION — when the naive target `f a`
(resp. preimage `g c`) is already used — by chasing the alternating `f`/`g` chain to a
fresh endpoint. The atomic fresh-case steps are done; the collision-chasing recursion +
its computability (bounded search for the entering stage) is the residual work.

Gotchas (v4.26): `List.not_mem_nil` here has type `a ∈ [] → False` (not `¬ ...`), so use
`by intro _ h; simp at h` for the empty-list vacuous case. `List.inj_on_of_nodup_map` takes
the `Nodup (map f l)` proof + two membership proofs + `f x = f y`, returns `x = y`.
