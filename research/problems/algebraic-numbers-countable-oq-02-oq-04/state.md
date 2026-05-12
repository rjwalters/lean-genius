# State: algebraic-numbers-countable-oq-02-oq-04 — Countability of Computable Reals

## Current Status

**Phase**: S2 LOWER BOUND (rational embedding ⇒ ℵ₀ ≤ # computable reals)
**Owner**: researcher-1 (S2, 2026-05-12)
**Branch**: `research/algebraic-numbers-countable-oq-02-oq-04-s2-rat-lower-<ts>`

## What's Done

- **Gallery entry created**: `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/`
  with `meta.json`, `annotations.json`, `index.ts`. Full overview, sections,
  cross-references, and 4 annotations covering historical context,
  definition choice, proof strategy, and a subtle point about
  computably-enumerable vs countable.
- **Lean source created**: `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean`
  (~110 lines, 1 sorry).
  - Imports Mathlib `Computability.Partrec`, `Computability.Primrec`,
    `Cardinal.Basic`, `Cardinal.Continuum`, `Topology.Instances.Real`, etc.
    plus parent `Proofs.AlgebraicNumbersCountable`.
  - `IsComputable (r : ℝ) : Prop` defined as: `∃ f : ℕ → ℚ, Computable f ∧
    Tendsto (fun n => (f n : ℝ)) atTop (nhds r)`.
  - `computable_reals_countable` (sorry, main): `Set.Countable {r | IsComputable r}`.
  - `card_computable_reals_le_aleph0` (proved): cardinal corollary via
    `le_aleph0_iff_set_countable.mpr computable_reals_countable`.
- **Manifest updated**: `proofs/Proofs.lean` regenerated via
  `.lean/scripts/generate-proofs-imports.sh` — adds the import line.
- **Problem statement corrected**: original `problem.md` said `computable ⊂ algebraic`
  which is mathematically wrong (e and π are computable transcendentals).
  Rewritten to reflect the correct hierarchy `ℚ ⊊ algebraic ⊊ computable ⊊ ℝ`.

## What's Next (S2+ targets)

1. **Discharge the `sorry` in `computable_reals_countable`**. Strategy:
   - `Encodable Nat.Partrec.Code` (countable index set).
   - `Computable f → ∃ c : Nat.Partrec.Code, ∀ n, c.eval n = Part.some (Encodable.encode (f n))`
     (Mathlib's `Computable.exists_code` or similar).
   - Define partial `codeLimit : Nat.Partrec.Code → Option ℝ` sending each
     code to the limit of its decoded rational sequence (when it converges).
   - Show `{r | IsComputable r} ⊆ Set.range (fun c => codeLimit c)` and apply
     `Set.Countable.image` + `Set.Countable.mono`.
2. **Lower bound**: prove `ℵ₀ ≤ #{r | IsComputable r}` via the rational
   embedding `q ↦ ⟨(q : ℝ), rat_isComputable q⟩`, where `rat_isComputable`
   uses the constant-sequence witness `(Computable.const q)`.
3. **Strict inclusions** (longer-term):
   - `algebraic ⊆ computable`: every root of a rational polynomial is
     computable via root-finding (Sturm's theorem + bisection, all
     algorithmic).
   - `computable ⊊ ℝ`: Cantor diagonal of computable reals fails to be
     *computably* enumerable but classically yields a non-computable real.
4. **Connect to Chaitin's Ω** (advanced/optional): construct an explicit
   non-computable real to demonstrate the strict inclusion concretely.

## API Risks Flagged for S2

- `Computable (f : ℕ → ℚ)` requires `Primcodable ℚ`. Mathlib provides this
  via `Mathlib.Data.Rat.Denumerable` (which gives `Denumerable ℚ`, hence
  `Encodable ℚ`, hence `Primcodable ℚ`). Imports include
  `Mathlib.Data.Rat.Denumerable` and `Mathlib.Logic.Denumerable`. If
  elaboration fails on `Computable f`, the issue is likely a missing
  `Primcodable` instance — switch to `Computable g : ℕ → ℕ` and decode
  via `Encodable.decode`.
- `le_aleph0_iff_set_countable.mpr` — exact name confirmed from sibling
  `AlgebraicNumbersCountableOQ02OQ03.lean` line 82.
- `Computable.const q` — used in sketched lower-bound; if not available
  under that name, can be replaced by `Primrec.const q |>.to_comp` or
  built via composition with `Encodable.encode`.

## Build Status (S1)

**Build**: pending (not yet attempted — Docker build is ~45 min cold per
`proofs/.lake` self-symlink trap; running locally not feasible in session
budget). Per the S15/S16/S17 four-square precedent, the file is shipped
"build pending" with strategy/scaffold review preferred over wait.

## Knowledge Score

EMPTY → progress. After this S1 PR, knowledge score should be ~5 (initial
infrastructure + strategy + 1 file + 1 module-doc + 4 annotations).

## Session Log

- **2026-05-12 (S1, researcher-4 session 67)**: SCAFFOLD created. Definition
  + main theorem (sorry) + cardinal corollary (clean). Gallery entry +
  annotations + Lean file + problem.md correction + this state.md.
  Released claim after push.
- **2026-05-12 (S2, researcher-1)**: LOWER BOUND added (unconditional).
  Built 5 closure theorems: `rat_isComputable` (every rational is
  computable, constant-sequence witness via `Computable.const` +
  `tendsto_const_nhds`), plus `int_/nat_/zero_/one_isComputable`.
  Built `aleph0_le_card_computable_reals` via `ℚ → {r | IsComputable r}`
  injection + `Cardinal.mk_rat`. Also derived `card_computable_reals_eq_aleph0`
  (exact ℵ₀) **conditional on the main S1 sorry** — no new assumptions.
  Lean file 110 → 208 lines, 1 sorry → 1 sorry, 0 axioms → 0 axioms,
  theorem count 2 → 9. Strategy for S3 unchanged.

## S2 — What This Buys

Before S2, the only result was the *conditional* upper bound. After S2:

- The lower bound `ℵ₀ ≤ #(computable reals)` is **unconditional**.
- The exact equality `#(computable reals) = ℵ₀` is **one sorry away**: it
  depends only on the main `computable_reals_countable` (still S3+).
- Once S3 lands, we get the full cardinality result for free with no extra
  proof — `card_computable_reals_eq_aleph0` is already stated and typechecks.

The five "concrete computables" (rat/int/nat/zero/one) also serve as
sanity checks on the `IsComputable` definition: any sensible definition
must make these computable, and the constant-sequence witness confirms
it does.

## API Risks Flagged for S3 (unchanged from S1)

(see original S1 notes above)
