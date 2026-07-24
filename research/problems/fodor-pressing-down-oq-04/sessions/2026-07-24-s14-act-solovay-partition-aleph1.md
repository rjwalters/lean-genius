# S14 ACT — Solovay's partition theorem at ω₁ (Part XIII)

**Date**: 2026-07-24
**Agent**: researcher-2
**Mode**: REVISIT (RICH, score 38)
**Outcome**: `solovay_partition_aleph1` proved — the pinned OQ target at κ = ℵ₁.

## What was proved

Part XIII (four theorems, 0 sorries, 0 axioms):

1. `exists_unbounded_disjoint_stationary_fibers` (general regular uncountable
   κ, ω-cofinal stationary S): there is an index set `C` unbounded below
   `κ.ord` and a family `T` of pairwise disjoint stationary subsets of `S`
   indexed by `C`.
2. `exhaustive_partition_of_disjoint_family`: packaging — absorb the unused
   remainder `S \ ⋃ T₀` into one designated piece; disjointness and
   stationarity survive, and the union becomes exactly `S`.
3. `solovay_partition_of_cof_omega`: exhaustive partition for ω-cofinal
   stationary sets below any regular uncountable κ.
4. `solovay_partition_aleph1`: **every stationary S ⊆ ω₁ is the disjoint
   union of stationary pieces indexed by a set unbounded below ω₁** —
   Solovay 1971 / Jech 8.10 at κ = ℵ₁.

## The key idea (why S13's "DEEP" verdict was wrong)

S13 predicted the ℵ₁-piece partition needs "limit-stage ideas beyond the
ω-iteration" — true **for the iterate-the-binary-split route** (the remainder
chain `⋂ₙ Rₙ` need not be stationary at limit stages). But no iteration is
needed at all: the S12 pigeonhole index `n` makes EVERY high-fiber
`{α ∈ S | η ≤ omegaSeq α n}` stationary simultaneously, so applying Fodor
once per η < κ.ord yields constants `c η ≥ η` (from any fiber point) with
stationary fibers `S ∩ (omegaSeq · n)⁻¹' {c η}`. Fibers of a *single* map at
distinct values are automatically pairwise disjoint — no bookkeeping. The
value set `{c η}` is unbounded below κ.ord because `c η ≥ η`. All pieces are
produced simultaneously; the limit-stage obstruction never arises.

Exhaustiveness is then trivial: dump `S \ ⋃ fibers` (including all non-limit
points of S) into one piece — a superset of a stationary set is stationary.

## Size disclosure (honest scoping)

The "ℵ₁-many pieces" content is carried by `IsUnboundedBelow C (ℵ₁).ord`
(file-native vocabulary): an unbounded subset of ω₁ has cardinality ℵ₁ since
any smaller family's supremum would be bounded (`cof ω₁ = ℵ₁`). The
`Cardinal.mk`-level equality `#↥C = ℵ₁` is NOT formalized — `Ordinal.{0} :
Type 1` puts `#↥C` in `Cardinal.{1}`, requiring universe-lift bookkeeping.
Deliberately left as an optional cosmetic rung.

## Lean notes

- Reused verbatim from Part XI: regressivity data (`omegaSeq_lt`, positivity
  from `IsSuccLimit.bot_lt`), fiber-widening via
  `Set.inter_subset_inter_left`, `η ≤ c` extraction from
  `hfib.nonempty (isSuccLimit_ord hκ.aleph0_le)`.
- `choose!` (not `choose`) on `∀ η, η < κ.ord → ∃ γ, ...` gives a total
  `c : Ordinal → Ordinal` — needed so `C := c '' Set.Iio κ.ord` is a plain
  image set.
- Unboundedness needs *strict* `α < β`: use `c (α+1) ≥ α+1 > α` with
  `(isSuccLimit_ord hκ.aleph0_le).succ_lt` and `lt_add_one`.
- `κ.ord > 0` via `(isSuccLimit_ord hκ.aleph0_le).bot_lt` +
  `rwa [Ordinal.bot_eq_zero]`.
- Partition packaging uses a decidable `if γ = c₀` piece definition;
  `rw [if_pos rfl]/[if_neg h]` after `by_cases`/`subst`, and
  `Set.disjoint_union_left` + a `hrem` helper (remainder disjoint from every
  family member via `Set.mem_biUnion`).
- ω₁ reduction reuses the S12 `hEq` rewrite onto
  `IsStationaryBelow.inter_isLimitOrdinals` +
  `cof_ord_eq_omega0_of_lt_aleph1`.

## Remaining open content (general κ only)

- `cf α = μ > ω` bands: a μ-indexed fundamental-sequence layer replacing
  `omegaSeq` (the Part XIII machinery is otherwise cofinality-agnostic).
- The regular trace `{α ∈ S | cf α = α}` (Jech 8.10's hard case; only
  relevant for κ with stationarily many regulars below, e.g. Mahlo).
- Optional cosmetic: `Cardinal.mk`-level size statement with universe lifts.

## Verification

Docker build `Proofs.FodorPressingDown` — see PR for result.
