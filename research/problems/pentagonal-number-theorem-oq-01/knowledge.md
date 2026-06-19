# Pentagonal Number Theorem — OQ-01

## Problem

Euler's pentagonal number theorem expands `∏_{n≥1}(1 - xⁿ) = ∑_{k∈ℤ} (-1)ᵏ x^{g(k)}`
where `g(k) = k(3k-1)/2` are the **generalized pentagonal numbers** (OEIS A001318).
Mathlib has `Nat.Partition` but neither Franklin's involution, partitions into
distinct parts with a parity sign, nor the formal-power-series infinite product
needed for the identity itself.

The OQ candidate arrived with no parent proof, no description, and no Mathlib
bearer for the deep identity — so the scope was defined this session: build the
**number-theoretic foundation** (the index-set theory of pentagonal exponents)
that any formalization of the theorem must consume, and document the deep core as
the open frontier.

## Summary of progress

Self-contained Lean file `proofs/Proofs/PentagonalNumberTheoremOQ01.lean`
(179 lines, 16 theorems, 2 defs, 0 axioms, 0 sorries by construction).

**Headline:** `isGenPent_iff_isSquare` — `m` is a generalized pentagonal number
iff `24·m + 1` is a perfect square. This is the classical recognition criterion
used to enumerate the pentagonal exponents in Euler's partition recurrence
`p(n) = ∑ (-1)^{k-1}(p(n-g_k) + p(n-g_{-k}))`.

- Forward: the algebraic identity `24·g(k)+1 = (6k-1)²` (`linear_combination`).
- Converse: a square `s² = 24m+1` is `≡ 1 (mod 24)`, forcing `s ≡ ±1 (mod 6)`
  (decided in `ZMod 6`), which recovers an index `k` with `6k-1 = ±s`; the value
  is then read off by `mul_left_cancel₀` on `12·(2m) = 12·k(3k-1)`.

Supporting, fully proved:
- `two_dvd_index_mul` / `two_mul_genPent`: `k(3k-1)` is even, exact doubling.
- `genPent_isGenPent`, `genPent_injective` (distinct indices ⇒ distinct values,
  via `(a-b)(3(a+b)-1)=0` and `3(a+b)≠1` over ℤ).
- `isGenPent_nonneg`.
- Concrete values `g(0..±4) = 0,1,2,5,7,12,15,22,26` matching A001318.

## Status of verification

**BUILD-PENDING.** This cycle both verification backends were unavailable:
- Aristotle MCP returned `Resource not found` (404) on every call.
- Docker Lean build was blocked: 10+ concurrent worktree builds contend on the
  shared (symlinked) `proofs/.lake`; a deterministic ProofWidgets cloud-release
  prune error (`Expr.ilean` missing) aborts main-repo builds, and worktree builds
  re-clone Mathlib because `proofs/.lake` symlinks outside the container mount.
  Four attempts (2 background exit-0 but no olean, 1 ProofWidgets-prune failure,
  1 9-min timeout) produced no clean compile.

Every tactic was hand-audited and the algebra numerically verified (Python), but
the file is **not yet machine-checked**. The PR is gated `loom:review-requested`
so it cannot auto-merge as "verified" until a build confirms it.

## Open core (frontier)

The deep identity / partition statement `p_even(n) - p_odd(n) = [n=g(k)]·(-1)ᵏ`
via **Franklin's sign-reversing involution** on partitions into distinct parts.
Requires building (in Mathlib or locally): distinct-part partitions with a parity
sign, Franklin's involution with pentagonal fixed points, and the formal
power-series infinite product. Multi-file effort; this file supplies the index
set it would consume.

## Sessions

### 2026-06-18 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (build-pending)

- Selected pentagonal-number-theorem-oq-01 from a stale-heavy pool (most
  "available" entries were already-landed or hard-from-scratch). Defined scope:
  the index-set foundation + recognition criterion.
- Verified the `24m+1 = (6k-1)²` characterization numerically, then formalized
  it and the supporting theory (179 L, 0 ax, 0 sorry).
- Both backends down → hand-audited all tactics; could not machine-verify.

**Next steps**: (1) re-run docker build when concurrent load drops / submit to
Aristotle when the MCP recovers, to confirm the file compiles; (2) if any tactic
fails, the likely culprits are exact lemma names (`Int.cast_pow`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.mul_ediv_cancel'`) and the `ZMod 6`
`decide` / `push_cast` plumbing in `isGenPent_iff_isSquare`; (3) the genuine
mathematical frontier is Franklin's involution for the deep identity.

### 2026-06-18 (Session 2) — EXTEND

**Mode**: EXTEND · **Outcome**: progress (build-gated PR)

- Session 1's file landed on `main` (#25893, build-verified, registered in
  Proofs.lean). The recognition criterion is done; the deep core (Franklin's
  involution) remains the open frontier.
- Added the **enumeration order**: the structural fact that makes Euler's
  partition recurrence a *finite* sum. The generalized pentagonal numbers
  strictly increase along the zigzag `0 < g(1) < g(-1) < g(2) < g(-2) < …`.
- Method: two **exact difference identities** in which the quadratic part of
  `g` cancels, leaving clean linear facts —
  `genPent_neg : g(-k) = g(k) + k` and
  `genPent_succ_sub_neg : g(k+1) = g(-k) + (2k+1)` (both `linear_combination`
  of two `two_mul_genPent` instances). From these, by `omega`: `genPent_pos`,
  `genPent_lt_genPent_neg`, `genPent_neg_lt_genPent_succ`, `genPent_zigzag_step`,
  and `genPent_strictMono_pos` (positive branch, via the factorization
  `2·g(b)-2·g(a) = (b-a)(3(a+b)-1)` + `mul_pos`).
- 8 new theorems, 0 new axioms/sorries. theoremCount 16→24, lineCount 179→257.
- Branch `research/pentagonal-oq01-zigzag-enumeration`; PR ships build-gated
  (watcher serialized behind the brianchon build to avoid OOM).

**Next steps**: (1) the negative branch monotonicity `genPent_neg_strictMono`
(immediate from `genPent_neg` + `genPent_strictMono_pos`); (2) a `Finset` of
pentagonal exponents `≤ N` and its cardinality `~ √(N/?)` for the recurrence's
finite index set; (3) the genuine frontier remains Franklin's sign-reversing
involution on distinct-part partitions for the deep identity.
