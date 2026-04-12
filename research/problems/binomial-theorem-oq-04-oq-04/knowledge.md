# Knowledge Base: binomial-theorem-oq-04-oq-04

Connect the Lindström–Gessel–Viennot (LGV) lemma to Vandermonde-type identities.

**Status: COMPLETED** — 0 axioms, 0 sorries. File: `proofs/Proofs/BinomialTheoremOQ04OQ04.lean`

---

## Session 2026-04-05 (Session 1) — LGV–Vandermonde Connection Proved

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Defined `lgvE m a b := C(m+(b-a), m)` — the LGV path matrix entry (East/North lattice paths)
2. Defined `lgvDet2` — the 2×2 LGV path matrix determinant
3. Proved Vandermonde via `Nat.add_choose_eq` + `sum_antidiagonal_eq_sum_range_succ`
4. Proved `vandermonde_via_powersetCard` — combinatorial LGV partition proof
5. Proved `lgvDet2_staircase` — 2×2 staircase determinant formula
6. Proved `vandermonde_chu_from_lgv` — sequential LGV gives Chu-Vandermonde terms
7. Built without importing BallotProblemOQ03 (which has pre-existing build errors)

### Key Technical Insights

- **BallotProblemOQ03.lean has pre-existing build errors** at lines 1424+; define `lgvE`/`lgvDet2` from scratch instead of importing
- **`vandermonde_via_powersetCard`** fix: use `rw [card_Ico, Nat.add_sub_cancel_left]` not `omega` to reduce `C(m+n-m, r-k) = C(n, r-k)`; omega cannot prove equality inside a `Nat.choose` call
- **`lgvDet2_staircase`** fix: add `show m+(r+1)=m+r+1 from by ring` to the simp call to resolve `add_assoc` mismatch inside ℤ cast
- **Two Vandermonde families**: standard Vandermonde uses Bool-vector model (C(m,k) terms); Chu-Vandermonde uses LGV e-function (C(m+k,m) terms); both are proved
- **1×1 degenerate LGV**: Vandermonde is the case where LGV has a single path (no pairs to invoke the Lindström involution on)

### Files Created

- `proofs/Proofs/BinomialTheoremOQ04OQ04.lean` — 228 lines, 0 sorries, 0 axioms
- `src/data/research/problems/binomial-theorem-oq-04-oq-04.json`
