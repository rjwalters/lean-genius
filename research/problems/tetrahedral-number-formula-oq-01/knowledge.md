# Knowledge: tetrahedral-number-formula-oq-01

## Summary

Open question: the **general-dimension** hockey-stick identity for hyper-tetrahedral
(d-dimensional simplex) numbers, generalizing the parent `tetrahedral-number-formula`
(which only proves the fixed d=3 rung: sum of triangular numbers = tetrahedral number).

## Session 2026-07-09 (Session 1) - General figurate theory

**Mode**: FRESH
**Outcome**: progress (UNVERIFIED — build infrastructure down)

### What I Did
- Built a dimension-indexed theory in `proofs/Proofs/TetrahedralNumberFormulaOQ01.lean`
  around `simplexNumber d n := (n+d).choose d`.
- Proved (manually reviewed; 0 sorries, 0 axioms):
  - `sum_simplex`: general hockey stick `∑_{k≤n} P_d(k) = P_{d+1}(n)` for every d.
  - `iterSum_one`: the headline — the figurate ladder is the d-fold iterated partial
    sum of the constant sequence 1; `iterSum d (fun _=>1) n = P_d(n)`, by induction on
    the DIMENSION d with `sum_simplex` as the one-step engine.
  - `simplexNumber_succ_succ`: figurate Pascal recurrence P_{d+1}(n+1)=P_{d+1}(n)+P_d(n+1).
  - `simplexNumber_eq_multichoose`: P_d(n) = Nat.multichoose (n+1) d.
  - `factorial_mul_simplexNumber(_prod)`: d!·P_d(n) = (n+1).ascFactorial d = ∏_{i<d}(n+1+i).

### Key Findings
- Mathlib supplies the ONE-STEP hockey stick (`Nat.sum_range_add_choose`) and the
  multiset coefficient (`Nat.multichoose`), but NOT the dimension-indexed figurate
  theory. The iterated-partial-sum characterization is the novel content.
- Induction on dimension d (not on n) is the structural difference from the parent.

### Blocker (verification)
- Docker build: containerd `metadata.db` I/O error (exit 125) — host infra corruption.
- Host `lake env lean`: main-repo cache missing `Batteries.CodeAction.Basic.olean` and
  `Mathlib.Tactic.Omega.olean` (fleet-race olean deletion). Not found in any fleet cache.
- Result: shipped [UNVERIFIED] after careful manual review; every lemma name/statement
  checked against Mathlib source (Choose/Sum.lean, Choose/Basic.lean, Factorial/BigOperators.lean).

### Files Modified
- proofs/Proofs/TetrahedralNumberFormulaOQ01.lean (new)
- src/data/research/problems/tetrahedral-number-formula-oq-01.json (knowledge)

### Next Steps
- Machine-verify when infra recovers.
- Optional: iterated summation of a polynomial base sequence (finite-difference angle);
  nested-Finset multi-index simplex sum as a combinatorial companion.
