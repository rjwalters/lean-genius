# Knowledge Base: LGV Lemma → Jacobi-Trudi Identity

**Problem**: ballot-problem-oq-03-oq-01-oq-01-oq-01
**Last Updated**: 2026-04-26
**Knowledge Items**: 29

Insights accumulated during research on this problem.

---

## Problem Understanding

Jacobi-Trudi identity expresses Schur polynomials as determinants of complete homogeneous
symmetric polynomials: `s_λ = det[h_{λᵢ-i+j}]`. The proof route via SSYT and RSK is:
  1. Define SSYT of shape λ with entries in {1..n}
  2. Show Schur = sum of monomial weights over SSYT
  3. Biject SSYT ↔ non-intersecting lattice paths (RSK)
  4. Apply LGV: det[e(Aᵢ,Bⱼ)] = weighted NI-path count
  5. Identify the LGV matrix with the Jacobi-Trudi matrix

---

## Session 2026-04-26 (Session 7) — ColStrictSym + sum_all_sym_pairs (proved)

**Mode**: REVISIT (RICH knowledge tier, score 55)
**Outcome**: progress — proved `sum_all_sym_pairs`, added `ColStrictSym` + `ssytSchurFin_two_row` stub

### What I Did

1. Added `ColStrictSym {n} a b P Q`: column-strict condition on `Sym (Fin n) a × Sym (Fin n) b`,
   comparing sorted representatives via `Multiset.sort`. Includes `Decidable` instance.
2. Proved `sum_all_sym_pairs (a b : ℕ)`: `∑_{all Sym pairs (P,Q)} wt(P)*wt(Q) = h_a * h_b`.
   Proof: `simp only [hsymm]` unfolds both sides, `Fintype.sum_prod_type'` splits sum over product
   type, then `simp_rw [← Finset.mul_sum]` + `rw [← Finset.sum_mul]` factors.
3. Added `ssytSchurFin_two_row` stub with structured proof plan (~140 lines remaining).
4. PR: rjwalters/lean-genius#12490. File: 345 → 401 lines.

### Key Findings

- **`sum_all_sym_pairs` proved (4 lines)**: The factorization is just `Fintype.sum_prod_type'` +
  `Finset.mul_sum`/`sum_mul`. Key step for JDT complement: col-strict + non-col-strict = h_a*h_b,
  so ssytSchurFin = h_a*h_b - h_{a+1}*h_{b-1} = schurPolynomial_two_row.
- **Remaining ~140 lines**: row-decomp equiv (~60), JDT bijection (~80), ring close (~20).
- **ColStrictSym decidable** via `Fintype.decidableForallFintype`.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (345 → 401 lines, new defs at lines 294-350)

### Next Steps

1. **Row decomp equiv** (~60 lines): `SSYTFin n 2 sh ≃ {(P,Q) : ColStrictSym (sh 0) (sh 1)}`
2. **JDT bijection** (~80 lines): `{¬ColStrict (sh 0, sh 1)} ≃ Sym σ (sh 0+1) × Sym σ (sh 1-1)`, wt-preserving
3. **Complement + ring close** (~20 lines): combine with `det_fin_two`

---

## Session 2026-04-25 (Session 6) — k=2 Case Split + ssytSchurFin_two_row Framework

**Mode**: REVISIT (RICH knowledge tier, score 53)
**Outcome**: progress — added `ssytSchurFin_two_row` sorry + isolated k=2 in `jacobi_trudi_ssyt_eq`

### What I Did

1. Added `ssytSchurFin_two_row (n : ℕ) (sh : Fin 2 → ℕ)` as a sorry with full jdt proof
   strategy documented in comments (the key intermediate goal for k=2).
2. Restructured `jacobi_trudi_ssyt_eq` to have 4 cases: k=0 (proved), k=1 (proved),
   k=2 (delegates to `ssytSchurFin_two_row`), k≥3 (sorry).
3. The main sorry is now precisely scoped: from "k≥2" to "k≥3", with the k=2 path fully
   documented via jdt bijection.

### Key Findings

- **jdt proof for k=2**: The identity `∑_{non-col-strict (P,Q)} weight = h_{a+1} * h_{b-1}`
  follows because the jdt bijection maps non-col-strict pairs (a,b) → ALL pairs (a+1,b-1),
  which generates the full product h_{a+1} * h_{b-1}. Weight is preserved since we just
  slide Q[c] into P (no weight change: we remove Q[c] from Q and add it to P).
- **Case structure**: `| succ (succ (succ k)) =>` correctly captures k≥3 (3+ rows).
- **ssytSchurFin_two_row is the priority**: ~200 lines (row-decomp Equiv + jdt Equiv + weight).
  The algebraic LGV approach (~300 lines total) remains the path for k≥3.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (345 → ~405 lines, PART VI-VII)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01-oq-01/meta.json` (sorries 1→2, lineCount, theoremCount)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json` (knowledge updated)

### Sorry Count: 1 → 2 (structural, not regression)

- `ssytSchurFin_two_row`: jdt bijection sorry (new, precisely scoped)
- `jacobi_trudi_ssyt_eq k≥3`: algebraic LGV + RSK (scope reduced from k≥2)

### Next Steps

1. **Prove ssytSchurFin_two_row** (~200 lines):
   - Define `twoRowEquiv : SSYTFin n 2 sh ≃ {col-strict row-pair}` via row projection
   - Define jdt bijection: `jdtEquiv : {non-col-strict (P,Q) of shape (a,b)} ≃ rowPairs n (a+1) (b-1)`
   - Prove weight preservation: `weight(P,Q) = weight(P',Q')` (Q[c] moves P→Q, unchanged total)
   - Combine: `ssytSchurFin n 2 sh = h_a*h_b - h_{a+1}*h_{b-1} = schurPolynomial_two_row`
2. **Algebraic LGV for k≥3** (~150 lines): ring-valued version of `lgv_lemma_rxr`

---

## Session 2026-04-25 (Session 5) — Algebraic LGV Identified as Cleaner Path

**Mode**: REVISIT
**Outcome**: analysis (no code changes)

### What I Did

- Conducted deep analysis of proof options for k≥2: RSK (~300-400 lines), algebraic LGV
  (~200 lines), jeu de taquin k=2 bijection (~100-150 lines), algebraic recurrence, and
  specialization arguments
- Confirmed: Mathlib has NO Jacobi-Trudi, NO RSK, NO polynomial-weighted LGV
- Confirmed: The existing `lgv_lemma_rxr` (BallotProblemOQ03OQ02.lean) is integer-valued
  and CANNOT be directly lifted to polynomial weights
- Identified the ALGEBRAIC LGV as the most modular approach (see Key Findings)

### Key Findings

- **Algebraic LGV is the recommended path**: Rather than building full RSK, build the
  polynomial-weighted generalization of `lgv_lemma_rxr`. This requires:
  1. `algebraic_lgv` (~150 lines): for a DAG with edge weights in CommRing R,
     `∑ NI_tuples, ∏ path_weights = det(weight_matrix)` where
     `weight_matrix[i][j] = ∑_{paths from sᵢ to tⱼ} path_weight`
  2. `weighted_path_count_eq_hsymm` (~30 lines): weighted lattice path count from
     height a to height b = `hsymm (Fin n) R (b-a)`. This follows from identifying
     weighted paths (sequences of b-a vertical steps labeled by Fin n) with Sym (Fin n) (b-a),
     which is exactly the one-row SSYT result already proved.
  3. RSK-for-polynomials (~150 lines): `SSYTFin n k sh ≃ NI-path-tuples` for the
     standard Jacobi-Trudi configuration, with weight preservation.
  Total: ~330 lines (vs ~400 for full RSK alone)

- **Integer LGV cannot be lifted**: `lgv_lemma_rxr` is specific to ℕ/ℤ (counts paths).
  Algebraic LGV is a separate theorem about ring-valued weights; it needs a fresh proof.

- **The k=2 jeu de taquin bijection works mathematically**:
  Given non-SSYT (P: weakly-inc of len a, Q: weakly-inc of len b) with first violation at c:
  - c = min{j : P[j] ≥ Q[j]}
  - P' = P[0..c-1] ++ [Q[c]] ++ P[c..a-1] (insert Q[c] into P at position c)
  - Q' = Q[0..c-1] ++ Q[c+1..b-1] (remove Q[c] from Q)
  Claim: weight-preserving bijection {non-SSYT pairs (a,b)} ≃ {all pairs (a+1, b-1)}
  Proof: P'[c-1] < Q[c] since c is the first violation (P[c-1] < Q[c-1] ≤ Q[c]); P'[c] = Q[c] ≤ P[c] = P'[c+1] ✓
  But: the INVERSE is non-trivial to define in Lean (need to identify the "inserted" position in P').
  Estimated ~80-100 lines for k=2, but doesn't generalize easily to k≥3.

- **Algebraic LGV module is more valuable than k=2 special case**: once proved,
  algebraic_lgv can be reused for other determinantal formulas (e.g., Sylvester, Dodgson condensation)

### Files Modified

- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/knowledge.md` (this file)

### Next Steps

1. **PRIORITY: Build `algebraic_lgv`** in a new file `BallotProblemOQ03AlgebraicLGV.lean`:
   - Statement: `det(weight_matrix) = ∑ NI_tuples, ∏ path_weights` over CommRing R
   - Proof: Leibniz expansion + distributivity + sign-reversing involution (same structure as lgv_lemma_rxr but generalized)
   - Module: can be separate from BallotProblemOQ03OQ01OQ01OQ01.lean
   
2. **Then: `weighted_path_count_eq_hsymm`**: Show paths from height a to b correspond to
   Sym (Fin n) (b-a) (use ssytSchurFin_one_row as a model)

3. **Then: RSK bijection**: Connect SSYTFin n k sh to NI-path-tuples with weight preservation

4. **Alternative quick win**: Prove k=2 case using jeu de taquin bijection (~100 lines)
   as a standalone theorem, then extend to k≥3 later

---

## Session 2026-04-24 (Session 4) — k≥2 Flagged Blocked; Switched to Bezout Non-PID

**Mode**: REVISIT
**Outcome**: blocked (k≥2 sorry) → switched problems

### What I Did

- Reviewed the k≥2 sorry in `jacobi_trudi_ssyt_eq`: it requires RSK correspondence (~300-400 Lean lines not in Mathlib)
- After 3+ sessions stuck on the same sorry without progress on k≥2, applied the "3+ sessions stuck → flag BLOCKED" protocol
- Switched to `bezout-identity-oq-02-oq-01-oq-01-oq-01-oq-01` (ℤ[X,Y] is NOT a PID)
- Verified and fixed a critical bug in the bezout proof's `dvd_gen2_totalDeg_zero` lemma

### Key Findings

- **k≥2 is genuinely blocked**: The RSK bijection (SSYT ↔ NI-lattice-paths) requires ~300-400 lines of infrastructure not present in Mathlib. No shortcut or alternative approach was found.
- **Protocol applied**: 3+ sessions stuck on k≥2 → flag BLOCKED, move on

### Files Modified

- None (switched to different problem)

### Next Steps

1. **k≥2 RSK sorry**: Remains open. A future session would need to build the full RSK bijection (~300-400 lines).
2. **Alternative**: Wait for Mathlib to add RSK, then come back.

---

## Session 2026-04-24 (Session 3) — Main Theorem Case Split: k=0,1 Proved

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Replaced the single `sorry` in `jacobi_trudi_ssyt_eq` with a case split on `k`:
  - k=0: `funext (fun i => i.elim0)` + `rw [hsh, schurPolynomial_empty, ssytSchurFin_empty]`
  - k=1: `funext (fun i => by fin_cases i <;> rfl)` + `rw [hsh, schurPolynomial_one_row, ssytSchurFin_one_row]`
  - k≥2: `sorry` with detailed RSK roadmap comment
- Updated file header and docstring to reflect k=0,1 are proved in the main theorem
- Updated meta.json (lineCount 313 → 345), knowledge.json (2 new builtItems, 3 new insights)
- `jacobi_trudi_ssyt_eq` now has explicit proofs for the base cases and a structured sorry

### Key Findings

- **k=0 proof pattern**: `have hsh : sh = Fin.elim0 := funext (fun i => i.elim0)` eliminates `sh`
  because any function `Fin 0 → ℕ` is eliminated by `i.elim0` (function from empty type is unique)
- **k=1 proof pattern**: `fin_cases i` for `i : Fin 1` produces exactly one case (i = 0), so `rfl` closes
  the extensionality goal `sh ⟨i, hi⟩ = sh ⟨0, _⟩`
- **`cases k with | zero => | succ k => cases k with | zero => | succ k =>`** cleanly handles
  the 0, 1, k+2 cases without awkward `rcases` patterns
- **RSK requirement confirmed**: No shortcut exists for k≥2; the combinatorial bijection
  SSYT ↔ NI-lattice-paths is the only known proof route, estimated 300-400 Lean lines

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (313 → 345 lines)
  - k=0 case proved in jacobi_trudi_ssyt_eq
  - k=1 case proved in jacobi_trudi_ssyt_eq
  - k≥2 sorry with RSK roadmap comment
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01-oq-01/meta.json` (lineCount, assumptions)
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json` (insights, builtItems)

### Next Steps

1. **Prove k≥2 case** via RSK bijection (~300-400 lines):
   - Define `SSYTFin n k sh ↪ NI-path-tuples` (forward map via RSK insertion)
   - Show bijection is weight-preserving
   - Apply LGV lemma (available in BallotProblemOQ03OQ02) in weighted form
2. **Alternative**: Submit to Aristotle after providing more scaffolding (unlikely to succeed
   without RSK structure, but worth trying after adding more intermediate lemmas)
3. **Intermediate goal**: Prove `ssytSchurFin_two_row` (k=2 case) as a standalone lemma
   using the Bender-Knuth / jeu de taquin involution argument

---

## Session 2026-04-24 (Session 2) — One-Row Case Proved

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Proved `ssytSchurFin_one_row` (k=1 case): `ssytSchurFin n 1 (fun _ => m) = hsymm (Fin n) R m`
- Constructed explicit `Equiv` between `SSYTFin n 1 (fun _ => m)` and `Sym (Fin n) m`
- Added two imports: `Mathlib.Data.Multiset.Sort` and `Mathlib.Algebra.BigOperators.Fin`
- Updated file header: ssytSchurFin_one_row now "proved" (was "open")
- Updated docstring in `jacobi_trudi_ssyt_eq` to reflect k=1 is now done

### Key Findings

- **Bijection structure**: `toFun T = ⟨↑(List.ofFn (fun j => T.1 ⟨0,j⟩)), card_proof⟩`
  - `invFun s` fills row 0 with `(s.1.sort (· ≤ ·))[j.val]` (sorted representative)
  - `left_inv`: SSYT row-0 monotone → `sort(ofFn(T.row0)) = ofFn(T.row0)` via `mergeSort_eq_self`
  - `right_inv`: `↑(s.1.sort (· ≤ ·)) = s.1` by `Multiset.sort_eq`
- **Col-strict impossibility for k=1**: proved by `omega` after `i1.isLt`, `i2.isLt`, `Fin.lt_iff_val_lt_val`
- **Weight preservation**: `Fintype.prod_sigma + Fin.prod_univ_one` reduces sigma product to `∏ j, X(T.1 ⟨0,j⟩)`; then `simp [map_coe, prod_coe, map_ofFn, prod_ofFn]` matches hsymm form
- **`Multiset.length_sort`** (not `card`): signature is `(s.sort r).length = Multiset.card s`
- **`List.SortedLE.getElem_le_getElem_of_le`**: for sorted lists, `i ≤ j → l[i] ≤ l[j]`

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (272→314 lines)
  - Added 2 imports; replaced sorry in ssytSchurFin_one_row with ~50-line bijection proof
  - Still has 1 sorry: `jacobi_trudi_ssyt_eq` (general RSK case)

### Next Steps

1. **Prove `jacobi_trudi_ssyt_eq`** (k ≥ 2 case):
   - Option A: Build RSK correspondence (~300 lines) — likely >500 total
   - Option B: Algebraic proof via transfer matrices / generating functions (avoid RSK)
   - Option C: Submit to Aristotle as a HARD sorry (unlikely to succeed without more structure)
   - Current status: 1 sorry remains; badge is `formalized`

2. **Verify Docker build** — upstream `BallotProblemOQ03OQ02.lean` build issues noted in Session 1

---

## Session 2026-04-24 (Session 1) — SSYT Infrastructure

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Replaced the trivial `rfl` tautology (`jacobiTrudi_lgv_connection`) with genuine SSYT infrastructure
- Defined `SSYTFin n k sh` (bounded semistandard Young tableaux, entries in Fin n)
- Provided `Fintype` instance via `Subtype.fintype _`
- Defined `SSYTFin.weight` (monomial product over all cells)
- Defined `ssytSchurFin` (sum of weights = Schur generating function)
- Proved `ssytSchurFin_empty` (k=0 base case: empty product + unique SSYT → 1)
- Stated `ssytSchurFin_one_row` (k=1 case, sorry pending Sym bijection)
- Stated `jacobi_trudi_ssyt_eq` (main theorem, sorry pending RSK construction)
- Updated meta.json: badge wip→formalized, sorries 0→2, theoremCount 7→10, defCount 2→5

### Key Findings

- **Mathlib HAS `SemistandardYoungTableau`** at `Mathlib.Combinatorics.Young.SemistandardTableau`
  — but it targets arbitrary ordered types with Young diagram shapes, not `Fin k → ℕ` shaped
- **`List.sortedLE_ofFn_iff`** (in `Mathlib.Data.List.Sort`): `(ofFn f).SortedLE ↔ Monotone f`
  — this is the key bridge for converting SSYT row-weakly-increasing condition to the Sym-based proof
- **`Finset.sum_unique`** synthesizes automatically via `@[to_additive]` from `Finset.prod_unique`
  — used in the k=0 base case proof
- **Pre-existing build failure**: `BallotProblemOQ03OQ02.lean` (upstream dependency) has two
  `List.drop_length` type errors (lines ~2370, 2386). Docker build is currently blocked.
  This is NOT caused by our changes.

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (178→272 lines)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01-oq-01/meta.json`

### Next Steps

1. **Prove `ssytSchurFin_one_row`** (k=1 case):
   - SSYTFin n 1 (fun _ => m) bijects to weakly-increasing functions `Fin m → Fin n`
   - These biject to `Sym (Fin n) m` via `List.sortedLE_ofFn_iff`
   - `hsymm (Fin n) R m = ∑ s : Sym (Fin n) m, monomial s` matches the weight sum
   
2. **Prove `jacobi_trudi_ssyt_eq`** (general case via RSK):
   - RSK in Lean requires ~300 lines
   - Alternative: algebraic proof via transfer matrices (avoid RSK entirely)
   - Check if Mathlib's `SemistandardYoungTableau` can replace our `SSYTFin` to save code

3. **Fix upstream build failure** in `BallotProblemOQ03OQ02.lean` (separate issue for Mechanic)

---

## Insights

1. SSYT can be formalized in ~50 lines using `Subtype` of function types over sigma types
2. `Fintype` instance is automatic via `Subtype.fintype _` when domain/codomain are finite
3. `Fin.elim0` serves as a universal eliminator for empty-partition base cases
4. The k=0 base case proof uses `IsEmpty` + `Unique` instances + `Finset.prod_empty` + `Finset.sum_unique`
5. Mathlib's `SemistandardYoungTableau` uses a different shape representation (YoungDiagram)
6. `List.sortedLE_ofFn_iff` is the key lemma for connecting monotone functions to sorted lists
7. The k=1 one-row case reduces to `Sym (Fin n) m` via the sorted-representative bijection
8. `Multiset.length_sort` (not `Multiset.card_sort`) gives `(s.sort r).length = s.card`
9. `List.SortedLE.getElem_le_getElem_of_le` handles monotonicity of sorted list access
10. `Fintype.sum_equiv` with an explicit `Equiv` is the cleanest way to reindex a finite sum
11. Weight preservation for `∏ (Fin 1 × Fin m)` uses `Fintype.prod_sigma` + `Fin.prod_univ_one`
12. `simp [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, prod_ofFn]` closes the weight match

---

## Dead Ends

- Trivial `rfl` tautology for `jacobiTrudi_lgv_connection` — replaced with mathematical content

---

## Mathlib Gaps

- No direct Jacobi-Trudi identity theorem in Mathlib
- No RSK correspondence in Mathlib
- `SemistandardYoungTableau` exists but uses `YoungDiagram` shapes, not `Fin k → ℕ`
