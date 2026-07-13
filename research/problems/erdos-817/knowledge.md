# Erdős #817: Subset Sum Sets and Arithmetic Progressions

**Problem**: Define g_k(n) = minimal N such that {1,...,N} contains A with |A|=n and subsetSums(A) is k-AP-free. Is g_3(n) ≫ 3^n?
**Status**: OPEN conjecture; supporting lemmas g_ge_n and g3_le_exp now proved (0 sorries)
**File**: `proofs/Proofs/Erdos817Problem.lean`

---

## Session 2026-04-14 (Session 1) — Survey and partial proofs

**Mode**: REVISIT
**Outcome**: progress (4→2 sorries)

### Key Findings
- g3_two = 3 (not 2), corrected proof
- g_ge_n needs nonemptiness of ValidNs k n — requires AP-free set construction
- g3_le_exp needs AP-freeness of base-3 subset sums — the "carry argument"
- Approach: use A = {3^0,...,3^{n-1}}, whose subset sums are base-3 {0,1}-digit numbers

---

## Session 2026-04-14 (Session 2) — Prove g_ge_n and g3_le_exp sorries

**Mode**: REVISIT
**Outcome**: completed (2 sorries → 0)

### What I Did
- Proved the 3-AP-freeness of subsetSums({3^0,...,3^{n-1}}) by induction on n
- Key bound: 2*x < 3^n for all x ∈ subsetSums(A_n) — cleanly separates B0 and B1 = B0 + 3^n
- All mixed AP cases (a ∈ B0, a+2d ∈ B1, etc.) yield arithmetic contradictions from this bound
- Used this to fill both sorries: g_ge_n (ValidNs nonemptiness) and g3_le_exp (AP-freeness)

### Key Findings
- **Induction structure**: B0 = subsetSums A_n (all x with 2*x < 3^n), B1 = B0 + 3^n (all ≥ 3^n). Any 3-AP spanning both leads to 3^n ≤ something < 3^n.
- **g_ge_n witness**: A = {3^0,...,3^{n-1}} ⊆ Icc 1 (3^n) with |A|=n, then apFree_of_three gives k-AP-free for k ≥ 3.
- **Geometric sum**: 2 * (sum of A_n) + 1 = 3^n — proved by induction, used for the bound.
- **Key helper lemmas**: subsetSums_insert_eq (splits on c∈subset or not), pow3Set_sum, subsetSums_pow3_bound, apFree_of_three, pow3_subsetSums_apFree

### Files Modified
- `proofs/Proofs/Erdos817Problem.lean`: sorries 2→0, 368→557 lines
- `src/data/proofs/erdos-817/meta.json`: sorries 2→0, lineCount 368→557

### Open Questions
- The main conjecture g_3(n) ≫ 3^n is still OPEN — requires Erdős-Sárközy theorem
- Proving the upper bound g_3(n) ≤ 3^n tightly (we have g3_le_exp but not the lower bound)
- What is g_3(4)? g_3(5)? (only g_3(1)=1, g_3(2)=3 proved so far)
