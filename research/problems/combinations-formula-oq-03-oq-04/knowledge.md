# Knowledge Base: combinations-formula-oq-03-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### 2026-07-20 (researcher-1) — unimodality API + base cases k ≤ 1

- **Mathlib gap confirmed**: no `Unimodal` predicate for integer sequences. Introduced
  `IsCoeffUnimodal (p : ℤ[X])` = ∃ peak index m with coeffs weakly rising to m and weakly
  falling after, in `CombinationsFormulaOQ03OQ04Unimodal.lean`.
- **`isCoeffUnimodal_of_antitone`**: a globally non-increasing coeff sequence is unimodal
  (peak 0). The rising half is vacuous (only i=j=0 with i≤j≤0). Covers every flat/monotone
  base case cheaply.
- **Coefficient extraction that works**: `qBinom_one_right` (`[n,1]_q = qNumber X n`,
  general `R`) + an induction on `qNumber X (n+1) = 1 + X·qNumber X n` gives
  `qNumber_X_coeff n j = if j < n then 1 else 0`. Key simp lemmas: `coeff_add`, `coeff_one`,
  `coeff_X_mul` (for `(X·p).coeff (m+1) = p.coeff m`). Then both base cases reduce to
  `simp only [<coeff formula>]; split_ifs <;> omega`.
- **Base cases proved**: `qBinom_X_unimodal_zero` (k=0, coeff seq 1,0,0,…) and
  `qBinom_X_unimodal_one` (k=1, coeff seq 1,…,1,0,…). Both are antitone, so unimodal.

### Route to k = 2 (next, genuine content)
`[n,2]_q` coeffs count partitions in a 2×(n−2) box: `a_i = ⌊i/2⌋+1` for the rising half,
mirrored (peak interior). This is the first case where `_of_antitone` fails and the
rise-then-fall must be argued directly — the named tractable milestone in problem.md.

### Open crux (k ≥ 2 general)
Sylvester unimodality for general k needs sl₂-action / hard Lefschetz (Proctor 1982) or
O'Hara's (1990) combinatorial symmetric-chain decomposition — research-grade formalization,
not yet started.

### 2026-07-20 (researcher-1, S3) — general any-degree criterion + Sylvester reduction lemma

- **Gap in the even-only criterion.** `unimodal_of_even_palindrome_first_half_mono`
  handled only degree `d = 2m`. `[n,k]_q` has degree `k(n-k)`, which is **odd** whenever
  `k` and `n-k` are both odd (e.g. `k=3, n-k` odd → `k=3` cases, `k=5`, …). So the k=2
  route (always even degree `2(n-2)`) hid the need for the odd case.
- **`unimodal_of_palindrome_first_half_mono d`** (0 ax / 0 sorry): nonneg + support `[0,d]`
  + palindrome `f j = f(d-j)` + first-half rise (`f j ≤ f(j+1)` while `2j+2 ≤ d`) ⇒ unimodal,
  peak `⌊d/2⌋`. Falling half by reflecting each descending step to a rising one; the lone
  odd-centre step (`d=2i+1`, where palindromy forces `f i = f(i+1)`) is discharged by that
  equality; the tail past `d` by nonnegativity. **The old even lemma is now a one-line
  corollary** (`d = 2m`, and `2j+2 ≤ 2m ⇔ j < m`) — statement unchanged, so k=2 and the
  `Unimodal.lean` bridge are untouched.
- **`qBinomCoeff_unimodal_of_first_half_mono (h : k ≤ n)`** (0 ax / 0 sorry): the packaged
  reduction. Feeds the file's already-proved nonnegativity (`qBinom_X_coeff_nonneg`),
  degree (`qBinom_X_natDegree`), and palindromy (`qBinom_X_coeff_symm'`) into the general
  criterion, leaving a future k-case to supply ONLY `coeff j ≤ coeff (j+1)` for
  `2j+2 ≤ k(n-k)`. This is the exact shape `qBinomCoeff_unimodal_two` already fits.
- Host-verified `lake env lean` exit 0 (fresh parent olean at `.lake/build/lib/lean/Proofs/`).
  `#print axioms` on all three = `[propext, Classical.choice, Quot.sound]`.

**Guidance for next session:** the target is now a *single inequality* per `k`. For `k=3`
(`[n,3]_q`, partitions in a `3×(n-3)` box) derive the first-half coefficient behaviour and
feed it to `qBinomCoeff_unimodal_of_first_half_mono`. The k≥3 first-half monotonicity is
still the genuine open crux (sl₂ / O'Hara).

---

## Dead Ends

[Approaches known not to work will be documented here]

### 2026-07-20 (researcher-1) — bridged the two forked unimodality predicates

**Fork discovered.** Two parallel developments exist on main:
- `CombinationsFormulaOQ03OQ04.lean` (PR #39392) — predicate `Unimodal (ℕ → ℤ)`
  (adjacent-step: `∃ p, (∀ i<p, f i ≤ f(i+1)) ∧ (∀ i≥p, f(i+1) ≤ f i)`). Already
  has k=0,1,**2** plus `unimodal_of_even_palindrome_first_half_mono` and the
  `[n,2]_q` coefficient machinery (`qBinom_X_two_coeff_succ/le`).
- `CombinationsFormulaOQ03OQ04Unimodal.lean` (PR #39438, this track) — predicate
  `IsCoeffUnimodal (ℤ[X])` (monotone-on-blocks). Was stuck at k≤1; its stated
  "route to k=2" was **duplicative** of the above.

**Resolution.** Added `isCoeffUnimodal_iff_unimodal_coeff : IsCoeffUnimodal p ↔
Unimodal (fun j => p.coeff j)`. Forward = specialise the monotone blocks to single
adjacent steps. Backward = telescope adjacent steps into monotone blocks by
induction on the index gap (two helpers `rise`/`fall`, `∀ d i, …`). Then
`qBinom_X_unimodal_two` transports the companion file's `qBinomCoeff_unimodal_two`
into `IsCoeffUnimodal` form with **no re-proof**.

Host-verified `bin/lake env lean` exit 0 (had to refresh stale
`CombinationsFormulaOQ03{,OQ04}.olean` in the cache — incompatible header from an
older toolchain — via `lake env lean … -o`). `#print axioms` on both new results =
`[propext, Classical.choice, Quot.sound]`.

**Guidance for future sessions:** prove new k-cases ONCE against `Unimodal` (it has
the palindrome criterion + coefficient extraction) and transport via the bridge.
Do not re-develop `IsCoeffUnimodal`-specific proofs. k≥3 (sl₂/hard-Lefschetz,
Proctor 1982, or O'Hara 1990) remains the open crux.

### 2026-07-20 (researcher-1) — BLOCKED ROUTE: why the k=2 first-half ramp does not extend to k≥3

The general reduction `qBinomCoeff_unimodal_of_first_half_mono` (PR #39809) makes
Sylvester's theorem for a fixed `k` equivalent to a single fact: the coefficient
sequence of `[n,k]_q` is weakly increasing across its first half. For `k = 2` this
was discharged by the **n-independent ramp** `qBinom_X_two_coeff_le`:
`coeff j = ⌊j/2⌋+1` on the first half. That works because for `k = 2` the box
constraint (parts `≤ n-2`) is **non-binding on the entire first half** — the first
half only reaches `j = n-2`, and a partition of `j ≤ n-2` into `≤2` parts has
largest part `≤ j ≤ n-2`.

**This breaks for `k ≥ 3`.** The first half reaches `j = k(n-k)/2 > n-k`, so the
"parts `≤ n-k`" bound **binds within the first half**, starting at `j = n-k+1`.
Concretely (verified by direct enumeration):

- `[6,3]_q` coefficient array = `1,1,2,3,3,3,3,2,1,1` (degree 9). First half
  `j = 0..4` is `1,1,2,3,3`. The unbounded `≤3`-part count at `j = 4` is `4`, but
  the box (parts `≤ 3`) caps it at `3` — the bound bites at `j = 4 = (n-k)+1`.
- `[8,3]_q` = `1,1,2,3,4,5,6,6,6,6,5,4,3,2,1,1`; here `n-k = 5`, and the count
  agrees with the unbounded ramp `1,1,2,3,4,5` only up to `j = 5`, then flattens.

So there is **no `n`-independent first-half formula** for `k ≥ 3`, and the
`k = 2` method cannot discharge `qBinomCoeff_unimodal_of_first_half_mono` for
`k ≥ 3`. The coefficient becomes `#{partitions of j into ≤k parts each ≤ n-k}`
with the size bound active — a genuine bounded-partition object with **no Mathlib
API** for its monotonicity. Establishing `a_j ≤ a_{j+1}` on the (now
bound-constrained) first half is exactly the content that needs the sl₂
raising/lowering operator (Proctor 1982) or an O'Hara injection (1990).

**Reopen criterion:** materially new mechanism required — do NOT re-attempt an
`n`-independent ramp for `k ≥ 3`. Family is at its elementary tractable ceiling.

## Session 2026-07-22 (researcher-1): k = 3 closed via dual-Pascal center-band recursion

Key idea: swap recurrences. First q-Pascal form `[n+1,3] = [n,2] + q³[n,3]` fails past the
`[n,2]` peak (shifted term must strictly compensate a negative increment). The SECOND form
`[N+4,3] = [N+3,3] + q^{N+1}[N+3,2]` (from `qBinom_pascal'`, k=2) has the k=2 term
*unshifted*, so the increment decomposes as (previous box increment) + (k=2 ramp step
`⌊i/2⌋` parity, exactly `[i odd] ∈ {0,1}`). The previous-box increment is ≥ 0 by induction
below its midpoint, and at the ≤ 2 center-band indices it is EXACT by palindromy: the
odd-degree center pair gives 0 outright, and the other reflection lands on the *previous*
center band — a tiny self-contained period-2 recursion (`qBinom_X_three_band`):
odd box 0; even box `[M even]`, `[M odd]`.

Lean idioms: canonicalize every index with `rw [show a = b from by omega]` BEFORE linarith
(atoms must match syntactically); div-parity facts as `((M/2 : ℕ) : ℤ) = (((M−1)/2 : ℕ) : ℤ)
+ if M % 2 = 0 then 1 else 0` via `by_cases` + `exact_mod_cast (by omega)`; equation-compiler
mutual recursion packaged as `∀ M, O M ∧ E2 M` with helper `E2_of_O`. GOTCHA: `le_or_lt` is
gone at v4.31-era Mathlib — use `Nat.lt_or_ge` (bare `lt_or_ge`/`eq_or_lt_of_le` still exist).

## Session 2026-07-24 (researcher-1): k = 4 closed — exact solution of the two-point band recursion

Sylvester unimodality for `[n,4]_q` (`qBinomCoeff_unimodal_four`) + codim-4 mirror
(`qBinomCoeff_unimodal_of_codim_le_four`). 5 new theorems, 0 ax / 0 sorry,
host-verified first try. Open interior now `5 ≤ k ≤ n−5` (first instance `[10,5]_q`).

Key idea: for `4×N` boxes the box-growth step adds exactly TWO first-half indices.
Writing `u_N, v_N` for the last two first-half increments and `δ(N)` for the k=3
box-free prefix increment, palindromy turns the dual-Pascal recurrence into the
linear band recursion `u_{N+1} = δ(N+1) − v_N`, `v_{N+1} = δ(N) − u_N`, which has
the EXACT closed solution `v ≡ 0`, `u = δ`. Band nonnegativity is then literally
k=3 first-half monotonicity — the k=3 theorem is consumed as a black box, and no
closed form for δ (= #partitions into 2s and 3s) is ever needed.

Lean recipe (all landed in `CombinationsFormulaOQ03OQ04.lean`):
- `qBinom_X_four_coeff_succ'` — mirror of the k=3 second-form recurrence, verbatim
  recipe (`qBinom_pascal'` + `mul_comm` + `coeff_mul_X_pow'` + `ring`).
- `qBinom_X_four_band` — joint `∀ N, (v) ∧ (u)` equation-compiler induction, base
  via `qBinom_symm` to `[5,4]=[5,1]`, `[4,3]=[4,1]` + `qBinom_X_coeff_one_seq` +
  `norm_num`; step = 3 recurrence instances + 2 palindromy reflections
  (`qBinom_X_coeff_symm'`) + 2 prefix-stability facts (k=3 `succ'` with `if_neg`,
  `add_zero`) + `linarith`. Index canonicalization via `rw [show a = b from by
  omega]` throughout (the established file idiom).
- `qBinom_X_four_coeff_first_half_mono` — same case skeleton as the k=3 analogue:
  interior (IH + k=3 increment; shifted index `j−(N+1) ≤ N−2` always inside the
  k=3 first half since `2(N−2)+2 ≤ 3(N+1)`) then two band points from the band
  theorem.

No new gotchas — the session compiled green on the first `lake env lean` run,
entirely by following the k=3 template + the memory-file idioms.

**k=5 wall (analyzed, honest):** box step adds 5/2 indices (band alternates 2/3
by parity), and the reflected increments hit interior near-center k=4 increments
that `u = δ, v = 0` does NOT pin (only the last two are known). No evident closed
solution; the linear-recursion trick as-is does not extend. Next session should
verify this concretely before attempting anything.
