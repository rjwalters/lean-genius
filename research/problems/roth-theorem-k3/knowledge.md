# Knowledge: roth-theorem-k3

## Session 1 (2026-03-22, researcher-2)

### Mathlib Infrastructure Survey
- **ZMod.dft** (`Analysis/Fourier/ZMod.lean`): Full DFT as LinearEquiv, notation 𝓕
- **ZMod.stdAddChar**: Standard additive character j ↦ exp(2πij/N), primitive
- **ThreeAPFree** (`Combinatorics/Additive/AP/Three/Defs.lean`): Mathlib's AP-free predicate
- **roth_3ap_theorem** (`Combinatorics/Additive/Corner/Roth.lean`): May have quantitative Roth via regularity — UNVERIFIED, could not read Mathlib source (symlink issue in worktree)
- **Additive energy** (`Combinatorics/Additive/Energy.lean`): E[s,t] counting
- **Behrend bound** (`Combinatorics/Additive/AP/Three/Behrend.lean`): Lower bound construction
- Parseval/Plancherel for finite groups: NOT FOUND in Mathlib

### What Was Done
1. **Restructured proof from 4 to 6 parts** (92→233 lines)
2. **Added tripleCount definition** + proved APFree ↔ tripleCount = 0
3. **Added card_le_nat, card_le_nat_real** — cardinality bounds (proved)
4. **Fixed density_increment_lemma** — added `0 < M` and `APFree B` to conclusion
5. **Proved density_increment_step** — one-step wrapper
6. **Proved density_iteration** — k steps boost density by k·δ²/100 (key iteration!)
7. **Added Fourier infrastructure** — norm bound, Parseval, AP-Fourier identity (sorry)
8. **Created RothTheoremAristotle.lean** — companion file for proof search

### Proof Architecture Insight
The iteration argument (roth_density_bound from density_increment_lemma) works as follows:
- `density_iteration` shows k applications boost density to ≥ δ + k·δ²/100
- Key inequality: current density d ≥ δ implies d² ≥ δ², so increment ≥ δ²/100
- After K = ⌈100·(1-δ)/δ²⌉ + 1 steps, density > 1, contradicting |A| ≤ N
- Type challenge: each step produces ∃(M)(B : Finset (ZMod M)), changing the type
- N₀ can be 1 since each step preserves M > 0 (from Nat.sqrt N ≥ 1 when N ≥ 1)

### Critical Finding: Our APFree ≡ Mathlib's ThreeAPFree
Our: ∀ a d, d ≠ 0 → a ∈ A → a+d ∈ A → a+2d ∉ A
Mathlib: ∀ a d, a ∈ A → a+d ∈ A → a+2d ∈ A → d = 0
These are contrapositives. An equivalence lemma would unlock Mathlib's additive combinatorics.

### Sorry Classification (Updated Session 2)
| Sorry | Difficulty | Aristotle? | Status |
|-------|-----------|------------|--------|
| fourierCoeff_norm_le | Easy | YES | **PROVED** (Session 2) |
| parseval_on_zmod | Medium | MAYBE | Needs orthogonality of characters |
| triple_count_fourier | Hard | NO | Deep identity connecting APs to Fourier |
| fourier_large_coefficient | Hard | NO | Key analytic step, needs Parseval + counting |
| density_increment_lemma | Hard | NO | Needs fourier_large_coefficient + pigeonhole |
| roth_density_bound | Medium | NO | **PROVED** (Session 2) |

## Session 2 (2026-03-22, researcher-4)

### What Was Done
1. **Proved fourierCoeff_norm_le** (triangle inequality + |exp(iθ)|=1)
   - Key technique: rewrite exponent to `↑θ * I` form via `push_cast; ring`
   - Show `(↑θ * I).re = 0` via `Complex.mul_re` + `Complex.I_re/I_im`
   - Then `Real.exp_zero` gives norm = 1
   - Triangle inequality via `norm_sum_le` + `Finset.sum_le_sum`
2. **Proved roth_density_bound** (main theorem of the file!)
   - Iterate `density_iteration` by induction on k: after k steps, get density ≥ δ+k·δ²/100
   - Cast unification: `push_cast` normalizes `↑(k+1)` to `↑k+1`
   - Choose K > 100/δ² via `exists_nat_gt`, clear denominator with `field_simp`
   - Density > 1 implies |B| > M, contradicting `card_le_nat_real`
3. **Updated Aristotle companion file** — removed proved lemmas, kept parseval and basic lemmas
4. **Reduced sorry count**: 6 → 4

### Proof Architecture
The main theorem `roth_density_bound` is now fully proved from `density_increment_lemma` (sorry):
```
density_increment_lemma (sorry)
  → density_increment_step (proved, session 1)
  → density_iteration (proved, session 1)
  → roth_density_bound (proved, session 2)
```

### Remaining Sorry Dependency Chain
```
parseval_on_zmod (sorry) ──────────────────────────┐
triple_count_fourier (sorry) ──────────────────────┤
                                                    ├→ fourier_large_coefficient (sorry)
                                                    │    └→ density_increment_lemma (sorry)
                                                    │         └→ roth_density_bound (PROVED)
```

### Technical Notes
- `div_lt_iff` does NOT exist as a bare identifier in current Mathlib — use `field_simp` or `mul_lt_mul_of_pos_right` to clear denominators
- `mul_lt_mul_of_pos_right` works for `a < b → 0 < c → a*c < b*c`
- `NeZero M` instance from `0 < M`: `⟨by omega⟩`

## Session 3 (2026-03-22, researcher-7)

### What Was Done
1. **Proved exp_eq_pow_root**: exp(2πik/N) = (exp(2πi/N))^k via Complex.exp_nat_mul
2. **Proved root_pow_eq_one**: exp(2πi/N)^N = 1 via Complex.exp_two_pi_mul_I
3. **Proved root_unity_sum_zero**: ∑_{k=0}^{N-1} ω^k = 0 for ω^N=1, ω≠1 via mul_neg_geom_sum
4. **Proved exp_val_mul_eq**: exp(2πi·val(a*b)/N) = exp(2πi·val(a)·val(b)/N)
   - Uses ZMod.val_mul to get val(a*b) = (val(a)·val(b)) % N
   - Decomposes k = N·(k/N) + k%N and shows exp absorbs the integer part
5. **Proved psi_eq_pow**: ψ(r*x) = ω_x^{val(r)} using exp_val_mul_eq + exp_nat_mul
6. **Proved char_orthogonality**: ∑_{r:ZMod N} ψ(r·c) = N·δ(c,0) — the KEY result
   - c = 0 case: simp (each term exp(0) = 1)
   - c ≠ 0 case: reindex via Fin.sum_univ_eq_sum_range, apply root_unity_sum_zero
   - ω ≠ 1 via Complex.exp_eq_exp_iff_exists_int + integer squeeze (0 ≤ n < 1 for n : ℤ)
7. All 6 lemmas compile without sorry (Docker build verified)

### Key Technical Discoveries
- `ZMod N = Fin N` definitionally when N > 0, so `change` works for sum reindexing
- `Fin.sum_univ_eq_sum_range (fun k => ω^k)` handles ZMod→Fin→range conversion cleanly
- `Complex.exp_eq_exp_iff_exists_int`: exp(a) = exp(b) ↔ ∃n:ℤ, a = b + n·2πi (confirmed in codebase)
- `mul_right_cancel₀` + `Complex.ofReal_injective` extracts ℝ equations from ℂ

### Parseval Proof Analysis
The Parseval proof `∑_r ‖Â(r)‖² = |A|·N` requires:
1. Expand ‖z‖² = normSq(z) = z · conj(z) as double sum
2. Use `exp_val_mul_eq` to rewrite each ψ(rx) · conj(ψ(ry))
3. Swap sum order via `Finset.sum_comm`
4. Apply `char_orthogonality` (proved!) to extract diagonal
5. Sum diagonal: ∑_{x∈A} N = |A|·N

**Blockers for Parseval**: Steps 1-2 require expanding `normSq(∑ f(x))` as a double sum and showing `ψ(rx)·conj(ψ(ry)) = exp(2πi·val(r)·(val(x)-val(y))/N)`. The character property `conj(ψ(a)) = ψ(-a)` needs `val(-a) ≡ -val(a) (mod N)`, which is tricky since `val` returns ℕ not ℤ. Better approach: work directly with the exp form and use `conj(exp(iθ)) = exp(-iθ)` from Mathlib.

### Sorry Classification (Updated)
| Sorry | Difficulty | Notes |
|-------|-----------|-------|
| ~~parseval_on_zmod~~ | ~~Medium~~ | **PROVED** (Session 4) |
| triple_count_fourier | Hard | Similar structure to Parseval but triple product |
| fourier_large_coefficient | Medium | Follows from Parseval + triple_count |
| density_increment_lemma | Hard | Needs fourier_large_coefficient + pigeonhole on subprogressions |

## Session 4 (2026-03-22, researcher-7)

### What Was Done
1. **Proved conj_psi**: conj(ψ(x)) = ψ(-x) via unit-norm inversion
   - Key insight: avoid `map_exp` (not in Mathlib) by using |ψ(x)| = 1
   - ψ(x) · ψ(-x) = ψ(0) = 1 (by psi_add + psi_zero)
   - conj(ψ(x)) · ψ(x) = |ψ(x)|² = 1 (by Complex.norm_exp + re=0)
   - Both are right-inverses of ψ(x) → equal by cancellation
2. **Proved parseval_on_zmod**: ∑_r ‖Â(r)‖² = |A|·N (Parseval identity)
   - Convert ‖z‖² = re(z·conj z) via Complex.mul_conj + normSq_eq_norm_sq
   - Pull .re out of sum (re is additive, proved by induction on Finset)
   - Expand (∑ ψ)·conj(∑ ψ) = ∑∑ ψ·conj(ψ) via sum_mul + mul_sum
   - Use conj_psi: conj(ψ(ry)) = ψ(-(ry))
   - Combine via psi_add: ψ(rx)·ψ(-(ry)) = ψ(r(x-y))
   - Swap sums (two applications of Finset.sum_comm)
   - Apply char_orthogonality: ∑_r ψ(r(x-y)) = N·δ(x=y)
   - Collapse diagonal: ∑_{x∈A} N = |A|·N
3. **Reduced sorry count**: 4 → 3

### Key Technical Discoveries
- `Complex.normSq_eq_norm_sq`: converts between normSq and ‖·‖²
- `Complex.norm_exp z`: ‖exp(z)‖ = Real.exp(z.re), so unit-norm when re=0
- `Finset.sum_ite_eq`: collapses conditional sums over Finsets
- Avoid `map_exp`/`Complex.exp_conj` — not available. Use unit-norm argument instead
- `left_ne_zero_of_mul` useful for ψ(x) ≠ 0 from ψ(x)·ψ(-x) = 1
- Sum swapping inside outer sums: use `simp_rw` with explicit `Finset.sum_comm`

### Remaining Sorry Dependency Chain (Updated Session 4)
```
triple_count_fourier (sorry) ──────────────────────┐
                                                    ├→ fourier_large_coefficient (sorry)
parseval_on_zmod (PROVED) ─────────────────────────┤    └→ density_increment_lemma (sorry)
                                                              └→ roth_density_bound (PROVED)
```

## Session 5 (2026-03-23, researcher-5)

### What Was Done
1. **Proved triple_count_fourier** — the Fourier identity for AP counting!
   - Fixed broken `← psi_add` by adding extra `Finset.sum_mul` to fully distribute 3-factor products
   - Used `simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]` to push r innermost
   - Applied `char_orthogonality` + `sub_eq_zero` for orthogonality collapse
   - Reduced to pure combinatorial identity `tripleCount_add_card_eq_triple_sum`
2. **Introduced `tripleCount_add_card_eq_triple_sum`** (sorry) — combinatorial identity:
   `tripleCount A + |A| = ∑_{x∈A} ∑_{y∈A} ∑_{z∈A} [x+z=2y]`

### Key Technical Discoveries
- **Distribution completeness**: `simp_rw [Finset.sum_mul, Finset.mul_sum]` does NOT fully distribute 3-factor products. Need: `simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]`
- **psi_add matching**: After distribution, ψ products are left-associated. Fix: explicit `show` with `rw [← psi_add, ← psi_add]; congr 1; ring`
- **Sum order**: The Fourier expansion of Â(r)²·conj(Â(2r)) gives variable order (x, z, y) where x,z from sq and y from conj
- **simp_rw sum_comm**: `simp_rw [Finset.sum_comm (s := univ) (t := A)]` pushes univ sums inside A sums in 3 automatic passes

### Remaining Sorry Dependency Chain (Updated Session 5)
```
tripleCount_add_card_eq_triple_sum (sorry) ─── pure combinatorics
    └→ triple_count_fourier (PROVED)
          └→ fourier_large_coefficient (sorry)
parseval_on_zmod (PROVED) ──┘    └→ density_increment_lemma (sorry)
                                       └→ roth_density_bound (PROVED)
```

## Session 7 (2026-03-23, researcher-3)

### What Was Done
1. **Proved `fourierCoeff_zero`**: Â(0) = |A| (zeroth Fourier coefficient counts elements)
2. **Proved `apFree_card_lt`**: AP-free sets cannot be full ZMod N for N ≥ 2
   - Uses {0, 1, 0+2·1} as a 3-AP in any ZMod N with N ≥ 2
   - Requires `ZMod.val_one_lt_of_lt` to show 1 ≠ 0 in ZMod N
3. **Proved `parseval_nonzero`**: Σ_{r≠0}‖Â(r)‖² = n·N - n² (Parseval minus r=0 term)
4. **Decomposed `fourier_large_coefficient` into two cases**:
   - **Case 1 (δ²N < 2): FULLY PROVED** via Parseval pigeonhole
     - n ∈ {1,...,N-1} ⟹ n(N-n) ≥ N-1 ⟹ max ‖Â(r)‖ ≥ 1 > δ²N/2
   - **Case 2 (δ²N ≥ 2): Reduced to one sorry** (norm bound inequality)
     - Set up Fourier identity: nN = n³ + S, computed ‖S‖ = n(n²-N)
     - Proved n² > N from δ²N ≥ 2 and n ≥ δN
     - Reduced to: n²-N < δ²N²/2 (which contradicts n² ≥ δ²N²)
     - Remaining sorry: the norm bound chain (AM-GM + Parseval)
5. **Changed signature**: `hN : 0 < N` → `hN : 1 < N` (ZMod 1 has no nonzero element)

### Proof Strategy for Remaining Sorry
The norm bound in Case 2 follows from:
- ‖S‖ ≤ Σ_{r≠0} ‖Â(r)‖²·‖Â(2r)‖  (triangle inequality + norm multiplicativity)
- < (δ²N/2) · Σ ‖Â(r)‖·‖Â(2r)‖  (hypothesis: each ‖Â(r)‖ < δ²N/2)
- ≤ (δ²N/2) · Σ (‖Â(r)‖² + ‖Â(2r)‖²)/2  (AM-GM: ab ≤ (a²+b²)/2)
- ≤ (δ²N/2) · (n(N-n) + nN)/2  (Parseval + sub-sum bound)
- ≤ (δ²N/2) · nN  (simplification: n(N-n)+nN = n(2N-n) ≤ 2nN)
After dividing by n > 0: n²-N < δ²N²/2. Combined with n² ≥ δ²N²: contradiction.

### Technical Notes
- `RCLike.norm_conj` handles ‖conj(z)‖ = ‖z‖ for the starRingEnd ℂ
- `Complex.norm_natCast` for ‖(↑n : ℂ)‖ = n
- `Complex.norm_real` + `abs_of_pos` for ‖(↑x : ℂ)‖ = |x| = x when x > 0
- `Finset.sum_lt_sum` for strict bound: need at least one strict inequality in the sum

### Remaining Sorry Dependency Chain (Updated Session 7)
```
fourier_large_coefficient (1 sorry: norm bound in Case 2)
    └→ density_increment_lemma (sorry)
          └→ roth_density_bound (PROVED)
```

## Session 9 (2026-03-23, researcher-5)

### What Was Done
1. **Decomposed `density_increment_lemma`** into coset partition cases:
   - N≥2, odd, g≥√N → coset_density_increment (sorry)
   - N≥2, odd, g<√N → box partition needed (sorry)
   - N even → reduction to odd (sorry)
   - N=1 → false edge case (sorry)

2. **Proved `psi_const_on_coset`** (modulo `mul_L_r_eq_zero`):
   ψ(r·(t + k·L)) = ψ(r·t) for all k, because L·r = 0 in ZMod N.

3. **Discovered density increment ≥ δ²/4** (stronger than needed δ²/100):
   Using Â(r) = Σ a_t·ψ(rt) with Σψ(rt)=0, the real-part alignment gives
   max deviation ≥ δ²g/4 by pigeonhole, hence density ≥ δ + δ²/4.

4. **Identified N=1 bug**: density_increment_lemma is FALSE for N=1, δ=1.
   Main theorem roth_density_bound uses N₀=1 which is unsound for δ=1.

### Key Insight: Annihilator Partition
The RIGHT partition is cosets of H = ⟨N/g⟩ (annihilator of ⟨r⟩), NOT cosets of ⟨r⟩ itself. On these cosets, ψ(r·) is EXACTLY constant (no phase approximation needed). This is because ⟨r⟩ ⊆ H⊥, so the Fourier coefficient at r contributes to the energy.

### Sorry Chain (Session 9)
```
mul_L_r_eq_zero (ZMod API) ──→ psi_const_on_coset (PROVED)
coset_char_sum_zero (sorry) ──→ coset_density_increment (sorry)
                                  ──→ density_increment_lemma
g<√N box partition (sorry) ────→    └→ density_increment_step (PROVED)
N even (sorry) ────────────────→        └→ density_iteration (PROVED)
N=1, δ+δ²/100≤1 (PROVED, S11)─→            └→ roth_density_bound (PROVED)
N=1, δ+δ²/100>1 (sorry, FALSE)→
```

## Session 11 (2026-03-23, researcher-8)

### What Was Done
1. **Proved N=1 subcase for small delta**: When delta + delta²/100 ≤ 1 (i.e., delta ≤ ~0.995),
   the N=1 case of density_increment_lemma is proved using the witness (M=1, B=Finset.univ).
   - APFree on ZMod 1 is vacuously true (Subsingleton.elim d 0)
   - Cardinality: |ZMod 1| = 1 ≥ delta + delta²/100 (from hle)
2. **Documented architectural gap**: For delta > ~0.995 at N=1, the conclusion requires
   density > 1 on some (M, B), which is impossible for finite sets. This is a genuine
   theorem-statement-level gap, not a proof gap.

### Architectural Analysis
The coset-based density increment can reduce the universe to size 1 when N is prime
(since gcd(val(r), N) = 1 for all r ≠ 0). This means:
- For prime starting N, M₁ = 1 after one step
- All subsequent iterations have M = 1
- The density approaches 1 but the iteration stalls at delta + delta²/100 > 1

**Resolution requires one of:**
1. **Dirichlet approximation**: Find arithmetic progressions of length ≥ √N where
   the character χ_r is approximately constant, giving M ≥ √N at each step
2. **Bohr sets**: Generalization of APs to higher dimensions, giving larger substructures
3. **Different proof architecture**: Triangle removal lemma or regularity-based proof

### Pre-existing Build Failures
The file has ~20 Mathlib API breakages in `fourier_large_coefficient` and related code:
- `ZMod.val_one_lt_of_lt` removed (need alternative for `1 ≠ 0` in ZMod N)
- `Finset.card_sdiff` / `Finset.sdiff_eq_empty_iff_subset` API changes
- `Exists.some` / `.some_mem` → need `.choose` / `.choose_spec`
- `exact_mod_cast` / `push_cast` behavior changes
- `linarith` on ℂ goals (ℂ not linearly ordered)
- Various `rw` pattern matching failures

These were NOT introduced by this session — they are pre-existing from Mathlib updates.

### Attempted Fixes (Reverted)
Attempted to fix the Mathlib breakages but could not verify without interactive Lean:
- `Finset.eq_univ_of_card` → use `refine` + `rw [ZMod.card]`
- `ZMod.val_one_lt_of_lt` → use `ZMod.natCast_zmod_eq_zero_iff_dvd` for `1 ≠ 0`
- `Exists.some` → `Exists.choose`
- `push_cast; linarith` → explicit `Nat.cast_sub` + `linarith`
- `linarith` on ℂ → `linear_combination`
Reverted these changes as the full fix requires an interactive Lean session.

## Session 17 (2026-03-24, researcher-4)

**Mode**: REVISIT
**Outcome**: progress (build fix)

### What I Did
1. **Identified build errors**: `density_increment_dirichlet` else branch had `have hN1 : N = 1 := by omega` which fails because `hN : 4 ≤ N` is in scope. The branch was written when the hypothesis was weaker (`0 < N` or `1 < N`), and when it was strengthened to `4 ≤ N`, the else case (d < √N) became reachable for prime N but the N=1 argument became unsound.
2. **Fixed build errors**: Replaced broken else branch (failed omega + downstream type errors) with a clean sorry + accurate documentation of what's needed (Dirichlet-based subprogression partition).
3. **Verified build**: Docker build succeeds. 0 axioms, 1 sorry (dead code), 1580 lines, 3 linter warnings.
4. **Updated metadata**: meta.json assumptions and lineCount updated.

### Key Findings
- The main theorem `roth_density_bound` is fully proved via Mathlib's `roth_3ap_theorem_nat` (corners theorem chain). The 1 sorry is in `density_increment_dirichlet`, a private helper used only by `density_chain`, which is itself never called.
- The sorry is in Case 2: when `gcd(val(r), N) < Nat.sqrt N`, the coset partition gives M = d < √N, which doesn't satisfy the conclusion `Nat.sqrt N ≤ M`. This case genuinely needs Dirichlet approximation.
- `DirichletApproximation.lean` is fully proved and available, but integrating it into the density increment argument requires ~100-200 lines of Lean (approximate character constancy on subprogressions, error bounds, density boost).

### Files Modified
- `proofs/Proofs/RothTheorem.lean` (lines 1414-1422: replaced broken else branch)
- `src/data/proofs/roth-theorem-k3/meta.json` (lineCount, assumptions)

### Next Steps
- To eliminate the sorry: implement Dirichlet-based density increment in Case 2 using `DirichletApproximation.dirichlet_approximation`
- This is optional since the main theorem is fully proved via Mathlib

## Session (2026-06-16, researcher-9) — State-sync to COMPLETED

**Mode**: REVISIT
**Outcome**: completed (stale-doc sync, no Lean change)

### What I Did
- Found `state.md` frozen at Phase ORIENT / Iteration 1 (2026-03-22) listing 6 open
  sorries (Fourier infrastructure), while the proof is in fact complete.
- Verified `proofs/Proofs/RothTheorem.lean` is 0 sorries / 0 axioms and unchanged on
  origin/main (last touched by audit #22746); registry.json already has the slug as
  `phase: COMPLETED, status: graduated`; gallery meta is `status: verified, badge: mathlib`.
- Synced `state.md` → COMPLETED, recording that the hand-built Fourier density-increment
  plan was superseded by reducing `roth_density_bound` onto Mathlib's `roth_3ap_theorem_nat`
  via the corners-theorem chain (the route state.md had filed as open Next-Action #3).

### Key Findings
- `roth_density_bound` (`RothTheorem.lean:1372`) maps `A : Finset (ZMod N)` to
  `S = A.image ZMod.val`, bridges `APFree A → ThreeAPFree (S:Set ℕ)` via
  `apFree_imp_threeAPFree_val` (`:1337`), and applies `roth_3ap_theorem_nat` with
  `N₀ = cornersTheoremBound (δ/3) + 1`.
- No build performed (triple backend blackout: Aristotle 404, Docker cold-cache 8h
  mathlib-clone zombie, 0 local oleans). No build needed — gallery/registry already
  verified and the Lean file is unchanged on main.

### Files Modified
- research/problems/roth-theorem-k3/state.md
- research/problems/roth-theorem-k3/knowledge.md

### Next Steps
None for k3. Companion OQs (oq-01/02/03) hold the remaining sorries/axioms under their own slugs.
