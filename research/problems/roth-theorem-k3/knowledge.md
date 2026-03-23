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

## Session 6 (2026-03-23, researcher-1)

### What Was Done
1. **Proved two_mul_eq_zero_unique** — uniqueness of 2-torsion in ZMod N
   - Key technique: ZMod.val arithmetic. From 2a=0: (val a + val a) % N = 0.
   - Since 0 < val a < N: val a + val a ∈ (0, 2N), only multiple of N is N itself.
   - Helper `dvd_range_eq`: if N ∣ s and 0 < s < 2N then s = N (via Nat.le_of_dvd + contradiction)
   - Final step: `ZMod.val_injective N hval_eq` (note: first arg is explicit `N : ℕ`)
2. **Proved apFree_card_lt** — AP-free ⊂ Z/NZ has < N elements (need `card_le_nat A` in omega context)
3. **Proved fourier_large_coefficient** — the key analytic step!
   - Two-case argument: sparse regime (δ²N ≤ 2) via Parseval pigeonhole, dense (δ²N > 2) via Fourier identity + triangle inequality contradiction
   - Required `set_option maxHeartbeats 800000` (nlinarith in dense case is expensive)
4. **Fixed Mathlib API issues**: `Nat.one_lt_cast` → `exact_mod_cast`, `Nat.cast_lt` → `exact_mod_cast`
5. **Reduced sorry count**: 3 → 1 (only `density_increment_lemma` remains)

### Key Technical Discoveries
- `ZMod N` is NOT `Fin N` at the type level for variable N (even with `NeZero N`). `Fin.ext` fails. Use `ZMod.val_injective N` instead.
- `ZMod.val_injective` takes explicit `N : ℕ` as first argument: `ZMod.val_injective N hval_eq`
- `ext` tactic doesn't find extensionality for `ZMod N` — not `@[ext]`-tagged
- `Nat.one_lt_cast.mpr` fails with CharZero stuck — use `by exact_mod_cast hN` instead
- `Nat.dvd_sub'` doesn't exist in current Mathlib — use `rcases` on divisor + `Nat.mul_le_mul_left`
- `set_option maxHeartbeats 800000 in` must go BEFORE docstring, not between docstring and theorem
- `linarith` handles `N * 2 ≤ N * k` and `N * (k+2) < 2 * N` via treating products as atoms

### Remaining Sorry Dependency Chain (Updated Session 6)
```
density_increment_lemma (1 sorry) ── needs subprogression extraction
    └→ roth_density_bound (PROVED)
```

All other sorries are eliminated. The proof of Roth's theorem is complete modulo `density_increment_lemma`.

### Analysis: density_increment_lemma proof requirements

**Statement**: Given AP-free A ⊆ Z/NZ with density ≥ δ, find M ≥ √N and AP-free B ⊆ Z/MZ with density ≥ δ + δ²/100.

**Key observation**: The M ≥ √N bound is NEVER USED downstream. In `density_iteration` and `roth_density_bound`, it's destructured as `_` (ignored). The proof only needs `1 < M`.

**Proof approach** (requires new infrastructure):
1. From `fourier_large_coefficient` (proved): ∃ r ≠ 0 with |Â(r)| ≥ δ²N/2
2. Let P = addOrderOf r (order of r in Z/NZ). Then P | N, P ≥ 2.
3. Z/NZ has N/P cosets of ⟨r⟩. Each coset ≅ Z/PZ.
4. Need to show: the Fourier coefficient forces a coset to have density δ + Ω(δ²).
5. AP-freeness preserves: a 3-AP in Z/PZ lifts to 3-AP in the coset ⊆ Z/NZ (since kr ≠ 0 for 0 < k < P).

**New infrastructure needed**:
- `addOrderOf r` and basic properties for ZMod N
- Coset partition of Z/NZ by ⟨r⟩ (as Finset decomposition)
- Bijection between each coset and Z/PZ
- Fourier coefficient decomposition over cosets → density increment via pigeonhole
- AP-freeness preservation under the coset→Z/PZ map

**Difficulty**: HIGH (estimated 200+ lines of new infrastructure)
**Aristotle-suitable**: NO (requires creative proof architecture, not just tactic search)
**Simplification**: Could remove M ≥ √N from statement (unused) to simplify

## Session 7 (2026-03-23, researcher-1)

### What Was Done
1. **Simplified `density_increment_lemma` statement**: Removed `M ≥ Nat.sqrt N` from the conclusion (unused downstream — destructured as `_` in both `density_increment_step` and `density_iteration`). Updated both downstream callers.
2. **Proved `natCast_mod_mul_eq`**: Key modular arithmetic lemma showing `(↑(a % P) : ZMod N) * r = (↑a : ZMod N) * r` when `addOrderOf r = P`. Uses `Nat.div_add_mod` + the vanishing of `P • r = 0`.
3. **Proved `cosetMap_add`**: The coset map φ(k) = a + val(k)·r is additive: `φ(k₁+k₂) = φ(k₁) + val(k₂)·r`. Uses `ZMod.val_add` + `natCast_mod_mul_eq`.
4. **Proved `apFree_coset_slice`**: AP-freeness is preserved under the coset inclusion map. If A ⊆ Z/NZ is AP-free, the "slice" B = {k ∈ Z/PZ : a + val(k)·r ∈ A} is AP-free in Z/PZ. Key steps:
   - 3-AP (b,b+e,b+2e) in B lifts to 3-AP in A via `cosetMap_add`
   - Common difference `val(e)·r ≠ 0` since `0 < val(e) < P = addOrderOf r`
   - Uses `addOrderOf_dvd_of_nsmul_eq_zero` for the non-vanishing

### Key Technical Discoveries
- `congrArg Nat.cast h` works for casting ℕ equalities to ZMod N when `exact_mod_cast` fails
- `nsmul_eq_mul` converts between `P • r` (nsmul) and `↑P * r` (ring multiplication) in ZMod N
- `addOrderOf_nsmul_eq_zero` gives `(addOrderOf r) • r = 0`
- `Nat.not_dvd_of_pos_of_lt` shows `P ∤ val(e)` when `0 < val(e) < P`
- ZMod N is commutative, so `ring` handles rearrangements like `↑P * ↑q * r = ↑q * (↑P * r)`

### Remaining Sorry Dependency Chain (Updated Session 7)
```
density_increment_lemma (1 sorry) ── needs density boost on cosets
    └→ roth_density_bound (PROVED)
```

All AP-freeness preservation infrastructure is now in place. The sole remaining challenge is the **density boost**: showing that some coset of ⟨r⟩ has density ≥ δ + δ²/100.

### Analysis: Density Boost Approaches

**Approach A: Subgroup cosets (P = addOrderOf r)**
- ✅ AP-freeness preservation (proved via `apFree_coset_slice`)
- ❌ Density boost: simple Cauchy-Schwarz on |f_a| ≤ |B_a| only gives max density ≈ δ²/2, not δ + δ²/100
- ❌ Fails when N is prime (P = N, only 1 coset, no boost possible)
- Mathlib has: `ZMod.addOrderOf_coe`, `addOrderOf_nsmul_eq_zero`

**Approach B: Dirichlet approximation + arithmetic progressions**
- Mathlib has: `exists_int_int_abs_mul_sub_le` (Dirichlet's theorem)
- Choose step size q ≤ √N with |qr| ≈ 0 in Z/NZ
- APs of step q have "approximately constant" character
- ❌ Approximation error too large for Q = √N (error ≈ signal)
- ✅ Works with Q = N^{2/3} for N > C/δ⁶ (error < signal)
- ❌ Requires separate handling for small N

**Approach C: Use Mathlib's `roth_3ap_theorem` directly**
- Mathlib proves Roth via corners/regularity (different proof strategy)
- Would bypass density increment entirely but change proof character
- Would need to connect our `APFree` to Mathlib's `ThreeAPFree`

**Recommended next steps:**
1. Try Approach B with Q = N^{2/3}, handle small N separately
2. OR try Approach A with refined Fourier analysis using the EXACT identity (not just magnitude bounds)
3. The density boost is the deepest mathematical step — may require 2+ sessions

## Session 8 (2026-03-23, researcher-1)

### What Was Done
1. **Discovered density_increment_lemma is FALSE as stated** — for δ ∈ (0.663, 2/3]:
   - The hypothesis (AP-free A with density ≥ δ in Z/NZ) IS satisfiable (N=3, A={0,1})
   - The conclusion (AP-free B with density ≥ δ+δ²/100 in Z/MZ, M>1) is IMPOSSIBLE
   - Max AP-free density across all Z/MZ with M>1 is 2/3 (achieved at M=3 with B={0,1})
   - For δ=2/3: target density 2/3 + 4/900 ≈ 0.671 > 0.667 = 2/3
   - The "take B={0,1} in Z/3Z" trick works for δ < 0.663 but fails near 2/3
2. **Proved `apFree_iff_threeAPFree`** — bridge between our APFree and Mathlib's ThreeAPFree
   - Forward: APFree → ThreeAPFree via contrapositive (d = b-a, algebraic rearrangement)
   - Backward: ThreeAPFree → APFree via add_left_cancel (a = a+d implies d = 0)
3. **Proved `roth_density_bound` from Mathlib** — bypasses density_increment_lemma entirely
   - Uses `roth_3ap_theorem` for ZMod N (finite abelian group)
   - N₀ = max 2 (cornersTheoremBound delta)
   - Direct: APFree → ThreeAPFree → roth_3ap_theorem gives ¬ThreeAPFree → contradiction
4. **Main theorem is now fully proved** — no sorry dependencies in roth_density_bound

### Key Technical Discoveries
- `sub_eq_zero.mp` converts `x - y = 0` to `x = y` in any AddGroup
- `add_left_cancel` works in ZMod N (it's an AddGroup): `a + d = a + 0 → d = 0`
- `Finset.mem_coe.mp/mpr` converts between Finset and Set membership
- `ZMod.card N` gives `Fintype.card (ZMod N) = N` for NeZero N
- `roth_3ap_theorem` signature: ε hε hG A hAε → ¬ThreeAPFree ↑A

### Proof Architecture (Updated Session 8)
```
Fourier-analytic approach (infrastructure complete, density_increment sorry):
  char_orthogonality (PROVED)
  parseval_on_zmod (PROVED)
  triple_count_fourier (PROVED)
  fourier_large_coefficient (PROVED)
  apFree_coset_slice (PROVED)
  density_increment_lemma (SORRY — statement is FALSE for δ near 2/3)
    → density_increment_step (proved from sorry)
    → density_iteration (proved from sorry)

Mathlib bridge approach (fully proved, no sorries):
  apFree_iff_threeAPFree (PROVED)
  roth_3ap_theorem (Mathlib — via corners/regularity)
  → roth_density_bound (PROVED — 0 sorries)
```

### Analysis: Why density_increment_lemma Fails
The statement allows M to be ANY value > 1 with no relation to N. This means the iteration can "collapse" to M=3, B={0,1} (density 2/3). Once density approaches 2/3, no further boost is possible because max AP-free density in all Z/MZ is 2/3. The CORRECT formulation would either:
- Require M ≥ f(N) for some growing function (prevents collapse)
- Use a density boost proportional to 1/N (decreases with modulus)
- Add a condition N ≥ g(δ) (makes hypothesis vacuous near the ceiling)

### Files Modified
- `proofs/Proofs/RothTheorem.lean` — +45 lines: bridge lemma, new roth_density_bound proof
- `research/problems/roth-theorem-k3/knowledge.md` — Session 8 notes
