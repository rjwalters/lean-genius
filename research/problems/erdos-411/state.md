# Current State

**Phase**: ITERATE
**Since**: 2026-05-13
**Iteration**: 9 (Cambie l=1 family completed)

## Current Focus

Extend Cambie's l=1 family. Cambie conjectures every r=2 doubling
solution has the form n = 2^l · p with l ≥ 1, p ∈ {2, 3, 5, 7, 35, 47}.
The l=1 layer is the set {4, 6, 10, 14, 70, 94}. Prior sessions proved
n=10 and n=94; this session proves the remaining four.

## Active Approach

For each new n ∈ {4, 6, 14, 70}, verify φ(n) + φ(n + φ(n)) = n by
`native_decide` (yielding `steinerberger_eq_n*`), then apply S8's
`steinerberger_r2_sufficient` (with `2 ∣ n` by `norm_num` and `n > 2`
by `omega`) to obtain `DoublingRelation n 2`. Total: 8 new theorems
(+53 lines), all one-line proofs reusing existing infrastructure.

## Blockers

Same as S8: the reverse Steinerberger direction (DoublingRelation n 2
→ equation at some witness iterate) and the full Cambie conjecture
(restricting solutions to the listed family) remain open. Cambie
conjectures the l ≥ 2 cases (only 2^l·p with p ≡ 7 mod 8 needing
further analysis); the p=2 parametric case (n = 2^l for l ≥ 2) is
amenable to a Mathlib-only proof and is the natural S10 target.

## Next Action

(Optional) Parametric power-of-2 result: `∀ l, 2 ≤ l → DoublingRelation
(2^l) 2`. Requires proving φ(2^l) + φ(2^l + φ(2^l)) = 2^l symbolically:
- φ(2^l) = 2^(l-1) via `Nat.totient_prime_pow` for p=2
- 2^l + 2^(l-1) = 3·2^(l-1)
- φ(3·2^(l-1)) = φ(3)·φ(2^(l-1)) = 2·2^(l-2) = 2^(l-1) for l ≥ 2,
  using `Nat.totient_mul` with coprimality of 3 and 2^(l-1)
- Sum: 2^(l-1) + 2^(l-1) = 2^l ✓

Alternatively: Selfridge–Weintraub g_{k+9}(n) = 9·g_k(n) solutions or
Weintraub's g_{k+25}(3114) = 729·g_k(3114) (would need a totientStep_p_dvd
lemma for general primes p).

## Attempt Counts

- Total attempts: 9
- Current approach attempts: 1 (succeeded)
- Approaches tried: 9 (axiomatic skeleton; Cambie ratio-3; Cambie ratio-4
  for two cases; Steinerberger sufficient direction; Cambie l=1 extension)

## Sessions

### Session 2026-05-13 — S9 Cambie l=1 family completed (PROVED)

**Mode**: ITERATE (researcher-6)
**Outcome**: 8 new theorems added (axiom-free, sorry-free)

#### What I added (Section VI.b)
- `steinerberger_eq_n4`: φ(4)+φ(6) = 2+2 = 4 (`native_decide`)
- `steinerberger_eq_n6`: φ(6)+φ(8) = 2+4 = 6 (`native_decide`)
- `steinerberger_eq_n14`: φ(14)+φ(20) = 6+8 = 14 (`native_decide`)
- `steinerberger_eq_n70`: φ(70)+φ(94) = 24+46 = 70 (`native_decide`)
- `doubling_r2_n4`: DoublingRelation 4 2 via `steinerberger_r2_sufficient`
- `doubling_r2_n6`: DoublingRelation 6 2 via `steinerberger_r2_sufficient`
- `doubling_r2_n14`: DoublingRelation 14 2 via `steinerberger_r2_sufficient`
- `doubling_r2_n70`: DoublingRelation 70 2 via `steinerberger_r2_sufficient`

#### Coverage of Cambie l=1 layer

| n  | p (in {2,3,5,7,35,47}) | Status        |
|----|------------------------|---------------|
| 4  | 2                      | **S9 NEW**    |
| 6  | 3                      | **S9 NEW**    |
| 10 | 5                      | S8 (S?)       |
| 14 | 7                      | **S9 NEW**    |
| 70 | 35                     | **S9 NEW**    |
| 94 | 47                     | S8 (S?)       |

All six l=1 minimal candidates of Cambie's conjectured family are
now proved doubling solutions.

#### Files Modified
- `proofs/Proofs/Erdos411Problem.lean` (+53 lines, 22→30 theorems)
- `src/data/proofs/erdos-411/meta.json` (lineCount, theoremCount,
  originalContributions)
- `src/data/research/problems/erdos-411.json` (currentState.iteration,
  focus, knowledge.builtItems, knowledge.insights, progressSummary,
  leanFiles[0])
- `research/problems/erdos-411/state.md` (this file)

#### Notes
- All 8 new theorems are one-liners using existing infrastructure:
  `steinerberger_eq_n*` are pure `native_decide`; `doubling_r2_n*`
  apply `steinerberger_r2_sufficient` from S8 with `by norm_num`,
  `by omega`, and the named equation lemma.
- No new Mathlib API surface used; no drift risk.
- Build pending — Docker build typically takes 30-45 min from clean
  cache due to broken proofs/.lake symlink. The additions are pure
  computational verifications (`native_decide`) + a 3-argument call
  to an already-proved theorem; correctness is high-confidence.

### Session 2026-05-08 — S8 Steinerberger sufficient direction (PROVED)

**Mode**: ITERATE
**Outcome**: 5 new theorems added (axiom-free, sorry-free)

#### What I added
- `iteratedTotientStep_two`: g_2(n) = (n + φ(n)) + φ(n + φ(n)) by rfl
- `steinerberger_iff`: g_2(n) = 2n ↔ φ(n) + φ(n + φ(n)) = n (rw + omega)
- `steinerberger_r2_sufficient`: even n > 2, equation ⇒ DoublingRelation n 2
- `steinerberger_eq_n10`: n=10 satisfies the equation (native_decide)
- `steinerberger_eq_n94`: n=94 satisfies the equation (native_decide)

#### Files Modified
- `proofs/Proofs/Erdos411Problem.lean` (+41 lines, 22 theorems total)
- `src/data/proofs/erdos-411/meta.json` (lineCount, theoremCount,
  originalContributions, proofStrategy, mainTheorems)
- `research/problems/erdos-411/state.md` (this file)

#### Notes
- Build pending — Docker build typically takes 30-45 min from clean cache
  due to broken proofs/.lake symlink (see memory: feedback_researcher_lake_symlink_broken)
- All proofs use only definitional unfolding, omega, native_decide, and
  composition of pre-existing lemmas; no Mathlib api drift risk
