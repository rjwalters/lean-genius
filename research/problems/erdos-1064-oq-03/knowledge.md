
## Session 2026-07-08 (researcher-6) — general transport removes the v₂(2a−φ(a))=1 restriction (excluded case DONE)

Executed the outstanding nextStep "Handle the excluded case v₂(2a−φ(a))>1". The
whole transport programme (`dblIter_transport`, `dblIter_*_iff`) assumed the first
cototient step `2a−φ(a)=2·b` with `b` odd — i.e. 2-adic valuation EXACTLY 1 —
excluding every seed with `v₂(2a−φ(a))≥2` (smallest: a = 3,7,9,11,27,…).

Generalisation (all VERIFIED 0 sorry / 0 axiom, docker [3058/3058]):
- `dblIter_transport_general` : with `2a−φ(a)=2^s·b` (s≥1, b odd),
  `D(a·2^(k+1)) = (2a − φ(b)·2^(s−1))·2^k`. Proof: the first step lands on
  `b·2^(k+s)` (valuation k+s), so `φ(step)=φ(b)·2^(k+s−1)`, giving the landing
  constant `C = 2a − φ(b)·2^(s−1)` (= old `2a−φ(b)` at s=1).
- `dblIter_transport_of_general` : recovers the old s=1 lemma via `pow_one`.
- `dblIter_totient_values_general` + `dblIter_{reversal,equality,forward}_iff_general` :
  criterion now reads regime off `φ(a) ⋛ φ(e)·2^(t−1)` with `C=e·2^t`, for arbitrary s.
- New excluded-seed families: `mem_EqualitySet_three` (a=3,s=2,e=b=1,t=2),
  `mem_EqualitySet_nine` (a=9,s=2,b=3,e=7,t=1), `mem_ForwardSet_seven` (a=7,s=3,b=1,e=5),
  `mem_ForwardSet_twentyseven` (a=27,s=2,b=9,e=21). Plus `totient_3/7/9/27`.
- `excluded_seeds_realize_equality_and_forward` capstone.

**New structural fact (brute check a<120):** among excluded seeds (v₂≥2) ONLY the
equality and forward regimes occur — NO excluded seed reverses. So the two realised
regimes exhaust the excluded phenomenology below 120. (All reversal seeds found so
far — 21,55,129,165,175 — have v₂=1.) PR #35885. Density-1 forward remains the sole
deep-open direction.

## Session 2026-07-08 (researcher-1) — second reversal seed a=55 (reversal set not the singleton {21})

Executed nextStep #2 (characterise the reversal seed set). The k-free three-way
criterion (dblIter_reversal_iff, in Proofs/EulerTotientOQ04OQ03.lean) makes the
per-seed reversal test φ(a) < φ(e)·2^(t−1) a finite computation on odd data. Brute
search over odd seeds a<200 (φ via the criterion arithmetic) gives reversal seeds
21, 55, 129, 165, 175, … — so 21 is smallest and 55 is the SECOND.

Added (all VERIFIED 0 axioms / 0 sorries, host lake env lean):
- totient_55 = 40, totient_35 = 24 (by decide, kernel — NOT native_decide, no ofReduceBool),
  totient_43 = 42 (Nat.totient_prime).
- reversal_via_criterion_55 (k) : 55·2^(k+1) ∈ ReversalSet. Criterion data a=55, b=35,
  e=43, t=1: 2·55−φ(55)=70=2·35 (b odd, v₂=1 OK), 2·55−φ(35)=86=43·2^1, φ(55)=40<42=φ(43)·2^0.
  Same proof shape as reversal_via_criterion (21): rw dblIter_reversal_iff (by decide ×3,
  norm_num for ht/hstep/hC) then norm_num [totient_55, totient_43].
- two_distinct_reversal_families : both 21·2^(k+1) and 55·2^(k+1) reverse ∀k, and 21≠55.
  (Kept the distinctness statement to seed-inequality 21≠55; a full ∀j,k family-disjointness
  proof hit exponent-arithmetic pitfalls — dropped as low-value/high-risk.)

File 794→829 lines, 56 theorems. NO gallery meta references EulerTotientOQ04OQ03.lean
(research file), so no count sync. Density-1 forward remains the sole deep-open direction
(needs ψ(x,y)). Further reversal seeds (129,165,175) and the excluded v₂(2a−φ(a))>1 case
remain as future elementary increments.

## Session 2026-07-08 (researcher-6) — Total decidable classifier

**Mode**: REVISIT | **Outcome**: progress (VERIFIED 0 sorry / 0 axiom)

### What I Did
- Turned the k-free three-way criterion into a COMPUTABLE total classifier in
  `EulerTotientOQ04OQ03.lean`:
  - `seedS/seedB/seedC/seedT/seedE`: from an odd seed `a`, extract `(s,b,t,e)`
    by two 2-adic valuations — `s=v₂(2a−φ(a))`, `b`=odd part, landing
    `C=2a−φ(b)·2^(s−1)`, `t=v₂(C)`, `e`=odd part of `C`.
  - `classifySeed a := compare (φ a) (φ(seedE a)·2^(seedT a−1))`.
- `seed_spec` (holds for all `a≥3`, oddness of `a` not required): the extracted
  data meets every hypothesis of `dblIter_*_iff_general` — `Odd b`, `Odd e`,
  `s,t≥1`, `2a−φ(a)=2^s·b`, `2a−φ(b)·2^(s−1)=e·2^t`.
- `classifySeed_lt_iff/_eq_iff/_gt_iff` + `classifySeed_classifies`: for every
  odd `a≥3`, `classifySeed a` correctly decides the regime of `a·2^(k+1)`.

### Key Findings
- The extraction is total: `C>0` always (φ(b)·2^(s−1) ≤ b·2^(s−1) = (2a−φ(a))/2
  < 2a), and `C` is even for `a≥3` because the only obstruction `s=1 ∧ b=1`
  forces `φ(a)=2a−2`, impossible for `a≥3` (φ(a)≤a−1). So `t≥1`.
- Mathlib plumbing: `Nat.ordProj_mul_ordCompl_eq_self` gives `2^v·oddpart = n`
  by defeq (no rewriting), `Nat.not_dvd_ordCompl` gives oddness; in this build
  `not_dvd_ordCompl` wants `Nat.Prime` (not `Prime`), and `Nat.totient_lt` takes
  `n` explicitly.
- The reversal seed set is now the decidable predicate `{a | classifySeed a = .lt}`.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (1048→1179; +6 defs, +5 theorems)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Next Steps
- Characterise `{odd a≥3 | classifySeed a = .lt}` structurally, or prove
  `seedS a ≥ 2 ⇒ classifySeed a ≠ .lt` (no excluded seed reverses; observed a<120).
- Density-1 forward stays analytically blocked (ψ(x,y)/Luca–Pomerance gap).

## Session 2026-07-08 (researcher-6) — Unconditional smallest reversing seed

**Mode**: REVISIT (pool file absent; branch dedicated to this problem, RICH tier)
**Outcome**: progress (VERIFIED host 0/0)

### What I Did
- Strengthened the merged `twentyone_least_reversal_seed` / `least_reversal_seed_families`
  (which are gated by `ValidSeed a` and cover only the four transport-admissible
  seeds {5,13,15,17} below 21) to an **unconditional** statement over all odd seeds,
  using the total computable `classifySeed`.
- `twentyone_smallest_reversing_seed`: `21·2^(k+1) ∈ ReversalSet` for all k, and for
  every odd `a` with `3 ≤ a < 21` (no admissibility hypothesis) `a·2^(k+1) ∉ ReversalSet`.
- Built `factor_two_split` (reusable: `n = c·2^u`, `c` odd ⟹ `n.factorization 2 = u ∧
  oddpart = c` — the computable content of seedS/seedB and seedT/seedE) and
  `classifySeed_val` (evaluates `classifySeed a` from the two 2-adic factorisations),
  then the ten per-seed evaluations `classifySeed_3..19`, `classifySeed_21'`.

### Key Findings
- The higher-valuation seeds {3,7,9,11,19} (v₂(2a−φ(a)) ≥ 2) are NOT `ValidSeed`, so the
  old `classify`/ValidSeed sweep said nothing about them; the total `classifySeed`
  (via `seed_spec`, valid for all odd a≥3) closes them — each classifies to `.eq`/`.gt`.
- This resolves the a<21 case of the open question "does any excluded seed reverse?":
  none below 21 does.
- Hand-computed regimes: 3→eq, 5→eq, 7→gt, 9→eq, 11→gt, 13→gt, 15→eq, 17→gt, 19→gt, 21→lt.

### Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+129, pure additive)
- `src/data/research/problems/erdos-1064-oq-03.json`

### Verification note
Host `lake env lean` exit 0, 0 sorry, axioms `[propext, Classical.choice, Quot.sound]`
(no `Lean.ofReduceBool`, no `native_decide`). Docker build blocked all session by a
persistent fleet write-stage SIGBUS-135 (line-less, after clean `[3058/3058]`
elaboration) — verified on host instead (file imports only Mathlib).

### Next Steps
- Extend the unconditional sweep upward, or prove `seedS a ≥ 2 ⇒ classifySeed a ≠ .lt`
  (no excluded seed ever reverses; observed a<120).
- Density-1 forward `φ(n) > φ(D(n))` a.e. remains the sole analytically-blocked direction.
