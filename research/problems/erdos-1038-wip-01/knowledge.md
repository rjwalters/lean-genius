# Erdős #1038 WIP-01 — Knowledge Base

## Problem

Supremum/infimum of |{x : |f(x)| < 1}| over non-constant monic polynomials with all
roots real in [-1,1]. Sup = 2√2 (Erdős–Herzog–Piranian 1958 conjecture, Tao 2025 proof).
The extremal witness is (the limit of polynomials approaching) x²−1.

## Session 2026-07-08 (researcher-1) — formalize the supremum object + provable lower bound

The predecessor file `Erdos1038WIP01.lean` proved the extremal quadratic's sublevel
measure is exactly 2√2 but never connected it to "the supremum". Added:
- `sublevelSup := ⨆ (f) (_ : MonicRealRootedIn01 f), sublevelMeasure f` — the extremal
  quantity as a Lean object (first time it is defined).
- `le_sublevelSup : ENNReal.ofReal (2√2) ≤ sublevelSup` — the machine-checkable HALF of
  Tao's `sublevelSup = 2√2`. One-liner: `le_iSup_of_le q (le_iSup_of_le
  quadratic_admissible sublevelMeasure_quadratic.ge)`. The matching UPPER bound
  (= 2√2) needs logarithmic potential theory beyond Mathlib — documented, not attempted.

Verified 0 axioms / 0 sorries; built via docker wrapper on retry 3 (shared-volume cache
corruption: line-less exit-135 then `UniqueFactorizationDomain/Basic.olean.private invalid
header`, healed across retries as the failure point advanced 1.3s→8.1s→green). Pre-existing
linter note at L85 (`simpa using h0`) is in the original code, harmless.

Status: the provable direction of the headline sup=2√2 is now formalized. Upper bound and
the infimum exact value (2^(4/3)−1 ≤ inf ≤ 1.835) remain OPEN/blocked (potential theory).

## Session 2026-07-08 (researcher-6) — the infimum side, second exact witness

Executed the first documented next step (the infimum side). Added:
- `sublevelInf := ⨅ (f) (_ : MonicRealRootedIn01 f), sublevelMeasure f` — the companion
  extremal quantity as a Lean object (first time it is defined).
- The linear polynomial `X` as a SECOND exact witness: `linear_admissible` (monic_X, root
  0 ∈ [-1,1] via mem_roots'), `sublevelSet_linear : sublevelSet X = Ioo(-1,1)` (abs_lt),
  `sublevelMeasure_linear : = ENNReal.ofReal 2` (Real.volume_Ioo + ring).
- `sublevelInf_le_two : sublevelInf ≤ ENNReal.ofReal 2` — one-liner mirroring the sup
  side: `iInf_le_of_le X (iInf_le_of_le linear_admissible sublevelMeasure_linear.le)`.

The `≤ 2` bound is genuine and machine-checked but NOT tight — the true infimum is ≤ 1.835,
witnessed by (x+1)(x−1)^m (m ≥ 3), which needs logarithmic potential theory beyond Mathlib.
Documented as such, not overclaimed. File now: 6 defs + 9 theorems, 172 lines, 0/0.

## Session 2026-07-08 (researcher-1) — the infimum is exactly 0 under the literal predicate

Sharpened the infimum side. The `MonicRealRootedIn01 f` predicate is
`f.Monic ∧ (∀ r ∈ f.roots, r ∈ [-1,1])` — it only constrains the real roots `f`
*actually has*; it does NOT force `f` to split over `ℝ`. So the rootless monic
`X² + 1` (empty real-root multiset) is vacuously admissible, and its sublevel set
`{x : |x²+1| < 1}` is empty. Added:
- `sq_add_one_admissible` — `X²+1` is monic (`monic_X_pow_add_C 1 two_ne_zero`) with
  no real roots (`mem_roots'` gives `r²+1=0`, killed by `nlinarith [sq_nonneg r]`).
- `sublevelSet_sq_add_one : = ∅` (|x²+1| ≥ 1 always).
- `sublevelMeasure_sq_add_one : = 0` (`measure_empty`).
- `sublevelInf_eq_zero : sublevelInf = 0` — `le_antisymm` of the iInf_le chain and
  `zero_le`. This SHARPENS `sublevelInf_le_two` (from ≤2 to exact 0) and shows the
  literal predicate is NOT faithful: the intended infimum `2^(4/3)−1 ≈ 1.52` requires
  the stronger hypothesis `f.roots.card = f.natDegree` (complete splitting over ℝ),
  which excludes `X²+1`.

File now: 6 defs + 13 theorems, 227 lines, 0 axioms / 0 sorries. Host-verified via
`lake env lean` (Docker shared-volume corruption produced spurious line-less
SIGBUS-135/SIGSEGV-139 at olean-write across 5 retries; elaboration always completed
clean in ~2s). `#print axioms` = {propext, Classical.choice, Quot.sound} only.

FOLLOW-UP (not pursued, needs potential theory): the faithful infimum under the
splitting hypothesis is still open (`2^(4/3)−1 ≤ inf ≤ 1.835`). A worthwhile next
step is to DEFINE the faithful predicate `MonicRealRootedIn01'` (add
`f.roots.card = f.natDegree`) and re-establish that `q = X²−1` and `X` satisfy it,
so the sup lower bound `2√2 ≤ sup'` transfers to the faithful object.

## Session 2026-07-08 (researcher-1) — the faithful splitting predicate + transferred sup bound

Executed the documented next step: defined the faithful predicate and transferred the
supremum lower bound to it. Added (8 declarations, file now 21 thm + 9 def, 321 lines,
0 axioms / 0 sorries, Docker build green on retry — SIGBUS-135 first attempt):

- `MonicRealRootedIn01' f := MonicRealRootedIn01 f ∧ f.roots.card = f.natDegree` — the
  faithful predicate adding complete splitting over ℝ (real roots account for full degree).
- `q_roots : q.roots = {1, -1}` — via `q = (X - C 1)*(X - C (-1))` (`simp [C_neg, C_1]; ring`)
  then `roots_mul` (needs product ≠ 0, from `quadratic_admissible.1.ne_zero`) + `roots_X_sub_C`×2.
- `quadratic_faithful : MonicRealRootedIn01' q` — `roots.card = 2 = natDegree`
  (natDegree via `compute_degree!`, card {1,-1} = 2 by rfl).
- `linear_faithful : MonicRealRootedIn01' X` — `roots_X`/`natDegree_X`, card {0}=1=1 (needs
  trailing `rfl`: `rw [roots_X, natDegree_X]` leaves `{0}.card = 1`, NOT auto-closed).
- `sq_add_one_not_faithful : ¬ MonicRealRootedIn01' (X²+1)` — roots empty (card 0) but
  natDegree 2; the exact polynomial that degenerated the literal infimum is excluded.
  Proof: `roots = 0` via `Multiset.exists_mem_of_ne_zero` + `nlinarith [sq_nonneg r]`.
- `sublevelSup'`, `le_sublevelSup' : 2√2 ≤ sublevelSup'` — the sup lower witness transfers
  (`le_iSup_of_le q (le_iSup_of_le quadratic_faithful sublevelMeasure_quadratic.ge)`).
- `sublevelSup'_le_sublevelSup`, `sublevelInf_le_sublevelInf'` — the faithful set ⊆ literal
  set, so sup drops / inf rises (`iSup_le`/`le_iInf` + `hf.1` to demote faithful→literal).
- `sublevelInf'`, `sublevelInf'_le_two` — linear witness; the faithful inf is no longer the
  spurious 0 (`sq_add_one` excluded), so `0 = sublevelInf ≤ sublevelInf' ≤ 2`.

The provable HALF of the intended `sublevelSup' = 2√2` is now formalized against the
faithful object. STILL OPEN (needs logarithmic potential theory, beyond Mathlib): the
matching sup upper bound, and the exact faithful infimum `2^(4/3)−1 ≤ inf ≤ 1.835`.
