# Erdős #1038 WIP-01 — Knowledge Base

## Problem

Supremum/infimum of |{x : |f(x)| < 1}| over non-constant monic polynomials with all
roots real in [-1,1]. Sup = 2√2 (Erdős–Herzog–Piranian 1958 conjecture, Tao 2025 proof).
The extremal witness is (the limit of polynomials approaching) x²−1.


## Session 2026-07-08 (researcher-4) — per-polynomial positivity: why faithfulness fixes inf-zero

Took the "cheap next win" from the previous session AND supplied the mechanism behind the
`sublevelInf_eq_zero` degeneracy at the *per-polynomial* level (the substantive new content).
Added:
- `isOpen_sublevelSet f : IsOpen (sublevelSet f)` — `{x : |f(x)| < 1} = eval⁻¹ (Ioo −1 1)`
  (`abs_lt` rewrite), open as the preimage of an open interval under `f.continuous`.
- `sublevelMeasure_pos_of_root f (hr : r ∈ f.roots) : 0 < sublevelMeasure f` — `f(r)=0`
  (`isRoot_of_mem_roots`) puts `r` in the *open* sublevel set, and `IsOpen.measure_pos`
  for the open-positive `volume` gives positive measure. (General: needs only a real root,
  not faithfulness.)
- `faithful_sublevelMeasure_pos f (hf : MonicRealRootedIn01' f) (hdeg : 1 ≤ natDegree) :
  0 < sublevelMeasure f` — faithful ⟹ `roots.card = natDegree ≥ 1` ⟹ root multiset nonempty
  (`Multiset.exists_mem_of_ne_zero`) ⟹ has a real root ⟹ positive measure. This is *exactly*
  the property the rootless `X²+1` fails (degree 2, empty roots, empty sublevel set) — the
  driver of `sublevelInf_eq_zero`. Faithfulness forbids it, so every positive-degree faithful
  witness contributes positive measure.
- `sublevelInf' := ⨅ (f) (_ : MonicRealRootedIn01' f), sublevelMeasure f` and
  `sublevelInf'_le_two : sublevelInf' ≤ 2` (linear witness, mirrors `sublevelInf_le_two`,
  now free of the rootless collapse).

Honest scope: this proves positivity *per polynomial*, NOT `sublevelInf' > 0` (an infimum
over infinitely many f could still tend to 0). The exact faithful infimum `2^(4/3)−1` and
the strict lower bound `sublevelInf' > 0` remain open (need logarithmic potential theory).

VERIFIED docker exit 0 (7743 jobs; one spurious line-less SIGBUS-135 on a comment-only
rebuild, green on retry). 0 axioms / 0 sorries. File 293→368 lines, 17→21 theorems, 8→9 defs.

## Session 2026-07-08 (researcher-4) — the faithful (complete-splitting) predicate + sup transfer

Executed the documented next step (define the faithful predicate, transfer the sup lower
bound, exclude the X²+1 pathology). Added:
- `MonicRealRootedIn01' f := MonicRealRootedIn01 f ∧ f.roots.card = f.natDegree` — the
  faithful predicate (f splits completely over ℝ, all roots in [-1,1]).
- `sublevelSup' := ⨆ (f) (_ : MonicRealRootedIn01' f), sublevelMeasure f`.
- `quadratic_admissible'` — X²−1 is faithfully admissible: factor `q = (X−C 1)(X−C(−1))`
  (`simp only [q, map_one, map_neg]; ring`), then `roots_mul` + `roots_X_sub_C` twice gives
  roots.card = 2 = natDegree (`compute_degree!`).
- `linear_admissible'` — X is faithfully admissible: `roots_X` gives {0}, card 1 = natDegree 1.
- `le_sublevelSup' : ofReal(2√2) ≤ sublevelSup'` — the 2√2 lower bound transfers verbatim
  (one-liner mirroring `le_sublevelSup`), since X²−1 splits and stays admissible.
- `sq_add_one_not_admissible' : ¬ MonicRealRootedIn01' (X²+1)` — X²+1 has 0 real roots but
  natDegree 2 (`Multiset.eq_zero_iff_forall_notMem` + `nlinarith [sq_nonneg r]`), so it is
  EXCLUDED. This is the point: the `sublevelInf_eq_zero` degeneracy needed X²+1's vacuous
  admissibility, which the faithful predicate removes.

VERIFIED docker exit 0 (7743 jobs, first try; cleaned 2 self-introduced lint warnings on a
2nd build). 0 axioms / 0 sorries. File 227→293 lines, 13→17 theorems, 6→8 defs.

STILL OPEN/blocked (potential theory beyond Mathlib): the faithful infimum exact value
2^(4/3)−1 ≈ 1.52, and both matching upper bounds (sup'=2√2, the Tao 2025 side).
Cheap next win: define `sublevelInf'` and mirror `linear_admissible'` for a faithful
`sublevelInf' ≤ 2`.

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
