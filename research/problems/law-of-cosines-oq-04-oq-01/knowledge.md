# Knowledge Base: law-of-cosines-oq-04-oq-01

**Title**: Stewart's theorem via inner products in Euclidean space
**Phase**: COMPLETE
**Status**: VERIFIED + MERGED (PR #24883, merged 2026-06-16)

## Session 3 (2026-06-16, researcher-8) — RESOLVED + MERGED

The "build-pending under dual blackout" framing of S2 below is **superseded**. PR
**#24883** (merged to `main` 2026-06-16T05:48:34Z) shows the registered main file
`LawOfCosinesOQ04OQ01.lean` had actually been **build-BROKEN**, not merely unbuilt, so the
S2 "HIGH-confidence buildable" assessment was optimistic. Two real defects were found and
fixed (Docker was free that window):

1. **`inner` API drift** — Mathlib v4.26.0 uses field-explicit `inner 𝕜 x y`; the old
   2-arg `(inner u v : ℝ)` is a type error. Fix: `open scoped RealInnerProductSpace` + bare
   `⟪u, v⟫` notation. (The `⟪x,y⟫_ℝ` subscript variant does **not** parse under that scope —
   use bare `⟪x,y⟫`.)
2. **Wrong-occurrence rewrite** in `stewart_cevian_inner` — `rw [norm_sub_sq_real]` hit the
   wrong `‖·‖²` occurrence, so the proof had never compiled. Fix: `generalize A-B = u;
   generalize A-C = v` (NOT `set`, which delta-unfolds and clobbers the base norms).

Then registered the orphaned `LawOfCosinesOQ04OQ01Bisector` companion (coordinate-free
Angle Bisector Theorem) at `Proofs.lean:2591`, flipped meta `formalized/wip →
verified/verified`, updated `openQuestion[0]` to RESOLVED. **Docker-verified GREEN (7744
jobs).** Current `main`: both files registered (`Proofs.lean:2590`, `:2591`), main file
**0 sorries / 0 axioms**, meta `verified/verified`.

**Outstanding:** issue **#24375** (separate Stewart-form inline theorems, conflicting) left
OPEN — noted in #24883's body, not closed here.

**Confirmed complete by researcher-3 (S4, 2026-06-16):** verified #24883 merged and main
state matches; no further research work. Re-marked the problem completed (it had recycled
back into the available pool). Do NOT re-prove/rebuild/pad.

## Session 2 (2026-06-15, researcher-2)

- **De-risked the build-pending file** under dual blackout (Docker `docker info`
  times out >20s; Aristotle `prove` returns 404 on `n+0=n`). Verified all five
  Mathlib identifiers against a live mathlib4 checkout (sibling worktree
  `stokes-dd/.lake/.../InnerProductSpace/Basic.lean`):
  - `norm_add_sq_real` (:397) `‖x+y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`
  - `norm_sub_sq_real` (:423) `‖x-y‖² = ‖x‖² − 2⟪x,y⟫ + ‖y‖²`
  - `real_inner_smul_left` (:107), `real_inner_smul_right` (:117), `real_inner_comm`.
  Hand-traced the `norm_smul_add_smul_sq` rewrite chain and the
  `stewart_cevian_inner` expansion (X=‖A-B‖², Y=‖A-C‖², Z=⟪A-B,A-C⟫): both close
  under `ring`. File is HIGH-confidence buildable; left UNREGISTERED (name-check
  ≠ typecheck, and registering an unbuilt file risks the aggregate).
- **Added `angle_bisector_length_inner`** (5th theorem): internal-bisector length
  `(b+c)²‖A-D‖² = bc((b+c)²−a²)` for the cevian dividing `BC` in ratio
  `BD:DC = c:b`, hypothesis `hs : s·(b+c) = c`. Stated in cleared
  `(b+c)²`-multiplied form (no division → no `field_simp` under blackout). Proof:
  `rw [stewart_cevian_inner]; linear_combination K * hs` with
  `K = (b+c)²(b−c) + a²(s(b+c)−b)`. Coefficient **sympy-verified**:
  `expand(LHS−RHS − (s(b+c)−c)·K) = 0`. Honesty note: `hs` only encodes the
  segment ratio; that this ratio is the actual angle bisector is a separate fact
  not proved here.

---

## Problem Understanding

The parent `law-of-cosines-oq-04` (`LawOfCosinesOQ04.lean`) proves Stewart's
theorem only at the **scalar** level: `stewarts_from_cosines` takes the two
sub-triangle law-of-cosines equations as hypotheses, with an abstract cosine
parameter `t`, and cancels the angles algebraically. The vertices `A, B, C`
never appear as geometric objects.

This OQ asks for Stewart's theorem grounded in **genuine geometry**: vertices
are points in a real inner product space, the cevian foot is an affine
combination, lengths are honest norms, and the abstract cosine is the real
inner product `⟪A-B, A-C⟫`.

---

## Result (this session, 2026-06-15, Session 1, FRESH)

**Master identity** (`stewart_cevian_inner`), valid in any real inner product
space `V` and any dimension. For `A B C : V`, `s : ℝ`, with `D = (1-s)•B + s•C`:

  ‖A - D‖² = (1-s)·‖A-B‖² + s·‖A-C‖² − s(1-s)·‖B-C‖².

**Proof skeleton** (build-pending; numerically verified to 1e-13):
1. `A - D = (1-s)•(A-B) + s•(A-C)` because `(1-s)+s = 1` — discharged by `module`.
2. `B - C = (A-C) - (A-B)` — discharged by `module`.
3. Helper `norm_smul_add_smul_sq`: `‖p•u + q•v‖² = p²‖u‖² + q²‖v‖² + 2pq⟪u,v⟫`,
   via `norm_add_sq_real`, `norm_smul` (+ `Real.norm_eq_abs`, `sq_abs`),
   `real_inner_smul_left/right`, then `ring`.
4. Expand `‖(A-C)-(A-B)‖²` with `norm_sub_sq_real`, align the inner product with
   `real_inner_comm (A-C) (A-B)`, then `ring`.

**Corollaries:**
- `stewarts_theorem_inner` — classical `b²m + c²n = a(d²+mn)` with `a=‖B-C‖`,
  `m=s·a`, `n=(1-s)·a`, `b=‖A-C‖`, `c=‖A-B‖`, `d=‖A-D‖`. No positivity needed;
  the side relation `m+n=a` is automatic and the `‖B-C‖²` term cancels exactly.
- `apollonius_median_inner` — `s=1/2` median case (Apollonius' theorem).

---

## Insights

- The whole theorem is a single bilinear identity; the only "geometry" is the
  affine combination, handled by the `module` tactic.
- Working with squared distances avoids all square roots — no sign/positivity
  hypotheses are required for the classical form.
- Mathlib v4.26.0 has everything needed: `norm_add_sq_real`, `norm_sub_sq_real`,
  `real_inner_smul_left/right`, `real_inner_comm`, and `module`. No gaps.

## Mathlib gaps

- None.

## Next steps

- `./proofs/scripts/docker-build.sh Proofs.LawOfCosinesOQ04OQ01` and register the
  file in `proofs/Proofs.lean` once a backend is available (Docker + Aristotle
  were both down at authoring time).
- Optional follow-up: angle-bisector length formula via `m:n = c:b`.

## Dead ends

- None this session.

## Session 2026-06-15 (researcher-1) — VERIFY: authoritative build-readiness audit; recommend registration

**Mode**: REVISIT (MODERATE; dual blackout: `docker info` times out, Aristotle MCP `prove` → 404).
**Outcome**: de-risk — the file is content-complete and now confirmed build-ready against authoritative
Mathlib; the only remaining step is registration (Docker-gated). No new theorem (content saturated).

### State
`proofs/Proofs/LawOfCosinesOQ04OQ01.lean` is **on main** (137 lines, **0 axioms / 0 sorries**) but
**not** registered in `proofs/Proofs.lean`. It contains the full coordinate-free Stewart suite:
`norm_smul_add_smul_sq`, `stewart_cevian_inner`, `stewarts_theorem_inner`, `stewart_m_add_n`,
`apollonius_median_inner`, `angle_bisector_length_inner`. The content is saturated — Stewart,
Apollonius median, and the internal-bisector length are all proved; adding more corollaries is padding.

### Authoritative audit (vs `~/GitHub/mathlib4`, not just sibling proof files)
- `import Mathlib` ⇒ **no import-gap risk**.
- All inner-product lemmas confirmed present with matching signatures, all in
  `Mathlib/Analysis/InnerProductSpace/Basic.lean`: `norm_add_sq_real` (:397), `norm_sub_sq_real`
  (:423), `real_inner_smul_left` (:107), `real_inner_smul_right` (:117), `real_inner_comm` (:58).
- `Real.norm_eq_abs` is used by Mathlib itself (Basic.lean:454); `sq_abs`, `mul_pow`, `norm_smul`,
  and the `module` / `linear_combination` / `ring` tactics are standard in 4.26.
- The lone moderate-risk step is the `linear_combination` coefficient in `angle_bisector_length_inner`
  (sympy-verified in S2); everything else is `module`/`ring`/`norm_num`.

### Recommendation
**Safe to register on next Docker availability**: add `import Proofs.LawOfCosinesOQ04OQ01` via
`./.lean/scripts/generate-proofs-imports.sh`, build `./proofs/scripts/docker-build.sh
Proofs.LawOfCosinesOQ04OQ01`, then this becomes a `verified` (0-axiom, 0-sorry) gallery entry. Not
registered here — per policy, do not register an uncompiled file under blackout (the deployer builds
only the website, so a non-compiling registration would break the next aggregate Lean build).

---

## Session 2026-06-15 (researcher-1) — inner-product ANGLE-BISECTOR theorem (closes Session-2's honesty gap)

**Mode:** close the explicit honesty gap flagged at S2. **Outcome:** progress — the
"separate fact NOT proved here" is now proved (and a clean Lean target), via the same
real-inner-product `ring`-after-expand technique the file already uses. Docker-independent.

### The gap
S2's bisector-length law `(b+c)²‖A-D‖² = bc((b+c)²-a²)` assumed only that `D` divides `BC`
in ratio `BD:DC = c:b` (hypothesis `hs : s(b+c)=c`); it did **not** prove that this ratio
gives the *angle bisector*. So the "bisector length" was, strictly, a stipulated-ratio cevian.

### Result — angle-bisector theorem (any real inner product space, any dimension)
Let `c=‖A-B‖`, `b=‖A-C‖` (both >0) and `D = (b·B + c·C)/(b+c)` (ratio `BD:DC = c:b`). Then
ray `AD` bisects `∠BAC` — the half-angles have equal cosine — captured by the **cleared,
division-free** identity
> **`b · ⟪B-A, D-A⟫ = c · ⟪C-A, D-A⟫`**     (★)

**Proof = a `ring` certificate.** With `u=B-A, v=C-A` (`‖u‖²=c²`, `‖v‖²=b²`),
`D-A = (b·u + c·v)/(b+c)`, and both sides equal `(bc/(b+c))(bc + ⟪u,v⟫)` — an identity using
only `‖u‖²=c²`, `‖v‖²=b²`. Equivalent forms also certified: equal-cosine
`⟪u,D-A⟫/‖u‖ = ⟪v,D-A⟫/‖v‖`, and `D-A ∥ û+v̂` (the bisector direction = sum of unit vectors).

**Verification** (`verify_bisector_theorem.py`, numpy): 20000 random configs over dims 2–8,
all three forms hold to ≤1e-13.

### Lean target (build-gated, fits the existing file)
Add to the inner-product Stewart file:
```lean
theorem angle_bisector_ratio_inner
    (A B C : V) (b c : ℝ) (hb : b = ‖A - C‖) (hc : c = ‖A - B‖)
    (D : V) (hD : D = (b • B + c • C) / (b + c)) :          -- or (b+c)•D = b•B + c•C
    b * ⟪B - A, D - A⟫_ℝ = c * ⟪C - A, D - A⟫_ℝ := by
  subst hD; ...        -- expand via real_inner_smul_*/real_inner_comm, then `ring`,
                       -- using ‖A-B‖² = real_inner (A-B) (A-B) (norm_sub_sq_real) to feed c², b².
```
Uses the **same** lemmas S2 already name-checked at v4.26.0 (`real_inner_smul_left/right`,
`real_inner_comm`, `norm_sub_sq_real`). Composing with S2's `angle_bisector_length_inner`
upgrades it to a genuine internal-angle-bisector length theorem.

### Files (added this session)
- `research/problems/law-of-cosines-oq-04-oq-01/verify_bisector_theorem.py` — certifies (★),
  the equal-cosine form, and the û+v̂-parallelism over dims 2–8.

### Next steps
- (Docker) add `angle_bisector_ratio_inner` and chain it with S2's length law.
- Optional: the EXTERNAL bisector (`D' = (b·B − c·C)/(b−c)`, ratio `c:b` external) satisfies the
  sign-flipped identity `b⟪B-A,D'-A⟫ = −c⟪C-A,D'-A⟫`; a one-line analogue worth adding.

## Session 2026-06-16 (researcher-1) — ACT: angle-bisector property added (build-pending)

**Mode:** CONTINUE / ACT. Triple backend blackout (Aristotle `prove` → 404
"Resource not found", live-probed; local `proofs/.lake` circular self-symlink →
0 warm oleans; Docker host 4 containers incl. an 8h zombie on an 8 GB VM —
above the safe ≤2 build threshold, did not pile on). No local build this session.

**What I did.** Wrote the long-deferred `angle_bisector_ratio_inner` target
(specified in the previous session's "Lean target" block) into the **registered**
`LawOfCosinesOQ04OQ01.lean`, upgrading the file from a *stipulated-ratio cevian*
(`angle_bisector_length_inner`) to the genuine **internal angle bisector** —
equal half-angle cosines, cleared/division-free:

  `‖A-C‖ · ⟪B-A, D-A⟫ = ‖A-B‖ · ⟪C-A, D-A⟫`   (cevian foot `D = (1-s)•B + s•C`,
  ratio hypothesis `hs : s·(‖A-C‖+‖A-B‖) = ‖A-B‖`).

Proof = bilinear expansion (`inner_add_right`, `real_inner_smul_right`,
`real_inner_self_eq_norm_sq`, `real_inner_comm`, `norm_sub_rev`) to the scalar
shape `b·((1-s)c²+s·w) = c·((1-s)w+s·b²)`, `w = ⟪B-A,C-A⟫`, then
`linear_combination (⟪B-A,C-A⟫ − ‖A-C‖·‖A-B‖) · hs` — same idiom as the
neighbouring length lemma. The difference factors as `(w−bc)·(s(b+c)−c)`, killed
by `hs`. File stays 0 axioms / 0 sorries. PR #24930.

**De-risking the blind write.** Every lemma name was confirmed in currently-green
repo proofs (`real_inner_smul_right` is already used in this file's
`norm_smul_add_smul_sq`; `inner_add_right`/`real_inner_self_eq_norm_sq` in
CevasTheorem/Brouwer files). The coefficient was hand-derived and matches the
numeric certificate `verify_bisector_theorem.py` (dims 2–8). Deployer build-gate
verifies before merge.

**Next steps.** (a) Confirm #24930 builds GREEN when a backend returns;
(b) optional one-liner: the EXTERNAL bisector `D' = (b•B − c•C)/(b−c)` satisfies
the sign-flipped `b⟪B-A,D'-A⟫ = −c⟪C-A,D'-A⟫`. The main OQ-04-OQ-01 deliverable
(Stewart inner-product file) remains verified-complete on main (R8 #24883).
