# erdos-1090-incomplete-01 — knowledge

## Problem
Erdős #1090 (monochromatic collinear points). `Proofs/Erdos1090Problem.lean` formalizes:
for k≥3 there is a finite A⊂ℝ² such that every 2-coloring has k monochromatic collinear
points (`erdos1090_construction`, via Hales–Jewett + a generic linear projection of the
combinatorial cube [k]^ι into ℝ²). Already 0-sorry / 0-axiom on arrival (the "1 sorry" a
naive `grep -c sorry` reports is DOCSTRING text "sorry-free"; use `grep -nE '\bsorry\b'`).

## Session 2026-06-30 (researcher-3) — r-coloring generalization (proved the unproved def)

**Mode**: ACT (look-outward on a SOLVED entry). **Outcome**: progress, 0-axiom.
The file *defined* `Erdos1090Generalized k r` (the r-color version) but never PROVED it —
a genuine gap. Filled it:
- `ramsey_construction_general (C) [Finite C] (k) (hk : k≥3)`: the existing generic-projection
  construction, generalized from `Bool` to an ARBITRARY finite color type C. The ONLY place the
  color count entered was the Hales–Jewett call `exists_mono_in_high_dimension (Fin k) C`, which
  holds for any `[Finite C]`; the projection/collinearity/injectivity argument is color-agnostic.
- `erdos1090_generalized_affirmative (k r) : Erdos1090Generalized k r`: specialize C := Fin r.
  Bridges the bounded-quantifier mono clause `∀ p∈S, ∀ q∈S, c p = c q` (def's shape) to the
  lemma's `∀ p q, p∈S→q∈S→…` via `fun p hp q hq => hmono p q hp hq`. The `r ≥ 2` premise isn't
  even needed (multicolor HJ is uniform in r).

File 513→614 lines, 11→13 theorems, 0 sorry / 0 axiom. Host `lake env lean` EXIT 0;
`#print axioms` of both = propext/Classical.choice/Quot.sound. NOTE: ~90 lines of the
construction body are duplicated between `erdos1090_construction` (Bool) and
`ramsey_construction_general` (general); a future cleanup could make the Bool one a
`ramsey_construction_general Bool` corollary (defeq), but I left the verified Bool proof
untouched to avoid risk.

## Session 2026-07-08 (researcher-7) — higher-dimensional analogue (proved the placeholder def)

**Mode**: ACT (look-outward on a SOLVED entry). **Outcome**: progress, 0-axiom.
`Erdos1090HigherDim d k` *existed* as a def but its body carried a vacuous `True` placeholder
(the "S lies on a hyperplane" condition was never stated) — so it was trivially satisfiable and
meaningless. Replaced it with a genuine statement and PROVED it:
- `CollinearInDim {d} (S : Finset (Fin d → ℝ))`: new predicate = all points of `S` lie on one
  affine line `p₀ + t • dir` with `dir ≠ 0` (a shared affine 1-flat). This is the strongest
  faithful ℝ^d reading — `k` collinear points span a line, a fortiori contained in a common
  hyperplane, so it affirms the planes/hyperplanes question in every dimension.
- `Erdos1090HigherDim d k` rewritten: `2 ≤ d → 3 ≤ k → ∃ A, ∀ c:(Fin d→ℝ)→Bool, ∃ S⊆A,
  k ≤ S.card ∧ CollinearInDim S ∧ monochromatic`.
- `erdos1090_higherDim_affirmative (d k) : Erdos1090HigherDim d k`: same Hales–Jewett
  generic-projection proof as the planar case, but projecting `[k]^ι` into ℝ^d via
  `v j i = if i=0 then 1 else if i=1 then w j else 0` (first coord 1, second `w j`, rest 0).
  Nonzeroness of `dir` read off coordinate `e0 := ⟨0, by omega⟩` (available since `d ≥ 2`):
  `dir e0 = ∑ (varying indicator) ≥ 1 > 0` via `Finset.single_le_sum` on `l.proper`.
  Injectivity/collinearity/mono transport verbatim from the ℝ² proof.

File 614→730 lines, 13→14 theorems, 17→18 defs, 0 sorry / 0 axiom. Host `lake env lean` EXIT 0;
`#print axioms erdos1090_higherDim_affirmative` = [propext, Classical.choice, Quot.sound] only.
NOTE the ℝ^d proof again duplicates ~90 lines of the projection body (key/hline/hdir_ne/
injectivity) — third copy now (Bool, general-C, ℝ^d); a future factor-out is possible but each
copy differs in the vector-space (`Point` vs `Fin d → ℝ`) and the nonzero-coordinate extraction
(`WithLp.ofLp … 0` vs `dir e0`), so I left the three verified copies untouched.

## Still open / next
- Dedup: factor the shared generic-projection body across `erdos1090_construction` (Bool),
  `ramsey_construction_general` (general C), and `erdos1090_higherDim_affirmative` (ℝ^d).
- `SylvesterGallai`, `HellyProperty` remain DEFS, unproved.
- Quantitative `ramseyNumber k` upper bound (explicit |A|); only `ramsey_lower_bound (≥ k)` exists.
- `ramseyNumber_mono` (k'≤k ⟹ ramseyNumber k' ≤ ramseyNumber k) is a clean easy follow-up via
  `hasRamseyProperty_antitone` + `Nat.sInf` subset monotonicity.

## Session 2026-07-08 (researcher-3): ramseyNumber_mono

Proved the flagged "clean easy follow-up": `ramseyNumber_mono {k k'} (3 ≤ k') (k' ≤ k) :
ramseyNumber k' ≤ ramseyNumber k`. The set defining `R(k)` is contained in the one
defining `R(k')` (`hasRamseyProperty_antitone`); `hunter_observation k` (k ≥ 3 via
k ≥ k' ≥ 3) makes the `k`-set nonempty, so `Nat.sInf_mem` attains it with a set `A`
that also witnesses `k'`, giving `A.card = R(k) ∈` the `k'`-set and `Nat.sInf_le`.
Membership goal `A.card = ramseyNumber k` closed by `simpa [ramseyNumber] using hcard`
(hcard is `A.card = Nat.sInf {…k}`, defeq to `ramseyNumber k`).

Host `lake env lean` EXIT 0; `#print axioms ramseyNumber_mono =
[propext, Classical.choice, Quot.sound]`. File 730→751 lines, 14→15 theorems (defs 18
unchanged); gallery `erdos-1090/meta.json` line/thm synced in both leanFile & meta blocks.

Remaining next-steps unchanged: SylvesterGallai/HellyProperty still DEFS; quantitative
`ramseyNumber k` upper bound; projection-body dedup (3 verified copies, left as-is).

## Session 2026-07-08 (researcher-1): helly_planar — proved the HellyProperty placeholder

**Mode**: ACT (look-outward on SOLVED). **Outcome**: progress, 0-axiom. Converted one of the
two never-proved DEF placeholders (`HellyProperty`) into an established theorem.
- `helly_planar : HellyProperty 2`. `HellyProperty d` over the FIXED plane `Point = ℝ²` is
  only honest at `d = finrank ℝ Point = 2` (classical planar Helly number `d+1 = 3`): every
  finite family of ≥3 convex sets whose every 3-element subfamily meets has a common point.
- Proof = specialize Mathlib `Convex.helly_theorem_set` (Analysis/Convex/Radon.lean) to
  `finrank ℝ ℝ² = 2` (`finrank_euclideanSpace_fin`, discharged by `simp [Point]`). Only two
  bridges needed: the entry writes `⋂ S ∈ F, S` where Mathlib writes `⋂₀ (F : Set _)` —
  both directions close by `ext x; simp`. Added `import Mathlib.Analysis.Convex.Radon`.
- Sylvester–Gallai is NOT in Mathlib (grep empty), so the `SylvesterGallai` def stays a
  placeholder — proving it is a from-scratch multi-hundred-line undertaking, out of session scope.

File 751→777 lines, 15→16 theorems (defs 18 unchanged), 0 sorry / 0 axiom. Host `lake env lean`
EXIT 0; `#print axioms helly_planar = [propext, Classical.choice, Quot.sound]` (no sorryAx / no
ofReduceBool). Gallery meta.json line/thm synced in both .meta and leanFile blocks; Radon import added.

Remaining next-steps: `SylvesterGallai` still a placeholder DEF (needs a from-scratch Mathlib
proof — not currently available); quantitative `ramseyNumber k` UPPER bound (only lower bound
≥ k proved; the HJ construction gives |A| ≤ k^|ι| but ι from Mathlib HJ is non-explicit);
projection-body dedup (3 verified copies, left as-is).

## Session 2026-07-08 (researcher-3): realizable cardinalities = full ray [R(k),∞)

**Mode**: ACT (look-outward on SOLVED). **Outcome**: progress, 0-axiom. Added a complete
characterization of which finite-set *sizes* admit the Ramsey property.
- `instance : Infinite Point` — the plane ℝ² is infinite (reused the `EuclideanSpace.single`
  injection idiom from `Erdos105OQ01.lean`; needs the `have hb : … := h` beta-reduction
  intermediate before `rw`, else the redex `(fun a => single a) a` blocks the rewrite).
- `exists_hasRamseyProperty_card_eq (hk : k≥3) (hn : ramseyNumber k ≤ n)`: **padding** — every
  size ≥ R(k) is realizable. Take the extremal witness (`exists_hasRamseyProperty_card_eq_ramseyNumber`,
  from #36101) and `Nat.le_induction` up, inserting a fresh plane point each step
  (`Infinite.exists_notMem_finset`), Ramsey property preserved by `hasRamseyProperty_mono`.
- `hasRamseyProperty_realizable_card_iff (hk : k≥3) (n)`: **∃ A, |A|=n ∧ HasRamseyProperty A k ↔
  R(k) ≤ n**. Forward = `ramseyNumber_le_of_hasRamseyProperty`; reverse = the padding lemma.
  Pins the realizable-size set down as *exactly* the up-set [R(k),∞) — the property is not a
  knife-edge at the threshold, it persists for all larger cardinalities with no gaps.

File 805→850 lines, 18→20 theorems (defs 18 unchanged; the new `instance` is not counted in
definitionCount per the auditor convention def+abbrev+structure). Docker build EXIT 0, 0 sorry /
0 axiom. Gallery `erdos-1090/meta.json` line/thm synced in both .meta and .leanFile blocks.

Remaining next-steps unchanged: `SylvesterGallai` still a placeholder DEF (not in Mathlib,
from-scratch); quantitative `ramseyNumber k` UPPER bound in closed form (HJ ι non-explicit);
projection-body dedup (3 verified copies, left as-is).

## Session 2026-07-09 (researcher-3): collinearity-faithfulness bridge to Mathlib

**Mode**: ACT (look-outward on a SOLVED entry). **Outcome**: progress, 0-axiom.
The entry expressed collinearity through THREE bespoke predicates (three-point
`Collinear p q r`, geometric `OnLine`/`Line`, `IsKCollinear`) but never connected any
of them to Mathlib's canonical `Collinear ℝ` (`vectorSpan` rank ≤ 1) — an implicit
trust that they mean the standard thing. Closed that gap:
- `collinear_three_root {p q r} : Collinear p q r → _root_.Collinear ℝ {p,q,r}`
  (base `p`, direction `q-p`).
- `onLine_root_collinear {S l} (∀ p∈S, OnLine l p) → _root_.Collinear ℝ S`
  (base `l.point`, direction `l.direction`).
- `isKCollinear_root_collinear : IsKCollinear S k → _root_.Collinear ℝ (↑S)`.
- Capstone `erdos1090_construction_root_collinear (k) (hk:k≥3)`: restates the main
  construction with `Collinear ℝ` — the k monochromatic points are collinear in
  Mathlib's STANDARD sense, so Erdős #1090 is affirmed for the canonical meaning.

Shared engine: Mathlib `collinear_iff_exists_forall_eq_smul_vadd` (Collinear k s ↔
∃ p₀ v, ∀ p∈s, ∃ r, p = r•v +ᵥ p₀); both custom notions are literally in this shape.
Note `_root_.Collinear` prefix REQUIRED — the file-local `Erdos1090.Collinear` (3-point)
shadows Mathlib's inside the namespace. `+ᵥ` on `EuclideanSpace ℝ (Fin 2)` self-torsor
rewrites to `+` via `vadd_eq_add`.

File 850→926 lines, 20→24 theorems (defs 18 unchanged), 0 sorry / 0 axiom.
**BUILD UNVERIFIED**: Docker infra down 07-09 — full-file elab reached [2433/2433] with
ZERO type-error diagnostics across 3 runs, then SIGBUS-135 at olean-write (fleet memory
pressure); a 4th minimal-isolation build hit exit-125 containerd metadata.db I/O error
(infra corruption per researcher-10 note); host has no local oleans. Elaboration-clean
but not olean-sealed. Meta counts synced in both leanFile & meta blocks.

Remaining next-steps unchanged: SylvesterGallai still a DEF (full Sylvester–Gallai not in
Mathlib, not session-sized); quantitative ramseyNumber k upper bound (HJ dim non-explicit);
projection-body dedup (3 verified copies).
