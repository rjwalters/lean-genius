/-
  The Three-Gap / Three-Distance (Steinhaus) Theorem — Formal Statement and Path
  (erdos-998-oq-04)

  ## Background

  Erdős Problem #998 (Kesten's equidistribution theorem) is built on the orbit
  structure of an irrational rotation `m ↦ {mα}` on the circle `[0,1)`.  The
  *three-distance theorem* (Steinhaus conjecture; proved by Sós, Surányi, and
  Świerczkowski) describes that orbit structure exactly:

    **For every irrational `α` and every `N ≥ 1`, the `N` points
    `{0, {α}, {2α}, …, {(N-1)α}}` cut the circle into `N` arcs whose lengths
    take at most THREE distinct values; moreover, when three values occur, the
    largest is the sum of the other two.**

  The parent file `Erdos998Problem.lean` only mentions this theorem in a prose
  docstring (Part V).  This file gives the first *formal Lean statement* of the
  theorem together with the elementary structural infrastructure, isolating the
  remaining combinatorial core.

  ## Mathlib status (June 2026)

  Mathlib4 does **not** contain the three-gap theorem.  A Coq formalization
  (van Ravenstein's proof) exists, but no Lean version.  The theorem is purely
  finite/order-theoretic — no measure theory or analysis is needed — so it is a
  natural Mathlib-style target built from `Int.fract`, `Finset`, and the linear
  order on `ℝ`.

  ## What is proved here vs. left open

  PROVED (elementary, robust):
    * `orbit_mem_Ico`     — every orbit point lies in `[0,1)`
    * `zero_mem_orbit`    — `0` is always an orbit point (the `i = 0` term)
    * `orbit_nonempty`    — the orbit is nonempty for `N ≥ 1`
    * `forwardGap_nonneg` — every forward gap length is `≥ 0`
    * `orbit_card`        — for irrational `α` the orbit has exactly `N` points
                            (injectivity of `i ↦ {iα}` via `Int.fract_eq_fract`
                            and `Irrational.int_mul`)
    * `fract_fract_sub_fract` — STEP A primitive: `{ {x} − {y} } = { x − y }`,
                            so the cyclic distance between two orbit points
                            depends only on their index difference (the engine
                            of STEP A in `exists_gap_triple`)

  PROVED (reductions — fully discharged modulo the isolated core):
    * `three_gap`         — at most three distinct gap lengths, reduced to
                            `exists_gap_triple` via `card_le_three_of_subset_triple`
    * `three_gap_additive`— the additive relation among the three lengths,
                            reduced to `exists_gap_triple` by pure `Finset` reasoning

  PROVED (the genuine content — the classification core, now CLOSED):
    * `exists_gap_triple` — the Sós–Surányi–Świerczkowski / van Ravenstein
                            classification, now fully discharged (no `sorry`).
                            The `N = 1` base case is the degenerate single-point
                            orbit; the `N ≥ 2` case pins the two Steinhaus
                            first-return generators as the minimal forward /
                            backward cyclic returns and the long gap as their sum
                            (`a + b = c` by construction), then shows every
                            forward gap length is one of the three.
    Supporting lemmas added for the `N ≥ 2` classification (all `sorry`-free,
    no axioms): `fract_add_of_lt_one`, `fract_add_of_one_le`, `fract_nat_add_lt`,
    `fract_nat_add_ge` (fractional-part carry / no-carry rules); `fract_neg_mul`
    (`{-iα} = 1 - {iα}` for irrational `α`, `i ≠ 0`); `forwardGap_ge` (the
    `Finset.le_inf'` lower-bound companion to `forwardGap_le`);
    `forwardGap_region_a / _b / _c` (the three regional gap values) and
    `forwardGap_mem_triple` (their assembly into membership in `{a, b, a+b}`).

  ## Status: COMPLETE — 0 `sorry`, 0 `axiom` (uses only `propext`,
  `Classical.choice`, `Quot.sound`).  The classification core was closed by
  Aristotle (Harmonic) proof search; project `f3b4620d-814e-430d-97a8-c40321b48abf`,
  which reports a clean `lake build` (8027 jobs) in its sandbox.

  BUILD VERIFICATION PENDING under this repo's pinned toolchain: Aristotle built
  the file under `leanprover/lean4:v4.28.0` (its vendored Mathlib), whereas this
  repo pins `v4.26.0`.  The proof uses only stable `Int.fract` / `Finset` API and
  is expected to compile unchanged, but it has NOT yet been kernel-checked here.
  A build-capable session must run
  `./proofs/scripts/docker-build.sh Proofs.Erdos998ThreeGapOQ04`
  before the gallery entry is flipped to `verified`.  Registered in `Proofs.lean`.
-/
import Mathlib

namespace Erdos998ThreeGap

open Finset

/-- The orbit of the rotation by `α` after `N` steps, viewed as a finite subset
    of `[0,1)`: the fractional parts `{0, {α}, {2α}, …, {(N-1)α}}`. -/
noncomputable def orbit (α : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image (fun (i : ℕ) => Int.fract ((i : ℝ) * α))

/-- Every orbit point lies in the half-open unit interval `[0,1)`. -/
theorem orbit_mem_Ico {α : ℝ} {N : ℕ} {x : ℝ} (hx : x ∈ orbit α N) :
    0 ≤ x ∧ x < 1 := by
  simp only [orbit, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- `0` is always an orbit point, contributed by the `i = 0` term. -/
theorem zero_mem_orbit (α : ℝ) {N : ℕ} (hN : 0 < N) : (0 : ℝ) ∈ orbit α N := by
  simp only [orbit, Finset.mem_image, Finset.mem_range]
  exact ⟨0, hN, by simp⟩

/-- The orbit is nonempty whenever `N ≥ 1`. -/
theorem orbit_nonempty (α : ℝ) {N : ℕ} (hN : 0 < N) : (orbit α N).Nonempty :=
  ⟨0, zero_mem_orbit α hN⟩

/-- The forward gap of an orbit point `x`: the shortest *positive cyclic*
    distance `{y - x}` from `x` to another orbit point `y`.  Cyclic distance is
    measured by `Int.fract (y - x) ∈ [0,1)`, so the minimum over `y ≠ x` is the
    length of the arc immediately clockwise-to-counterclockwise of `x`.  Defined
    totally via `dite`; the junk value `0` is only hit on the (excluded) empty
    case `N ≤ 1`. -/
noncomputable def forwardGap (α : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if h : ((orbit α N).erase x).Nonempty then
    ((orbit α N).erase x).inf' h (fun y => Int.fract (y - x))
  else 0

/-- The finite set of distinct gap lengths produced by the `N`-point orbit. -/
noncomputable def gapLengths (α : ℝ) (N : ℕ) : Finset ℝ :=
  (orbit α N).image (forwardGap α N)

/-- Every forward gap length is nonnegative (each cyclic distance `{y - x}` is
    `≥ 0`, and so is their minimum; the junk branch is `0`). -/
theorem forwardGap_nonneg (α : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ forwardGap α N x := by
  unfold forwardGap
  split
  · rename_i h
    exact Finset.le_inf' h _ (fun y _ => Int.fract_nonneg _)
  · exact le_refl 0

/-- For irrational `α`, distinct indices give distinct orbit points: the map
    `i ↦ {iα}` is injective.  If `{iα} = {jα}` then `Int.fract_eq_fract` yields a
    `z : ℤ` with `iα - jα = z`, i.e. `(i - j)·α = z`; for `i ≠ j` the coefficient
    `(i - j : ℤ)` is nonzero, so `(i - j)·α` is irrational
    (`Irrational.intCast_mul`) while also equal to the integer `z` — contradiction
    via `Int.not_irrational`.  This is the injectivity engine behind both
    `orbit_card` and the candidate-membership step of `forwardGap_le`. -/
theorem fract_mul_inj {α : ℝ} (hα : Irrational α) {i j : ℕ} (hne : i ≠ j) :
    Int.fract ((i : ℝ) * α) ≠ Int.fract ((j : ℝ) * α) := by
  intro hij
  rw [Int.fract_eq_fract] at hij
  obtain ⟨z, hz⟩ := hij
  have hm : ((i : ℤ) - (j : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have key : (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * α = (z : ℝ) := by
    push_cast
    rw [sub_mul]
    exact hz
  have hirr : Irrational ((((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * α) := hα.intCast_mul hm
  rw [key] at hirr
  exact (Int.not_irrational z) hirr

/-- For irrational `α` the map `i ↦ {iα}` is injective on `ℕ`, hence the orbit
    has exactly `N` distinct points.  Injectivity is `fract_mul_inj`; cardinality
    then follows from `Finset.card_image_of_injOn` and `Finset.card_range`. -/
theorem orbit_card {α : ℝ} (hα : Irrational α) (N : ℕ) :
    (orbit α N).card = N := by
  have hinj : Set.InjOn (fun i : ℕ => Int.fract ((i : ℝ) * α)) ↑(Finset.range N) := by
    intro i _ j _ hij
    simp only at hij
    by_contra hne
    exact fract_mul_inj hα hne hij
  rw [orbit, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **STEP A primitive — cyclic distance depends only on the index difference.**
    For any two reals `x, y`, the fractional part of the difference of their
    fractional parts equals the fractional part of their difference:
        `{ {x} − {y} } = { x − y }`.
    Specialised to `x = jα`, `y = kα` this is exactly the identity
        `Int.fract (P_j − P_k) = Int.fract ((j − k)·α)`
    invoked in STEP A of the `exists_gap_triple` proof path: the cyclic distance
    between two orbit points depends only on their index difference, because
    `{x} − {y}` differs from `x − y` by the integer `⌊y⌋ − ⌊x⌋`, and `Int.fract`
    is invariant under integer shifts (`Int.fract_sub_intCast`).  This is the
    mechanical engine that lets the forward gap at `P_k` be rewritten as a
    minimum of `Int.fract ((j − k)·α)` over the remaining indices. -/
theorem fract_fract_sub_fract (x y : ℝ) :
    Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  have h : Int.fract x - Int.fract y = (x - y) - (((⌊x⌋ - ⌊y⌋ : ℤ)) : ℝ) := by
    simp only [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- **STEP A (upper-bound half) — now formalized.**  For irrational `α` and
    indices `j, k < N` with `j ≠ k`, the forward gap at the orbit point
    `P_k = {kα}` is bounded above by the cyclic distance `{(j - k)·α}` realised by
    the other orbit point `P_j = {jα}`:

      `forwardGap α N {kα} ≤ {(j - k)·α}`.

    This is the routine `Finset.inf'_le` direction of STEP A in the
    `exists_gap_triple` proof path: each index `j ≠ k` furnishes a candidate arc
    from `P_k` whose length is `{P_j − P_k} = {(j − k)·α}` (the latter equality is
    `fract_fract_sub_fract`), so the actual forward gap — an `inf'` over all such
    candidates — is at most each of them.  Membership of `P_j` in the erased orbit
    uses injectivity (`fract_mul_inj`).  The matching *lower* bound (that the gap
    equals the *minimal* index-difference distance) is the remaining STEP B–C
    content; this lemma discharges the easy half as checked Lean. -/
theorem forwardGap_le {α : ℝ} (hα : Irrational α) {N : ℕ}
    {j k : ℕ} (hj : j < N) (hne : j ≠ k) :
    forwardGap α N (Int.fract ((k : ℝ) * α)) ≤ Int.fract (((j : ℝ) - (k : ℝ)) * α) := by
  have hxj : Int.fract ((j : ℝ) * α) ∈ orbit α N := by
    simp only [orbit, Finset.mem_image, Finset.mem_range]; exact ⟨j, hj, rfl⟩
  have hjk : Int.fract ((j : ℝ) * α) ≠ Int.fract ((k : ℝ) * α) := fract_mul_inj hα hne
  have hmem : Int.fract ((j : ℝ) * α) ∈
      (orbit α N).erase (Int.fract ((k : ℝ) * α)) := Finset.mem_erase.mpr ⟨hjk, hxj⟩
  have hNe : ((orbit α N).erase (Int.fract ((k : ℝ) * α))).Nonempty := ⟨_, hmem⟩
  unfold forwardGap
  rw [dif_pos hNe]
  refine le_trans
    (Finset.inf'_le (f := fun y => Int.fract (y - Int.fract ((k : ℝ) * α))) hmem)
    (le_of_eq ?_)
  rw [fract_fract_sub_fract, sub_mul]

/-
    PROOF PATH for the core classification `exists_gap_triple`
    (van Ravenstein / Sós, elementary).  Session 6 (researcher-1, 2026-06-18)
    refines the session-5 prose into an EXPLICIT lemma decomposition: the
    monolithic `sorry` factors into three routine reductions (STEPS A–C, all
    provable from named Mathlib API) followed by ONE genuine Steinhaus crux
    (STEP D).  This is the turnkey scaffold for the next backend-up session.

    Notation: for `k ∈ [0,N)` write `P_k := {kα} = Int.fract (k·α)`; these are
    the orbit points (distinct, by `orbit_card`).  The two witnesses already
    fixed in the proof below are
        a := min_{1≤i<N} Int.fract ( i·α)      (best FORWARD  return; this file's first witness)
        b := min_{1≤i<N} Int.fract (-i·α)      (best BACKWARD return; this file's second witness)
    and `c := a + b` (so `a + b = c` holds by `rfl`).

    ── STEP A  (forwardGap as a fract-of-index-difference; ROUTINE).
       For `x = P_k`, every other orbit point is some `P_j` (j ≠ k, distinctness
       from `orbit_card`), and
          Int.fract (P_j − P_k) = Int.fract ((j − k)·α),
       because `P_j − P_k = (j−k)·α − (⌊jα⌋−⌊kα⌋)` differs from `(j−k)·α` by an
       integer, and `Int.fract` is invariant under integer shifts
       (`Int.fract_int_add` / `Int.fract_add_int`).  Hence
          forwardGap α N P_k = min_{j∈[0,N), j≠k} Int.fract ((j − k)·α).
       The per-pair identity `Int.fract (P_j − P_k) = Int.fract ((j − k)·α)` is
       now DISCHARGED as the named lemma `fract_fract_sub_fract` (above); what
       remains of STEP A is the routine `Finset.inf'_congr` transport of that
       identity across the erased orbit.
       Mathlib: `fract_fract_sub_fract`, `Finset.inf'_congr`.

    ── STEP B  (split the index difference into forward/backward; ROUTINE).
       Writing `d = j − k`, the index `d` ranges over `[−k, N−1−k] \ {0}`.
       Splitting on the sign of `d` (with `e := −d` on the negative side):
          forwardGap α N P_k = min ( F_k , B_k ),  where
            F_k := min_{d=1}^{N−1−k} Int.fract ( d·α)   (forward  returns still in range)
            B_k := min_{e=1}^{k}     Int.fract (−e·α)   (backward returns still in range)
       (`F_{N−1}` / `B_0` are over empty ranges — drop that side; the orbit has
       `N ≥ 2` points so at least one side is nonempty.)
       Mathlib: `Finset.inf'_union`, image of `Finset.range` under `(· + k)` /
       negation, `Int.fract` evaluation.

    ── STEP C  (subset-min bounds + extremal attainment; ROUTINE).
       `F_k` is a min over `{1,…,N−1−k} ⊆ {1,…,N−1}`, so `F_k ≥ a`; likewise
       `B_k ≥ b`.  At the extremes the full range is recovered: `F_0 = a` and
       `B_{N−1} = b`.  Therefore  `forwardGap α N P_k ≥ min a b`  for every `k`,
       and the two witnesses `a, b` are themselves ATTAINED gap lengths
       (`a = forwardGap α N P_0`'s forward part, `b` at `P_{N−1}`).
       Mathlib: `Finset.inf'_le`, `Finset.le_inf'`, `Finset.inf'_mem`,
       `Finset.exists_min_image`.

    ── STEP D  (the genuine Steinhaus crux — the SOLE remaining content).
       Let `p, q ∈ [1,N)` be the least indices attaining `a, b` respectively.
       Claim: `forwardGap α N P_k = min (F_k, B_k) ∈ {a, b, a+b}` for every `k`.
       The mechanism (van Ravenstein):
         • if `k + p < N`  then `p` lies in `F_k`'s range, so `F_k = a` and the
           forward neighbour of `P_k` is `P_{k+p}` (gap `a`);
         • if `k ≥ q`      then `q` lies in `B_k`'s range, so `B_k = b` and the
           backward-side neighbour gives gap `b`;
         • the `p + q − N` indices with `k + p ≥ N` AND `k < q` have NEITHER a
           pure forward-`p` nor backward-`q` neighbour available, and minimality
           of `p, q` forces their gap to be exactly the LONG value `a + b`.
       The crux is showing no orbit point lies strictly inside the candidate arc
       — i.e. that `min (F_k, B_k)` cannot be a value strictly between in
       `(min a b, a+b)`.  This is pure `Nat`/order arithmetic on the indices
       once STEPS A–C are in place; it needs NO new Mathlib infrastructure.

    STATUS OF THE FRONTIER: STEPS A–C are routine and provable manually or via
    a single per-lemma Aristotle `prove` call each; STEP D is the one HARD
    (known, not open) obligation.  Backends were BOTH down session 6
    (Aristotle MCP → 404 "Resource not found"; Docker gated at 15 build
    containers / ~5.7 GiB of 7.65 GiB, OOM-unsafe), so no Lean was shipped —
    only this decomposition.  When a backend recovers, submit STEP D (or the
    whole file) to Aristotle `prove_file`, with STEPS A–C as warm-up lemmas. -/
/-- A finite set covered by an explicit triple `{a, b, c}` has at most three
    elements.  Pure `Finset` cardinality arithmetic — the engine behind the
    `≤ 3` bound once the gap lengths are classified. -/
theorem card_le_three_of_subset_triple {s : Finset ℝ} {a b c : ℝ}
    (h : s ⊆ ({a, b, c} : Finset ℝ)) : s.card ≤ 3 := by
  have hc : ({a, b, c} : Finset ℝ).card ≤ 3 := by
    have h1 := Finset.card_insert_le a ({b, c} : Finset ℝ)
    have h2 := Finset.card_insert_le b ({c} : Finset ℝ)
    have h3 : ({c} : Finset ℝ).card = 1 := Finset.card_singleton c
    omega
  exact le_trans (Finset.card_le_card h) hc

/-! ### Infrastructure for the `N ≥ 2` three-gap classification -/

/-- General fract addition (no carry): if the fractional parts sum to `< 1`,
    the fractional part of the sum is their sum. -/
theorem fract_add_of_lt_one {x y : ℝ} (h : Int.fract x + Int.fract y < 1) :
    Int.fract (x + y) = Int.fract x + Int.fract y := by
  obtain ⟨z, hz⟩ := Int.fract_add x y
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_nonneg y
  have h2 := Int.fract_nonneg (x+y)
  have h3 := Int.fract_lt_one (x+y)
  have hzr : (z:ℝ) = Int.fract (x+y) - Int.fract x - Int.fract y := by linarith [hz]
  have ha : (-1:ℝ) < (z:ℝ) := by linarith
  have hb : (z:ℝ) < 1 := by linarith
  have ha' : (-1:ℤ) < z := by exact_mod_cast ha
  have hb' : z < (1:ℤ) := by exact_mod_cast hb
  have hz0 : z = 0 := by omega
  rw [hz0] at hzr; push_cast at hzr; linarith

/-- General fract addition (with carry): if the fractional parts sum to `≥ 1`,
    the fractional part of the sum is their sum minus one. -/
theorem fract_add_of_one_le {x y : ℝ} (h : 1 ≤ Int.fract x + Int.fract y) :
    Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by
  obtain ⟨z, hz⟩ := Int.fract_add x y
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_nonneg y
  have h2 := Int.fract_nonneg (x+y)
  have h3 := Int.fract_lt_one (x+y)
  have h4 := Int.fract_lt_one x
  have h5 := Int.fract_lt_one y
  have hzr : (z:ℝ) = Int.fract (x+y) - Int.fract x - Int.fract y := by linarith [hz]
  have ha : (-2:ℝ) < (z:ℝ) := by linarith
  have hb : (z:ℝ) < 0 := by linarith
  have ha' : (-2:ℤ) < z := by exact_mod_cast ha
  have hb' : z < (0:ℤ) := by exact_mod_cast hb
  have hz0 : z = -1 := by omega
  rw [hz0] at hzr; push_cast at hzr; linarith

/-- Nat-indexed version of `fract_add_of_lt_one`. -/
theorem fract_nat_add_lt {α : ℝ} {m n : ℕ}
    (h : Int.fract ((m:ℝ)*α) + Int.fract ((n:ℝ)*α) < 1) :
    Int.fract (((m+n : ℕ):ℝ)*α) = Int.fract ((m:ℝ)*α) + Int.fract ((n:ℝ)*α) := by
  have hc : ((m+n:ℕ):ℝ)*α = (m:ℝ)*α + (n:ℝ)*α := by push_cast; ring
  rw [hc, fract_add_of_lt_one h]

/-- Nat-indexed version of `fract_add_of_one_le`. -/
theorem fract_nat_add_ge {α : ℝ} {m n : ℕ}
    (h : 1 ≤ Int.fract ((m:ℝ)*α) + Int.fract ((n:ℝ)*α)) :
    Int.fract (((m+n : ℕ):ℝ)*α) = Int.fract ((m:ℝ)*α) + Int.fract ((n:ℝ)*α) - 1 := by
  have hc : ((m+n:ℕ):ℝ)*α = (m:ℝ)*α + (n:ℝ)*α := by push_cast; ring
  rw [hc, fract_add_of_one_le h]

/-- For irrational `α` and `i ≠ 0`, `{-iα} = 1 - {iα}` (since `{iα} ≠ 0`). -/
theorem fract_neg_mul {α : ℝ} (hα : Irrational α) {i : ℕ} (hi : i ≠ 0) :
    Int.fract (-((i:ℝ) * α)) = 1 - Int.fract ((i:ℝ) * α) := by
  apply Int.fract_neg
  have := fract_mul_inj hα hi
  simpa using this

/-- **Lower bound for the forward gap.**  If a real `L` bounds every cyclic
    index-difference distance `{(j-k)·α}` (for `j < N`, `j ≠ k`) from below,
    then `L` bounds the forward gap at `P_k` from below.  This is the
    `Finset.le_inf'` companion to `forwardGap_le`. -/
theorem forwardGap_ge {α : ℝ} (hα : Irrational α) {N : ℕ} (hN2 : 2 ≤ N) {k : ℕ}
    (hk : k < N) (L : ℝ)
    (hL : ∀ j, j < N → j ≠ k → L ≤ Int.fract (((j : ℝ) - (k : ℝ)) * α)) :
    L ≤ forwardGap α N (Int.fract ((k : ℝ) * α)) := by
  unfold forwardGap
  have hNe : ((orbit α N).erase (Int.fract ((k:ℝ)*α))).Nonempty := by
    obtain ⟨i, hiN, hik⟩ : ∃ i, i < N ∧ i ≠ k := by
      rcases eq_or_ne k 0 with rfl | hk0
      · exact ⟨1, by omega, one_ne_zero⟩
      · exact ⟨0, by omega, Ne.symm hk0⟩
    refine ⟨Int.fract ((i:ℝ)*α), Finset.mem_erase.mpr ⟨fract_mul_inj hα hik, ?_⟩⟩
    simp only [orbit, Finset.mem_image, Finset.mem_range]; exact ⟨i, hiN, rfl⟩
  rw [dif_pos hNe]
  apply Finset.le_inf'
  intro y hy
  rw [Finset.mem_erase, orbit, Finset.mem_image] at hy
  obtain ⟨hyne, j, hjr, rfl⟩ := hy
  rw [Finset.mem_range] at hjr
  have hjk : j ≠ k := by intro h; subst h; exact hyne rfl
  have hh : Int.fract (Int.fract ((j:ℝ)*α) - Int.fract ((k:ℝ)*α))
      = Int.fract (((j:ℝ)-(k:ℝ))*α) := by
    rw [fract_fract_sub_fract, sub_mul]
  rw [hh]; exact hL j hjr hjk

/-- **Region `a`.**  When the forward step `p` keeps the index inside the orbit
    (`k + p < N`), the forward gap at `P_k` is exactly the short forward gap `a`. -/
theorem forwardGap_region_a {α : ℝ} (hα : Irrational α) {N : ℕ} (hN2 : 2 ≤ N)
    (a : ℝ) (p : ℕ)
    (hp1 : 1 ≤ p) (hpa : Int.fract ((p:ℝ) * α) = a)
    (hamin : ∀ i, 1 ≤ i → i < N → a ≤ Int.fract ((i:ℝ) * α))
    {k : ℕ} (hk : k < N) (hreg : k + p < N) :
    forwardGap α N (Int.fract ((k:ℝ) * α)) = a := by
  -- The backward-direction trick: every backward return `{-eα}` with `e + p < N`
  -- is at least `a`, else `{(e+p)α} < a` contradicts minimality of `a`.
  have htrick : ∀ e, 1 ≤ e → e + p < N → a ≤ Int.fract (-((e:ℝ) * α)) := by
    intro e he1 hep
    by_contra hlt
    push_neg at hlt
    rw [fract_neg_mul hα (by omega)] at hlt
    have hsum : 1 ≤ Int.fract ((e:ℝ) * α) + Int.fract ((p:ℝ) * α) := by
      rw [hpa]; linarith
    have hcol := fract_nat_add_ge (α := α) (m := e) (n := p) hsum
    have hbound := hamin (e + p) (by omega) hep
    rw [hcol, hpa] at hbound
    have hlt1 := Int.fract_lt_one ((e:ℝ) * α)
    linarith
  refine le_antisymm ?_ ?_
  · -- Upper bound: the orbit point `P_{k+p}` realises gap `a`.
    have hle := forwardGap_le hα (j := k + p) (k := k) (by omega) (by omega)
    have harg : ((k + p : ℕ) : ℝ) - (k : ℝ) = (p : ℝ) := by push_cast; ring
    rw [harg, hpa] at hle
    exact hle
  · -- Lower bound: no orbit point lies closer than `a`.
    apply forwardGap_ge hα hN2 hk
    intro j hj hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · -- `j < k`: backward return, use the trick.
      have hee : ((j : ℝ) - (k : ℝ)) * α = -(((k - j : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hlt)]; ring
      rw [hee]
      exact htrick (k - j) (by omega) (by omega)
    · -- `j > k`: forward return, use minimality of `a`.
      have hee : ((j : ℝ) - (k : ℝ)) * α = (((j - k : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hgt)]
      rw [hee]
      exact hamin (j - k) (by omega) (by omega)

/-- **Region `b`.**  When the backward step `q` keeps the index inside the orbit
    (`q ≤ k`), the forward gap at `P_k` is exactly the short backward gap `b`. -/
theorem forwardGap_region_b {α : ℝ} (hα : Irrational α) {N : ℕ} (hN2 : 2 ≤ N)
    (b : ℝ) (q : ℕ)
    (hq1 : 1 ≤ q) (hqb : Int.fract (-((q:ℝ) * α)) = b)
    (hbmin : ∀ i, 1 ≤ i → i < N → b ≤ Int.fract (-((i:ℝ) * α)))
    {k : ℕ} (hk : k < N) (hreg : q ≤ k) :
    forwardGap α N (Int.fract ((k:ℝ) * α)) = b := by
  -- `b = 1 - {qα}`.
  have hbval : b = 1 - Int.fract ((q:ℝ) * α) := by
    rw [← hqb, fract_neg_mul hα (by omega)]
  -- The forward-direction trick: every forward return `{dα}` with `d + q < N`
  -- is at least `b`, else `{-(d+q)α} < b` contradicts minimality of `b`.
  have htrick : ∀ d, 1 ≤ d → d + q < N → b ≤ Int.fract ((d:ℝ) * α) := by
    intro d hd1 hdq
    by_contra hlt
    push_neg at hlt
    have hsum : Int.fract ((d:ℝ) * α) + Int.fract ((q:ℝ) * α) < 1 := by
      rw [hbval] at hlt; linarith
    have hcol := fract_nat_add_lt (α := α) (m := d) (n := q) hsum
    have hbound := hbmin (d + q) (by omega) hdq
    rw [fract_neg_mul hα (by omega), hcol] at hbound
    rw [hbval] at hbound
    have hdpos : 0 < Int.fract ((d:ℝ) * α) := by
      have hne0 : Int.fract ((d:ℝ) * α) ≠ 0 := by
        have := fract_mul_inj hα (i := d) (j := 0) (by omega)
        simpa using this
      exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne0)
    linarith
  refine le_antisymm ?_ ?_
  · -- Upper bound: the orbit point `P_{k-q}` realises gap `b`.
    have hkq_lt : k - q < k := Nat.sub_lt (by omega) (by omega)
    have hle := forwardGap_le hα (N := N) (j := k - q) (k := k) (by omega) (by omega)
    have harg : ((k - q : ℕ) : ℝ) - (k : ℝ) = -((q : ℝ)) := by
      rw [Nat.cast_sub hreg]; ring
    rw [harg, show ((-(q:ℝ)) * α) = -((q:ℝ) * α) by ring, hqb] at hle
    exact hle
  · -- Lower bound: no orbit point lies closer than `b`.
    apply forwardGap_ge hα hN2 hk
    intro j hj hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · -- `j < k`: backward return, use minimality of `b`.
      have hee : ((j : ℝ) - (k : ℝ)) * α = -(((k - j : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hlt)]; ring
      rw [hee]
      exact hbmin (k - j) (by omega) (by omega)
    · -- `j > k`: forward return, use the trick.
      have hee : ((j : ℝ) - (k : ℝ)) * α = (((j - k : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hgt)]
      rw [hee]
      exact htrick (j - k) (by omega) (by omega)

/-- **Region `a + b`.**  When neither `p` (forward) nor `q` (backward) keeps the
    index inside the orbit (`N ≤ k + p` and `k < q`), the forward gap at `P_k`
    is exactly the long gap `a + b`. -/
theorem forwardGap_region_c {α : ℝ} (hα : Irrational α) {N : ℕ} (hN2 : 2 ≤ N)
    (a b : ℝ) (p q : ℕ)
    (hpN : p < N) (hpa : Int.fract ((p:ℝ) * α) = a)
    (hamin : ∀ i, 1 ≤ i → i < N → a ≤ Int.fract ((i:ℝ) * α))
    (hq1 : 1 ≤ q) (hqN : q < N) (hqb : Int.fract (-((q:ℝ) * α)) = b)
    (hbmin : ∀ i, 1 ≤ i → i < N → b ≤ Int.fract (-((i:ℝ) * α)))
    {k : ℕ} (hk : k < N) (hreg1 : N ≤ k + p) (hreg2 : k < q) :
    forwardGap α N (Int.fract ((k:ℝ) * α)) = a + b := by
  -- Basic facts about `a`, `b` and the max property of index `q`.
  have ha0 : 0 ≤ a := by rw [← hpa]; exact Int.fract_nonneg _
  have hb0 : 0 ≤ b := by rw [← hqb]; exact Int.fract_nonneg _
  have hbval : b = 1 - Int.fract ((q:ℝ) * α) := by
    rw [← hqb, fract_neg_mul hα (by omega)]
  have hqmax : ∀ i, 1 ≤ i → i < N → Int.fract ((i:ℝ) * α) ≤ Int.fract ((q:ℝ) * α) := by
    intro i hi1 hiN
    have := hbmin i hi1 hiN
    rw [fract_neg_mul hα (by omega), hbval] at this
    linarith
  -- `a < {qα}` (min strictly below max) and hence `a + b < 1`.
  have halt : a < Int.fract ((q:ℝ) * α) :=
    lt_of_le_of_ne (hamin q hq1 hqN)
      (by rw [← hpa]; exact fract_mul_inj hα (by
        -- `p ≠ q`: else min = max forces all returns equal, contradicting injectivity.
        intro h
        have hN3 : 3 ≤ N := by omega
        have hqa : Int.fract ((q:ℝ) * α) = a := by rw [← h]; exact hpa
        have e1 : Int.fract (((1:ℕ):ℝ) * α) = a :=
          le_antisymm (le_trans (hqmax 1 (by norm_num) (by omega)) (le_of_eq hqa))
            (hamin 1 (by norm_num) (by omega))
        have e2 : Int.fract (((2:ℕ):ℝ) * α) = a :=
          le_antisymm (le_trans (hqmax 2 (by norm_num) (by omega)) (le_of_eq hqa))
            (hamin 2 (by norm_num) (by omega))
        exact fract_mul_inj hα (i := 1) (j := 2) (by norm_num) (e1.trans e2.symm)))
  have hpq : p ≠ q := by
    intro h; rw [← hpa, h] at halt; exact lt_irrefl _ halt
  have hab_lt : a + b < 1 := by rw [hbval]; linarith
  have hfab : Int.fract (a + b) = a + b := Int.fract_eq_self.mpr ⟨by linarith, hab_lt⟩
  have hqfract : Int.fract ((q:ℝ) * α) = 1 - b := by rw [hbval]; ring
  -- Forward index-difference distances (`d < p`) are at least `a + b`.
  have hfwd : ∀ d, 1 ≤ d → d < p → a + b ≤ Int.fract ((d:ℝ) * α) := by
    intro d hd1 hdp
    have hda : a ≤ Int.fract ((d:ℝ) * α) := hamin d hd1 (by omega)
    have hdlt1 : Int.fract ((d:ℝ) * α) < 1 := Int.fract_lt_one _
    have hkey : Int.fract ((d:ℝ) * α) - a = Int.fract (-(((p - d : ℕ):ℝ) * α)) := by
      have h1 := fract_fract_sub_fract ((d:ℝ) * α) ((p:ℝ) * α)
      rw [← sub_mul, hpa] at h1
      have h2 : Int.fract (Int.fract ((d:ℝ) * α) - a) = Int.fract ((d:ℝ) * α) - a :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have h3 : ((d:ℝ) - (p:ℝ)) * α = -(((p - d : ℕ):ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hdp)]; ring
      rw [h2] at h1; rw [h3] at h1; exact h1
    have hb_le := hbmin (p - d) (by omega) (by omega)
    rw [← hkey] at hb_le; linarith
  -- Backward index-difference distances (`e < q`) are at least `a + b`.
  have hbwd : ∀ e, 1 ≤ e → e < q → a + b ≤ Int.fract (-((e:ℝ) * α)) := by
    intro e he1 heq
    have hve : Int.fract (-((e:ℝ) * α)) = 1 - Int.fract ((e:ℝ) * α) := fract_neg_mul hα (by omega)
    have hue_le : Int.fract ((e:ℝ) * α) ≤ Int.fract ((q:ℝ) * α) := hqmax e he1 (by omega)
    have hkey : Int.fract ((q:ℝ) * α) - Int.fract ((e:ℝ) * α) = Int.fract (((q - e : ℕ):ℝ) * α) := by
      have h1 := fract_fract_sub_fract ((q:ℝ) * α) ((e:ℝ) * α)
      rw [← sub_mul] at h1
      have h2 : Int.fract (Int.fract ((q:ℝ) * α) - Int.fract ((e:ℝ) * α))
          = Int.fract ((q:ℝ) * α) - Int.fract ((e:ℝ) * α) :=
        Int.fract_eq_self.mpr ⟨by linarith,
          by linarith [Int.fract_nonneg ((e:ℝ) * α), Int.fract_lt_one ((q:ℝ) * α)]⟩
      have h3 : ((q:ℝ) - (e:ℝ)) * α = (((q - e : ℕ):ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt heq)]
      rw [h2] at h1; rw [h3] at h1; exact h1
    have ha_le := hamin (q - e) (by omega) (by omega)
    rw [← hkey] at ha_le
    rw [hve, hbval]; linarith
  refine le_antisymm ?_ ?_
  · -- Upper bound: the orbit point `P_{k+p-q}` realises gap `a + b`.
    have hle := forwardGap_le hα (N := N) (j := k + p - q) (k := k) (by omega) (by omega)
    have harg : ((k + p - q : ℕ):ℝ) - (k:ℝ) = (p:ℝ) - (q:ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add]; ring
    rw [harg] at hle
    have hval : Int.fract (((p:ℝ) - (q:ℝ)) * α) = a + b := by
      have h1 := fract_fract_sub_fract ((p:ℝ) * α) ((q:ℝ) * α)
      rw [← sub_mul, hpa, hqfract] at h1
      have e : a - (1 - b) = (a + b) - ((1:ℤ):ℝ) := by push_cast; ring
      rw [e, Int.fract_sub_intCast, hfab] at h1
      exact h1.symm
    rw [hval] at hle; exact hle
  · -- Lower bound: no orbit point lies closer than `a + b`.
    apply forwardGap_ge hα hN2 hk
    intro j hj hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · -- `j < k`: backward return.
      have hee : ((j : ℝ) - (k : ℝ)) * α = -(((k - j : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hlt)]; ring
      rw [hee]; exact hbwd (k - j) (by omega) (by omega)
    · -- `j > k`: forward return.
      have hee : ((j : ℝ) - (k : ℝ)) * α = (((j - k : ℕ) : ℝ) * α) := by
        rw [Nat.cast_sub (le_of_lt hgt)]
      rw [hee]; exact hfwd (j - k) (by omega) (by omega)

/-- **Core classification.**  For every orbit index `k < N`, the forward gap at
    `P_k` is one of the three values `a`, `b`, `a + b`. -/
theorem forwardGap_mem_triple {α : ℝ} (hα : Irrational α) {N : ℕ} (hN2 : 2 ≤ N)
    (a b : ℝ) (p q : ℕ)
    (hp1 : 1 ≤ p) (hpN : p < N) (hpa : Int.fract ((p:ℝ) * α) = a)
    (hamin : ∀ i, 1 ≤ i → i < N → a ≤ Int.fract ((i:ℝ) * α))
    (hq1 : 1 ≤ q) (hqN : q < N) (hqb : Int.fract (-((q:ℝ) * α)) = b)
    (hbmin : ∀ i, 1 ≤ i → i < N → b ≤ Int.fract (-((i:ℝ) * α)))
    {k : ℕ} (hk : k < N) :
    forwardGap α N (Int.fract ((k:ℝ) * α)) ∈ ({a, b, a + b} : Finset ℝ) := by
  by_cases hka : k + p < N
  · rw [forwardGap_region_a hα hN2 a p hp1 hpa hamin hk hka]
    simp
  · by_cases hkb : q ≤ k
    · rw [forwardGap_region_b hα hN2 b q hq1 hqb hbmin hk hkb]
      simp
    · push_neg at hka hkb
      rw [forwardGap_region_c hα hN2 a b p q hpN hpa hamin hq1 hqN hqb hbmin hk hka hkb]
      simp

/-- **Core combinatorial classification (Sós–Surányi–Świerczkowski /
    van Ravenstein).**  This is the genuine mathematical content of the
    three-gap theorem, isolated as a single statement.

    There exist three real values `a, b, c` — the two "short" gaps `{pα}` and
    `1 - {qα}` (where `p, q` are the Steinhaus first-return generators) and the
    "long" gap `{pα} + (1 - {qα})` — such that

      * every forward gap length is one of `a, b, c`  (the `⊆` part), and
      * the long gap is the sum of the two short gaps  (`a + b = c`).

    The `≤ 3` bound (`three_gap`) and the additive relation
    (`three_gap_additive`) both follow from this lemma by pure finite
    reasoning, so this is the sole remaining proof obligation.  The proof path
    is the classification in step 2 of the docstring below: walk the orbit in
    circular order and show each point's forward neighbour is reached by adding
    `p` or `q` to its index. -/
theorem exists_gap_triple (α : ℝ) (hα : Irrational α) {N : ℕ} (hN : 1 ≤ N) :
    ∃ a b c : ℝ, a + b = c ∧ gapLengths α N ⊆ ({a, b, c} : Finset ℝ) := by
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · -- `N = 1`: the orbit is the single point `{0}`; with no second point the lone
    -- gap length is the junk value `0`, so the degenerate triple `(0, 0, 0)`
    -- already covers `gapLengths`.  This base case is fully closed.
    obtain rfl : N = 1 := hN1.symm
    refine ⟨0, 0, 0, by ring, ?_⟩
    have horbit : orbit α 1 = {(0 : ℝ)} := by
      simp [orbit, Finset.range_one, Finset.image_singleton, Int.fract_zero]
    have hfg : forwardGap α 1 (0 : ℝ) = 0 := by
      unfold forwardGap
      rw [horbit, Finset.erase_singleton, dif_neg Finset.not_nonempty_empty]
    have hgap : gapLengths α 1 = {(0 : ℝ)} := by
      rw [gapLengths, horbit, Finset.image_singleton, hfg]
    rw [hgap]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp
  · -- `N ≥ 2`: name the two genuine "short" gaps as the minimal forward / backward
    -- cyclic returns `{iα}` / `{-iα}` over the nonzero indices `1 ≤ i < N`.  These
    -- are the Steinhaus first-return generators; their sum is the "long" gap, so
    -- the additive relation `a + b = c` holds by construction (`rfl`).  The single
    -- remaining obligation is the gap *classification* (Sós–Surányi–
    -- Świerczkowski / van Ravenstein): every forward gap length equals one of
    -- these three values.  See the proof-path comment above.
    have hS : ((Finset.range N).erase 0).Nonempty :=
      ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_range.mpr hN2⟩⟩
    refine ⟨(((Finset.range N).erase 0).image
              (fun (i : ℕ) => Int.fract ((i : ℝ) * α))).min'
              (hS.image (fun (i : ℕ) => Int.fract ((i : ℝ) * α))),
            (((Finset.range N).erase 0).image
              (fun (i : ℕ) => Int.fract (-((i : ℝ) * α)))).min'
              (hS.image (fun (i : ℕ) => Int.fract (-((i : ℝ) * α)))),
            _, rfl, ?_⟩
    -- Membership: each gap length is `forwardGap α N (P_k)` for some `k < N`,
    -- so the classification lemma `forwardGap_mem_triple` finishes.
    intro x hx
    rw [gapLengths, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [orbit, Finset.mem_image] at hy
    obtain ⟨k, hk_mem, rfl⟩ := hy
    rw [Finset.mem_range] at hk_mem
    -- Extract the forward generator `p` (attaining the minimal forward return `a`).
    have ha_mem := Finset.min'_mem
      (((Finset.range N).erase 0).image (fun (i : ℕ) => Int.fract ((i : ℝ) * α)))
      (hS.image (fun (i : ℕ) => Int.fract ((i : ℝ) * α)))
    rw [Finset.mem_image] at ha_mem
    obtain ⟨p, hp_mem, hp_eq⟩ := ha_mem
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hp_mem).1
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_erase.mp hp_mem).2
    have hamin : ∀ i, 1 ≤ i → i < N →
        (((Finset.range N).erase 0).image (fun (i : ℕ) => Int.fract ((i : ℝ) * α))).min'
          (hS.image (fun (i : ℕ) => Int.fract ((i : ℝ) * α))) ≤ Int.fract ((i : ℝ) * α) := by
      intro i hi1 hiN
      apply Finset.min'_le
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hiN⟩, rfl⟩
    -- Extract the backward generator `q` (attaining the minimal backward return `b`).
    have hb_mem := Finset.min'_mem
      (((Finset.range N).erase 0).image (fun (i : ℕ) => Int.fract (-((i : ℝ) * α))))
      (hS.image (fun (i : ℕ) => Int.fract (-((i : ℝ) * α))))
    rw [Finset.mem_image] at hb_mem
    obtain ⟨q, hq_mem, hq_eq⟩ := hb_mem
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Finset.mem_erase.mp hq_mem).1
    have hqN : q < N := Finset.mem_range.mp (Finset.mem_erase.mp hq_mem).2
    have hbmin : ∀ i, 1 ≤ i → i < N →
        (((Finset.range N).erase 0).image (fun (i : ℕ) => Int.fract (-((i : ℝ) * α)))).min'
          (hS.image (fun (i : ℕ) => Int.fract (-((i : ℝ) * α)))) ≤ Int.fract (-((i : ℝ) * α)) := by
      intro i hi1 hiN
      apply Finset.min'_le
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hiN⟩, rfl⟩
    exact forwardGap_mem_triple hα hN2 _ _ p q hp1 hpN hp_eq hamin hq1 hqN hq_eq hbmin hk_mem

/-- **The Three-Gap (Three-Distance / Steinhaus) Theorem.**

    For every irrational `α` and every `N ≥ 1`, the `N` arc lengths cut out of
    the circle by the orbit take at most three distinct values.  Reduced to the
    combinatorial classification `exists_gap_triple` via the cardinality engine
    `card_le_three_of_subset_triple`. -/
theorem three_gap (α : ℝ) (hα : Irrational α) {N : ℕ} (hN : 1 ≤ N) :
    (gapLengths α N).card ≤ 3 := by
  obtain ⟨a, b, c, _, hsub⟩ := exists_gap_triple α hα hN
  exact card_le_three_of_subset_triple hsub

/-- **Additive structure of the three gaps.**  When three distinct gap lengths
    occur, one of them is the sum of the other two (hence equal to the largest).
    This is immediate from the classification in `three_gap`: the long gap
    `{pα} + (1 - {qα})` is the sum of the two short gaps `{pα}` and `1 - {qα}`. -/
theorem three_gap_additive (α : ℝ) (hα : Irrational α) {N : ℕ} (hN : 1 ≤ N)
    (h3 : (gapLengths α N).card = 3) :
    ∃ a b c : ℝ, a ∈ gapLengths α N ∧ b ∈ gapLengths α N ∧ c ∈ gapLengths α N ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b = c := by
  obtain ⟨a, b, c, hsum, hsub⟩ := exists_gap_triple α hα hN
  -- The triple has card ≤ 3, and since `gapLengths` (card 3) sits inside it,
  -- equality of cardinalities forces `gapLengths = {a, b, c}`.
  have hcard3 : ({a, b, c} : Finset ℝ).card ≤ 3 := by
    have h1 := Finset.card_insert_le a ({b, c} : Finset ℝ)
    have h2 := Finset.card_insert_le b ({c} : Finset ℝ)
    have hs : ({c} : Finset ℝ).card = 1 := Finset.card_singleton c
    omega
  have heq : gapLengths α N = ({a, b, c} : Finset ℝ) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [h3]; exact hcard3)
  have htc : ({a, b, c} : Finset ℝ).card = 3 := by rw [← heq]; exact h3
  -- A three-element literal `{a, b, c}` forces the three entries pairwise
  -- distinct: collapsing any pair drops the cardinality to ≤ 2.
  -- A 2-element literal has card ≤ 2 (used to contradict `htc : card = 3`).
  have pair_le : ∀ x y : ℝ, ({x, y} : Finset ℝ).card ≤ 2 := by
    intro x y
    have hx := Finset.card_insert_le x ({y} : Finset ℝ)
    have hy : ({y} : Finset ℝ).card = 1 := Finset.card_singleton y
    omega
  have hab : a ≠ b := by
    intro he
    rw [he] at htc
    have hcol : ({b, b, c} : Finset ℝ) = ({b, c} : Finset ℝ) := by
      apply Finset.ext; intro x
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hcol] at htc
    have := pair_le b c; omega
  have hac : a ≠ c := by
    intro he
    rw [he] at htc
    have hcol : ({c, b, c} : Finset ℝ) = ({b, c} : Finset ℝ) := by
      apply Finset.ext; intro x
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hcol] at htc
    have := pair_le b c; omega
  have hbc : b ≠ c := by
    intro he
    rw [he] at htc
    have hcol : ({a, c, c} : Finset ℝ) = ({a, c} : Finset ℝ) := by
      apply Finset.ext; intro x
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hcol] at htc
    have := pair_le a c; omega
  refine ⟨a, b, c, ?_, ?_, ?_, hab, hac, hbc, hsum⟩
  · rw [heq]; simp
  · rw [heq]; simp
  · rw [heq]; simp

end Erdos998ThreeGap
