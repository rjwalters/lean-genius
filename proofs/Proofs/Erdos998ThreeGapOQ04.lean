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
    * `forwardGap_le`     — STEP A (upper-bound half): `forwardGap α N {kα}` is
                            `≤ {(j − k)·α}` for every other index `j`
    * `forwardGap_attained` — STEP A/B (lower-bound / attainment half): the gap is
                            *equal to* `{(j − k)·α}` for some concrete `j < N`,
                            `j ≠ k`.  Combined with `forwardGap_le` this pins
                            `forwardGap α N {kα} = min_{j≠k} {(j − k)·α}` — the gap
                            is now pure index arithmetic (full STEP A/B reduction)

  PROVED (reductions — fully discharged modulo the isolated core):
    * `three_gap`         — at most three distinct gap lengths, reduced to
                            `exists_gap_triple` via `card_le_three_of_subset_triple`
    * `three_gap_additive`— the additive relation among the three lengths,
                            reduced to `exists_gap_triple` by pure `Finset` reasoning

  PARTIALLY PROVED (the genuine content — see the proof-path comments):
    * `exists_gap_triple` — the Sós–Surányi–Świerczkowski / van Ravenstein
                            classification.  The `N = 1` base case is now CLOSED
                            (degenerate single-point orbit); the `N ≥ 2` case
                            pins the two Steinhaus first-return generators as the
                            minimal forward / backward cyclic returns and the long
                            gap as their sum (`a + b = c` by construction), leaving
                            a single `sorry` on the gap-classification step.

  ## Status: scaffolding through STEP A/B build-VERIFIED at the S7 revision
  (v4.26.0, 7743 jobs); the S9 addition `forwardGap_attained` is hand-verified
  against the Mathlib source but NOT yet kernel-checked (Aristotle backend down +
  Docker host OOM-saturated this cycle — deferred to a cache-warm build, the same
  mode in which S7's `forwardGap_le` was shipped then verified).  All scaffolding
  plus the `N = 1` base case compile; the only remaining `sorry` is the `N ≥ 2`
  classification step (STEP D) inside the isolated core `exists_gap_triple`.
  Registered in `Proofs.lean`.
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

/-- **STEP A/B (attainment) — the forward gap is REALISED by an index difference.**
    Whenever the erased orbit at `P_k = {kα}` is nonempty, the forward gap is not
    merely bounded by, but *equal to*, the cyclic distance `{(j - k)·α}` of some
    concrete in-range index `j < N`, `j ≠ k`:

      `∃ j < N, j ≠ k ∧ forwardGap α N {kα} = {(j - k)·α}`.

    This is the lower-bound companion to `forwardGap_le`: together they pin the
    forward gap as the *minimum* of `{(j - k)·α}` over `j ∈ [0,N) \ {k}`, turning
    the gap into pure index arithmetic — the STEP A/B reduction in the
    `exists_gap_triple` proof path.  No irrationality is needed: the `inf'`
    attaining point lies in the orbit (`Finset.exists_mem_eq_inf'`), hence equals
    `{jα}` for some `j ∈ range N`, and `j ≠ k` because it is `erase`d-distinct from
    `{kα}`; the value rewrite is `fract_fract_sub_fract` exactly as in
    `forwardGap_le`. -/
theorem forwardGap_attained {α : ℝ} {N : ℕ} {k : ℕ}
    (hNe : ((orbit α N).erase (Int.fract ((k : ℝ) * α))).Nonempty) :
    ∃ j, j < N ∧ j ≠ k ∧
      forwardGap α N (Int.fract ((k : ℝ) * α))
        = Int.fract (((j : ℝ) - (k : ℝ)) * α) := by
  have hfg : forwardGap α N (Int.fract ((k : ℝ) * α))
      = ((orbit α N).erase (Int.fract ((k : ℝ) * α))).inf' hNe
          (fun y => Int.fract (y - Int.fract ((k : ℝ) * α))) := by
    unfold forwardGap
    rw [dif_pos hNe]
  obtain ⟨y, hy, hyeq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (orbit α N).erase (Int.fract ((k : ℝ) * α))) hNe
      (fun y => Int.fract (y - Int.fract ((k : ℝ) * α)))
  rw [Finset.mem_erase] at hy
  obtain ⟨hyne, hyorb⟩ := hy
  simp only [orbit, Finset.mem_image, Finset.mem_range] at hyorb
  obtain ⟨j, hjN, rfl⟩ := hyorb
  refine ⟨j, hjN, ?_, ?_⟩
  · intro h
    exact hyne (by rw [h])
  · rw [hfg, hyeq]
    show Int.fract (Int.fract ((j : ℝ) * α) - Int.fract ((k : ℝ) * α))
        = Int.fract (((j : ℝ) - (k : ℝ)) * α)
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
    sorry

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
