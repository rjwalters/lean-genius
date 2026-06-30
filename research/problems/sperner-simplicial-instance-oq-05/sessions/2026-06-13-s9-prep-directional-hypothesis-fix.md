# S9 PREP — `scarfWalk_isPanchromatic`: the S8 parity hypothesis `c 0 ≠ c m` is INSUFFICIENT; corrected directional hypothesis + provable rightward soundness

**Slug**: `sperner-simplicial-instance-oq-05`
**Researcher**: researcher-1
**Date**: 2026-06-13
**Session**: 17 (S9 PREP — correction)
**Type**: Doc-only readiness/correction memo (no `.lean` diff, no gallery diff)
**Predecessor**: Session 16 (S8 PREP, 2026-06-04, researcher-1) proposed amending
`scarfWalk_isPanchromatic` with `(h_parity : c 0 ≠ c m)` and sketched a ~55 LOC
discharge.
**Successor**: S9/S10 ACT — discharge the **corrected** rightward theorem under Docker.

---

## 0. TL;DR

The S8 PREP amendment is **wrong**: `c 0 ≠ c m` does **not** make
`scarfWalk_isPanchromatic` true, because the 1-d Scarf walk is **strictly
directional** — the entry face `k` fixes a single travel direction (left or
right) for the entire walk, so a *global* endpoint-parity hypothesis cannot
guarantee a panchromatic cell lies *in the direction the walk actually travels*.

A concrete counterexample (`m = 4`, `c = (0,1,1,1,1)`, `start = 2`, `k = 1`)
satisfies `c 0 ≠ c m` yet the walk returns the **non-panchromatic** cell 3.

The **correct** hypothesis is *directional*. For the rightward walk
(`k = ⟨1⟩`, the case the smoke-test exercises) it is:

```lean
(h_parity : c start.val ≠ c m)     -- rightward: colour must change to the right of `start`
```

Under this hypothesis the theorem is **true and cleanly provable** by induction
on the fuel parameter with the measure `m - start.val ≤ fuel`; the boundary
case is discharged by contradiction with `h_parity`. Full strategy in §4.

**Had S8 ACT shipped as written, it would have discharged the `sorry` with a
provably false theorem** (or, more likely, failed to close and burned the
session). This correction is the load-bearing deliverable.

---

## 1. Why the walk is directional (root cause)

`step` (leaf file L64–72) computes the exit face as the *flip* of the entry
face and consults the parent adjacency `iadj` (parent file L818–829, wired into
`intervalTriangulation` at L968 via `adj := iadj m`):

```lean
def step (hm) (i) (k) (_h_in) : Fin m ⊕ (Fin m × Fin 2) :=
  let k' := if k.val = 0 then ⟨1⟩ else ⟨0⟩
  match (intervalTriangulation m hm).adj i k' with
  | none           => .inl i              -- boundary: stuck on current cell
  | some (i', k'') => if IsPanchromatic1d c i' then .inl i' else .inr (i', k'')
```

`iadj m i k'` (parent L818):
- `k'.val = 0` ⇒ `if i+1 < m then some (⟨i+1⟩, ⟨1⟩) else none`
- `k'.val ≠ 0` ⇒ `if 0 < i then some (⟨i-1⟩, ⟨0⟩) else none`

Trace the entry face through one step:

| entry `k` | exit `k' = flip k` | `iadj` move | new cell | new entry `k''` |
|---|---|---|---|---|
| `1` | `0` | `i → i+1` (if `i+1 < m`) | `i+1` | `1` |
| `0` | `1` | `i → i-1` (if `0 < i`)  | `i-1` | `0` |

**The new entry face equals the original entry face.** So the direction is an
*invariant* of the walk: enter through face `1` ⇒ the walk moves
`+1, +1, +1, …` (rightward) forever; enter through face `0` ⇒ it moves
`−1, −1, −1, …` (leftward) forever. `scarfWalkAux` recurses with exactly this
`k''` (leaf L89: `scarfWalkAux hm next k' n`), so the invariant is preserved by
construction.

**Consequence.** A rightward walk from `start` can only ever inspect cells
`start, start+1, …, m-1`. It is *blind* to every cell with index `< start`.
Symmetrically a leftward walk is blind to cells `> start`. Therefore any
soundness hypothesis must put the colour change **in the direction of travel**.

## 2. Counterexample to the S8 hypothesis `c 0 ≠ c m`

Let `m = 4` and `c = (c0,c1,c2,c3,c4) = (0,1,1,1,1)` (i.e. `c n = if n = 0 then 0 else 1`).

- Panchromatic cells (cell `i` = edge `[i,i+1]`, panchromatic iff `c i ≠ c (i+1)`):
  - cell 0: `c0=0 ≠ c1=1` → **panchromatic**
  - cell 1: `c1=1 = c2` → no; cell 2: `c2=1=c3` → no; cell 3: `c3=1=c4` → no.
- S8 hypothesis holds: `c 0 = 0 ≠ 1 = c 4 = c m`. ✓
- Take `start = ⟨2⟩`, `k = ⟨1⟩` (rightward). `h_start`: `c2=1=c3`, so
  `¬ IsPanchromatic1d c ⟨2⟩`. ✓

Walk (`scarfWalk c (by omega) ⟨2⟩ ⟨1⟩ h_start = scarfWalkAux … ⟨2⟩ ⟨1⟩ 4`):

1. cell 2, not panchromatic → `step`: `k'=0`, `iadj 4 ⟨2⟩ ⟨0⟩`: `2+1=3<4` ⇒
   `some (⟨3⟩, ⟨1⟩)`. `IsPanchromatic1d c ⟨3⟩`? `c3=1=c4` → no ⇒ `.inr (⟨3⟩, ⟨1⟩)`,
   recurse with fuel 3.
2. cell 3, not panchromatic → `step`: `k'=0`, `iadj 4 ⟨3⟩ ⟨0⟩`: `3+1=4 < 4`?
   **No** ⇒ `none` ⇒ `.inl ⟨3⟩`. Walk returns cell **3**.

`IsPanchromatic1d c ⟨3⟩ = (c3 ≠ c4) = (1 ≠ 1) = False`. So the walk returns a
**non-panchromatic** cell while `c 0 ≠ c m` holds. **The S8-amended theorem is
provably false.** ∎

The flaw in S8 PREP §2 point 2 ("the walk must land on a panchromatic cell …
it cannot terminate on a non-panchromatic cell via the `.adj = none` branch")
is exactly this: the `.adj = none` branch *does* fire on a non-panchromatic
cell when the colour change lies *behind* the walk (here, the only change is at
cell 0, to the **left** of `start = 2`, while the walk goes right).

## 3. The corrected (directional) hypothesis

The walk's entry face is fixed by the `k` argument of `scarfWalk`. Two clean
soundness theorems, one per direction:

### 3a. Rightward (the smoke-test case, `k = ⟨1⟩`)

```lean
theorem scarfWalk_isPanchromatic_right (hm : 0 < m) (start : Fin m)
    (h_start : ¬ IsPanchromatic1d c start)
    (h_parity : c start.val ≠ c m) :
    IsPanchromatic1d c (scarfWalk c hm start ⟨1, by omega⟩ h_start) := …
```

Rationale: a rightward walk inspects edges `[start,start+1], …, [m-1,m]`; if
`c start ≠ c m` then `c` is non-constant on `{start, …, m}`, so some inspected
edge is panchromatic, and the walk halts at the **first** one. `h_parity`
rejects the §2 counterexample (`c start = c 2 = 1 = c 4 = c m`, so the
hypothesis fails — the theorem correctly does not apply). ✓

### 3b. Leftward dual (`k = ⟨0⟩`)

```lean
theorem scarfWalk_isPanchromatic_left (hm : 0 < m) (start : Fin m)
    (h_start : ¬ IsPanchromatic1d c start)
    (h_parity : c 0 ≠ c (start.val + 1)) :
    IsPanchromatic1d c (scarfWalk c hm start ⟨0, by omega⟩ h_start) := …
```

(A leftward walk inspects edges `[start,start+1], [start-1,start], …, [0,1]`,
i.e. the colours `{0, …, start+1}`; non-constancy there is `c 0 ≠ c (start+1)`.)

### 3c. Recommendation

Ship **3a only** for S9 ACT. It is the case the existing `decide` smoke-test
exercises (`start = ⟨0⟩`, `k = ⟨1⟩`) and the canonical "constructive 1-d
Sperner" statement (start at the left boundary, walk right to the colour
change). 3b is an optional symmetric bonus. A *single* combined theorem with a
direction-dispatched hypothesis (`if k = 1 then c start ≠ c m else c 0 ≠ c (start+1)`)
is achievable but uglier and not recommended — two named theorems read better.

### 3d. Smoke-test compatibility (corrected hypothesis holds)

The S7 `example` (leaf L162–168) uses `m = 3`, `c n = if n ≤ 1 then 0 else 1`
(so `c = (0,0,1,1)`), `start = ⟨0⟩`, `k = ⟨1⟩`. Corrected rightward hypothesis:
`c start.val = c 0 = 0 ≠ 1 = c 3 = c m`. ✓ The `decide` smoke-test transfers
unchanged; an S9 ACT can additionally re-state it as an *application* of
`scarfWalk_isPanchromatic_right` with `h_parity := by decide`.

## 4. Proof strategy for 3a (rightward soundness)

The crux is a fuel-indexed generalisation proved by induction on the fuel.

### 4a. Generalised lemma

```lean
private lemma scarfWalkAux_right_sound (hm : 0 < m) :
    ∀ (f : ℕ) (s : Fin m),
      c s.val ≠ c m → m - s.val ≤ f →
        IsPanchromatic1d c (scarfWalkAux c hm s ⟨1, by omega⟩ f)
```

Then 3a is immediate: `scarfWalk c hm start ⟨1⟩ h_start = scarfWalkAux c hm start ⟨1⟩ m`
(by `scarfWalk_eq_scarfWalkAux`, the S7 lemma), and `m - start.val ≤ m` always.
So `scarfWalk_isPanchromatic_right := scarfWalkAux_right_sound hm m start h_parity (by omega)`
modulo the `rw [scarfWalk_eq_scarfWalkAux]`.

### 4b. Induction on `f`

**Base `f = 0`.** Hypothesis `m - s.val ≤ 0` with `s.val < m` (so `m - s.val ≥ 1`)
is contradictory: `exact absurd hfuel (by have := s.isLt; omega)`. (The walk never
actually exhausts fuel under the measure; the base case is vacuous.)

**Step `f = n + 1`.** Unfold one layer of `scarfWalkAux` (leaf L84–89):

- **Panchromatic start.** If `IsPanchromatic1d c s`, the walk returns `s`
  immediately (S7 `scarfWalkAux_of_panchromatic_start`); goal is the hypothesis
  itself. `simpa using h`.
- **Non-panchromatic start.** Then `hps : ¬ IsPanchromatic1d c s`, i.e.
  (after `simp only [IsPanchromatic1d, not_not] at hps`) `hps : c s.val = c (s.val+1)`.
  The walk reduces to `match step c hm s ⟨1⟩ hps with …`. Evaluate `step`:
  exit face `k' = ⟨0⟩` (since `(⟨1⟩:Fin 2).val = 1 ≠ 0`), and
  `(intervalTriangulation m hm).adj s ⟨0⟩ = iadj m s ⟨0⟩` (defeq, `adj := iadj m`).
  `iadj m s ⟨0⟩` branches on `s.val + 1 < m`:
  - **`s.val + 1 < m`.** `iadj = some (⟨s.val+1⟩, ⟨1⟩)`. Two sub-cases on
    `IsPanchromatic1d c ⟨s.val+1⟩`:
    - panchromatic ⇒ `step = .inl ⟨s.val+1⟩` ⇒ walk returns `⟨s.val+1⟩`, which is
      panchromatic. ✓
    - non-panchromatic ⇒ `step = .inr (⟨s.val+1⟩, ⟨1⟩)` ⇒ walk recurses
      `scarfWalkAux c hm ⟨s.val+1⟩ ⟨1⟩ n`. Apply `ih` with `s := ⟨s.val+1⟩`:
      - parity: need `c (s.val+1) ≠ c m`. From `hps : c s.val = c (s.val+1)` and
        `hpar : c s.val ≠ c m` get `c (s.val+1) = c s.val ≠ c m`. ✓
      - fuel: need `m - (s.val+1) ≤ n`. From `hfuel : m - s.val ≤ n+1` and
        `s.val+1 ≤ m` get `m - (s.val+1) = (m - s.val) - 1 ≤ n`. ✓
      `ih` closes the goal. ✓
  - **`s.val + 1 ≥ m`, i.e. `s.val + 1 = m`** (since `s.val < m`). `iadj = none`
    ⇒ `step = .inl s` ⇒ walk returns `s` — *but `s` is non-panchromatic*. This
    branch is killed by `h_parity`: `s.val + 1 = m` gives
    `c (s.val+1) = c m`, and `hps : c s.val = c (s.val+1) = c m`, contradicting
    `hpar : c s.val ≠ c m`. `exact absurd (hps.trans (by rw [...])) hpar` (or
    `omega`/`simp`-assisted). ✓

Every branch closes. The measure `m - s.val` strictly decreases on the only
recursive call (`s → s+1`), matching the consumed fuel; `h_parity` is the exact
ingredient that excludes the false `.adj = none` terminal.

### 4c. Lean fiddliness to expect (for the ACT, under Docker)

- **`step` reduction.** Unfolding `step` and `iadj` through the `if`/`dite`
  chain needs care: prefer `simp only [step, intervalTriangulation, iadj]` then
  `split` / `split_ifs`, or a dedicated `step_right` helper lemma:
  `step c hm s ⟨1⟩ h = if h2 : s.val+1 < m then (if IsPanchromatic1d c ⟨s.val+1, h2⟩ then .inl ⟨s.val+1,h2⟩ else .inr (⟨s.val+1,h2⟩, ⟨1⟩)) else .inl s`.
  Proving this helper once (by `simp [step]; split <;> rfl`-style) makes the
  main induction much cleaner. **Recommended**: add `step_right_eq` as a named
  reduction lemma alongside the S7 structural lemmas.
- **`Fin` literal matching.** `⟨1, by omega⟩ : Fin 2` vs `(1 : Fin 2)` — keep one
  spelling throughout; `Fin.isValue`/`decide` handle the `.val` facts.
- **`scarfWalkAux` unfold at `n+1`.** Use `rw [scarfWalkAux]` (the equation
  lemma) or `conv`/`unfold`; then `by_cases` on `IsPanchromatic1d c s` (decidable
  instance exists, leaf L53).

### 4d. Estimated decomposition

| Sub-item | LOC | Risk | Notes |
|---|---|---|---|
| `step_right_eq` reduction helper | ~8 | LOW | `simp [step] ; split <;> rfl`; isolates `iadj` `dite` mess. |
| `scarfWalkAux_right_sound` (induction) | ~30 | MED | Fuel induction; boundary contradiction via `h_parity`. |
| `scarfWalk_isPanchromatic_right` (wrapper) | ~3 | LOW | `rw [scarfWalk_eq_scarfWalkAux]; exact …`. |
| (optional) `scarfWalk_isPanchromatic_left` dual | ~35 | MED | Mirror; ship only if time permits. |
| **Total (3a only)** | **~40** | **MED** | Within an ACT budget. Docker-verify mandatory. |

## 5. Downstream impact — `exists_panchromatic_constructive`

The current proof-term (leaf L111–116) applies `scarfWalk_isPanchromatic`
directly. With the corrected directional theorem it must (a) fix the direction
and (b) thread the directional parity. Recommended canonical form (left
boundary, rightward, the classical constructive 1-d Sperner):

```lean
theorem exists_panchromatic_constructive (hm : 0 < m)
    (h_parity : c 0 ≠ c m)                       -- canonical Sperner endpoint
    (h_start : ¬ IsPanchromatic1d c ⟨0, hm⟩) :
    ∃ i : Fin m, IsPanchromatic1d c i :=
  ⟨scarfWalk c hm ⟨0, hm⟩ ⟨1, by omega⟩ h_start,
   scarfWalk_isPanchromatic_right c hm ⟨0, hm⟩ h_start (by simpa using h_parity)⟩
```

Here `start = ⟨0⟩`, so the rightward hypothesis `c start.val ≠ c m` is exactly
`c 0 ≠ c m` — the global Sperner endpoint condition **is** correct *when you
start at the left boundary and walk right*. (The S8 `c 0 ≠ c m` was right for
this specific entry point but wrong as a hypothesis on the *general* `start`/`k`
theorem.) The old `boundary_door : Fin m × Fin 2` parameter is dropped in favour
of the canonical `⟨0⟩`/`⟨1⟩` start; if a caller needs an arbitrary start, expose
`scarfWalk_isPanchromatic_right` directly.

**No external callers** (grep `exists_panchromatic_constructive` over `proofs/`,
`src/` → leaf file only; the C2-1d module is a gallery `additionalFiles[]`
companion, not imported elsewhere). Change is contained to the leaf file.

**Gallery impact**: none. `src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
advertises the C1 brute-force module only; the C2-1d Scarf module carries no
annotations yet (S10+ scope).

## 6. Acceptance criteria for S9 ACT (under Docker)

- [ ] `scarfWalk_isPanchromatic_right` exists with hypothesis `c start.val ≠ c m`
      (NOT `c 0 ≠ c m` on a general `start`).
- [ ] The old `scarfWalk_isPanchromatic` (general `k`, hypothesis-free, `sorry`)
      is **removed** or replaced — it is *false* and must not remain as a stated
      theorem even behind `sorry`.
- [ ] `exists_panchromatic_constructive` re-proved via the corrected theorem
      (canonical left-boundary form in §5), 0 sorries.
- [ ] No new `axiom`s. Sorry count on the leaf file 1 → 0.
- [ ] The S7 `decide` smoke-test still passes (corrected hypothesis holds for
      its colouring, §3d).
- [ ] `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstanceOQ05Scarf1d`
      succeeds; the single pre-existing sorry warning disappears, no new warnings.
- [ ] Counterexample regression guard (optional but recommended): a `decide`
      `example` that the §2 colouring `(0,1,1,1,1)` with `start=2,k=1` yields a
      non-panchromatic walk result — documents *why* the directional hypothesis
      is needed and prevents a future regression to the global-parity form.

## 7. INFRA / host context

- **Docker daemon: DOWN this session** (`docker info` times out at 15 s).
  No Lean build possible; this memo is doc-only by necessity. Disk has
  **recovered** to 97 GiB free / 11 % used (the 2026-06-13 "disk 100 %" incident
  noted in agent memory is resolved). The blocker is now the Docker daemon, not
  disk.
- HEAD `fa1c4d27aa8` (`agents: per-slot researcher model pin`, #22898), branch
  `research/sperner-oq05-s9-prep-directional-fix` off `origin/main`.
- Mathlib pin (per `proofs/lake-manifest.json`): `2df2f0150c…` (v4.26.0),
  unchanged since S3 PREP #18712.
- Leaf file `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`: 170 LOC,
  1 real sorry (L105, `scarfWalk_isPanchromatic`), 0 axioms — unchanged since S7.
- Pre-claim probe: `gh pr list --search "sperner-simplicial-instance-oq-05 in:title" --state open`
  → 0 open PRs. Uncontested claim window.

## 8. Risk inventory

| Risk | Level | Mitigation |
|---|---|---|
| The corrected rightward hypothesis is itself insufficient | LOW | §4 gives a complete branch-by-branch proof; the only terminal that fails (boundary `.adj=none`) is exactly the one `h_parity` excludes. Counterexample §2 confirms necessity; §3d confirms the smoke-test satisfies it. |
| `step`/`iadj` `dite` reduction fights the tactics | MED | §4c recommends a `step_right_eq` helper to isolate the `dite` chain; precedent `iadj_cases` (parent L832) shows the pattern. Docker iteration needed. |
| Dropping `scarfWalk_isPanchromatic` breaks an importer | LOW | Grep confirms leaf-file-only usage; gallery is C1-only. |
| Ship-without-Docker temptation | N/A (avoided) | This PR is doc-only; the ACT is explicitly gated on `docker-build.sh` success (§6). No `.lean` diff is shipped unverified. |
| Mathlib pin drift | LOW | Pin byte-stable since #18712; §4 routes through public `T.adj`/`iadj` (no private parent lemmas beyond the already-public reduction). |

## 9. References

- **S8 PREP memo (corrected by this memo)**:
  `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-06-04-s8-prep-parity-hypothesis.md`
- **S7 ACT memo** (structural lemmas + smoke test):
  `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-06-01-s7-act-helper-lemmas.md`
- **Leaf file**: `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
  (170 LOC; `step` L64, `scarfWalkAux` L81, `scarfWalk` L93,
  `scarfWalk_isPanchromatic` `sorry` L102–105, S7 lemmas L130–150, smoke-test L162).
- **Parent file**: `proofs/Proofs/SpernerSimplicialInstance.lean`
  (`iadj` L818, `iadj_cases` L832, `iadj_symm'` L866, `intervalTriangulation`
  L958 with `adj := iadj m` L968).
- **State log**: `research/problems/sperner-simplicial-instance-oq-05/state.md`
- **Classical 1-d Sperner**: the discrete intermediate-value theorem —
  `c : {0,…,m} → Fin 2`, `c 0 ≠ c m ⇒ ∃ i < m, c i ≠ c (i+1)`. The directional
  refinement (this memo) is that a *one-way* search from `start` finds it iff the
  colour change lies on that side, i.e. iff `c start ≠ c m` (rightward).
