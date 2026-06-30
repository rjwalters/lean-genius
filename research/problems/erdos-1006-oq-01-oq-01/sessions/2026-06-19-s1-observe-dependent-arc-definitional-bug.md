# S1 OBSERVE — `hasDependentArc` is mis-encoded ⇒ the de-axiomatization target is currently *false* (doc-only)

**Date**: 2026-06-19 (~11:24 UTC)
**Researcher**: researcher-2
**Mode**: OBSERVE — first session on this slug. Read `problem.md`, audited the
parent Lean file `Proofs/Erdos1006OQ01.lean`, and discovered a definitional
soundness bug that *blocks* the stated goal until the definition is repaired.
**Status**: thin doc-only OBSERVE. No Lean edit, no build, no Mathlib bearer
search, no parent gallery touch. (Build gate respected — host is saturated and
`docker-build` clones Mathlib from source.)

## §0. The task

`problem.md` (id `erdos-1006-oq-01-oq-01`, category extension, tractability
*challenging*): **"Prove `cover_graph_characterization` without axioms"** —
formalize Pretzel's proof that robustly acyclic orientations must be Hasse
diagrams.

Parent: `Proofs/Erdos1006OQ01.lean` (277 LOC, **3 axioms**, 0 sorries, badge
`axiom`, status `axiomatized`). The de-axiomatization target is the first axiom:

```lean
axiom cover_graph_characterization [Fintype V] :
  admitsRobustAcyclicOrientation G ↔ isCoverGraph G
```

## §1. Finding: `hasDependentArc` is vacuously false ⇒ `isRobustlyAcyclic ≡ isAcyclic`

The relevant definitions (lines 56–74):

```lean
def GraphOrientation.isAcyclic (O : GraphOrientation G) : Prop :=
  ∃ (rank : V → ℕ), ∀ u v, O.arc u v → rank u < rank v

def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ), (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank v ≤ rank u                                  -- ← BUG: inequality backwards

def GraphOrientation.isRobustlyAcyclic (O : GraphOrientation G) : Prop :=
  O.isAcyclic ∧ ¬O.hasDependentArc
```

**Claim.** For *every* acyclic `O`, `hasDependentArc O` is **False**, hence
`isRobustlyAcyclic O ↔ isAcyclic O`.

**Proof.** Let `O` be acyclic and let `R : V → ℕ` be a global rank witness
(`∀ a b, O.arc a b → R a < R b`). Fix any candidate arc `(u,v)` with
`O.arc u v`. The inner hypothesis of `hasDependentArc` asks for ranks
respecting *all arcs except `(u,v)`*; `R` respects **all** arcs, so it
satisfies that hypothesis. But `O.arc u v` gives `R u < R v`, i.e.
`¬ (R v ≤ R u)`. So `R` refutes the inner `∀`-statement
`(respects others) → rank v ≤ rank u` for this `(u,v)`. As `(u,v)` was
arbitrary, no arc satisfies the existential, so `hasDependentArc O` is False. ∎

Equivalently: an arc `(u,v)` could only be "dependent" in this encoding if the
*remaining* arcs forced `rank v ≤ rank u`, i.e. forced a directed path
`v → … → u`. But together with `O.arc u v` that is a directed cycle, impossible
in an acyclic `O`. The encoding therefore detects nothing.

## §2. Consequence: the axiom is *false*, and lets you derive `False`

Because `isRobustlyAcyclic ≡ isAcyclic`, we get
`admitsRobustAcyclicOrientation G ↔ (G admits an acyclic orientation)`, which is
**True for every finite `G`** (any linear order works — the file's own
`linearOrientation` is acyclic). So under the current definitions the axiom
asserts

> every finite graph is a cover graph of some poset

which is **false**. Concrete refutation — the triangle `K₃` (complete graph on
`Fin 3`):

- `admitsRobustAcyclicOrientation K₃ = True`: `linearOrientation` orients
  `0→1→2`, `0→2`; `rank = Fin.val` witnesses acyclicity; `hasDependentArc` is
  vacuously false by §1.
- `isCoverGraph K₃ = False`: a 3-element poset cannot have all three pairs
  covering. If `0 ⋖ 1` and `1 ⋖ 2` then `0 < 1 < 2`, so `0 ⋖ 2` fails (1 lies
  strictly between). By symmetry every linear/branching arrangement kills one
  of the three covering edges. Hence `K₃` is not a Hasse diagram.

Then `(cover_graph_characterization).mp (proof_admits) : isCoverGraph K₃`
contradicts `isCoverGraph K₃ = False`, i.e. `False` is derivable from the
axiom. **The current axiomatization is unsound, not merely strong.**

> Audit note for Mechanic/Auditor: `meta.json` honestly reports
> `status: axiomatized`, badge `axiom`, 3 axioms — the *disclosure* is fine.
> The problem is the *content* of one axiom contradicts the file's own
> definitions. This is a correctness bug in the Lean source, independent of the
> gallery-integrity numerics (which all match: 277 LOC / 3 axioms / 0 sorries).

## §3. The one-line fix

The intended notion: arc `(u,v)` is **dependent** iff *reversing* it (to `v→u`)
while keeping the other arcs creates a directed cycle — equivalently, no acyclic
ranking of the reversed orientation exists — equivalently, every ranking
respecting the other arcs already forces `rank u ≤ rank v` (so you cannot place
`v` below `u`). That is the **opposite** inequality:

```lean
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ), (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank u ≤ rank v                                  -- FIX: was `rank v ≤ rank u`
```

Sanity check of the fix:
- **No path `u → … → v` in the remaining arcs** ⇒ one can choose a respecting
  ranking with `rank v < rank u` (rank the two independently) ⇒ inner `∀` is
  False ⇒ arc **not** dependent (reversible). ✓
- **A path `u → … → v` in the remaining arcs** ⇒ every respecting ranking has
  `rank u < … < rank v`, so `rank u ≤ rank v` always holds ⇒ arc **dependent**
  (reversal closes a cycle). ✓

So `isRobustlyAcyclic` becomes the genuine "every arc is a covering relation"
property, and `admitsRobustAcyclicOrientation` becomes a *restrictive* property
(Nešetřil–Rödl: graphs of high girth and chromatic number fail it), as intended.

## §4. De-axiomatization roadmap (post-fix)

The proof file already contains the *forward* direction skeleton; the bug is why
it currently typechecks too easily. After the §3 fix the work is:

1. **STEP A (fix + re-prove forward).** Apply §3. Re-prove
   `cover_graph_admits_robust` (lines 157–167) under the corrected
   `hasDependentArc`. The old proof leaned on the vacuous collapse (it discharged
   `¬hasDependentArc` with a single global `posetRank`). Now `¬hasDependentArc`
   requires: for each covering arc `u ⋖ v`, a ranking respecting all *other*
   covering arcs with `rank v < rank u`. This is realizable because `u ⋖ v`
   means nothing lies strictly between `u` and `v`, so the pair can be swapped
   without violating other covers — but it must be constructed (perturb
   `posetRank`), not asserted.

2. **STEP B (reverse direction = the actual Pretzel content).**
   `admitsRobustAcyclicOrientation G → isCoverGraph G`. Given robustly acyclic
   `O`, define the **reachability preorder** `u ≤ v := Relation.ReflTransGen O.arc u v`.
   Acyclicity (the rank witness) gives antisymmetry ⇒ `PartialOrder V`. Then show
   `isCoverGraphOf G`, i.e. `G.Adj u v ↔ (u ⋖ v ∨ v ⋖ u)`:
   - (→) `Adj u v` ⇒ WLOG `O.arc u v` (covers) ⇒ `u < v`. Robustness (every arc
     independent under the *corrected* def) ⇒ no path `u → … → v` of length ≥ 2
     ⇒ nothing strictly between ⇒ `u ⋖ v`.
   - (←) `u ⋖ v` ⇒ `u < v` ⇒ a directed `O`-path `u → … → v`. Its first arc
     `u → w` gives `u < w ≤ v`; covering ⇒ `w = v` ⇒ `O.arc u v` ⇒ `Adj u v`.

3. **STEP C.** Combine A+B into `cover_graph_characterization` as a `theorem`,
   delete the axiom, update `meta.json` (`axiomCount 3 → 2`, refresh
   `assumptions`). The other two axioms (`chromatic_lt_girth_implies_robust`,
   `nesetril_rodl_counterexample`) are *separate, genuinely deep* results and
   stay axiomatized for now — out of scope for this slug.

**Mathlib infrastructure**: `Relation.ReflTransGen` / `Relation.TransGen` for
reachability; `Finset.card_lt_card` (already used by `posetRank_strictMono`);
`PartialOrder.lift` is not directly applicable (no carrier map) — build the
instance by hand from reachability with antisymmetry from the rank witness.

**Tractability re-assessment**: STEP B is the real theorem and is *moderate*,
not *challenging*, once the reachability poset is set up — the robustness ⇔
covering equivalence is exactly what the corrected definition encodes. STEP A
(re-proving forward under the fix) is the fiddlier part (constructing per-arc
swapped rankings).

## §5. Why no Lean edit this session

The §3 fix cascades into STEP A (the existing `cover_graph_admits_robust` proof
breaks under the corrected definition). Shipping the definition swap *without*
the repaired forward proof would leave the file broken; shipping both requires a
Docker build to verify, and the host is saturated (per project policy, never run
`lake build`; `docker-build` clones Mathlib from source = OOM risk). Pushing
unverified Lean is unsafe (deployer auto-merges math PRs). This session therefore
ships the **finding + roadmap only**; the Lean change is the next build-capable
session's STEP A/B/C.

## §6. State transition

OBSERVE → **ORIENT**. The obstacle is identified (definitional bug), the fix is
known (§3), and the reverse-direction strategy is sketched (§4 STEP B). Next
action: in a build-capable session, apply §3, re-prove forward (STEP A), then
formalize the reachability-poset reverse direction (STEP B), build via
`docker-build Proofs.Erdos1006OQ01`, and de-axiomatize.
