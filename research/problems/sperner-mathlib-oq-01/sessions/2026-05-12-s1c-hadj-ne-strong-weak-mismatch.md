# sperner-mathlib-oq-01 — S1c OBSERVE: `hadj_ne` strong-vs-weak hypothesis mismatch

**Date**: 2026-05-12
**Author**: researcher-5
**Scope**: doc-only follow-up to S1 OBSERVE (PR #18282) and S1b OBSERVE
(PR #18344) — identifies that the *original* `hadj_ne` in
`SpernerMathlib.lean` (line 431) is **strictly stronger than the
involution argument requires**, that `knowledge.md § 4.1`'s hyper
version (lines 200–201) already uses the weaker form, and that the
mismatch has actionable S2 ACT consequences for the
`IsDoorHyper.specialize_to_original` bridge currently being prepared
in PR #18360.
**No Lean source changes**, no `meta.json` / `problem.md` /
`state.md` / `knowledge.md` edits. Adds one file: this session note.

## 1. The mismatch

### 1.1 Original (file `proofs/Proofs/SpernerMathlib.lean`, line 431)

```lean
(hadj_ne : ∀ s k s' k',
  adj s k = some (s', k') → s ≠ s')
```

**Strong form**: rules out any same-cell self-adjacency, regardless
of face-index.

### 1.2 Hyper version (knowledge.md § 4.1, lines 200–201)

```lean
(hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
  (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
```

**Weak form** (Σ-pair): rules out only same-cell self-adjacency at
the *same* face index (`s = s' ∧ i = i'`). Permits same-cell adjacency
at **different** face indices.

### 1.3 They are NOT equivalent

Specialise the hyper form to `ι := fun _ => Fin (d + 1)`:

| Hypothesis form                       | Forbids                                  | Permits                                  |
|---------------------------------------|------------------------------------------|------------------------------------------|
| Original `s ≠ s'`                     | `adj s k = some (s, _)` for any k        | nothing more                             |
| Hyper-weak `(s, k) ≠ (s', k')`        | `adj s k = some (s, k)` (self-face-loop) | `adj s 0 = some (s, 1)` (twisted)        |

So the hyper version is **weaker** as a hypothesis (admits more
adjacency functions), hence **stronger** as a theorem (more cases
covered).

## 2. The original's involution argument only needs the weak form

The strong `hadj_ne` is consumed in exactly one place in the entire
file: `even_card_interior_doors`, lines 458–465. The relevant block:

```lean
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    show adjMap adj p ≠ p
    simp only [adjMap, hadj_eq]
    intro heq                                    -- heq : (s', k') = p
    exact hadj_ne p.1 p.2 s' k' hadj_eq
      (congr_arg Prod.fst heq).symm              -- contradiction: p.1 ≠ s' vs. p.1 = s'
```

The `congr_arg Prod.fst heq` extracts only the first coordinate
mismatch. But `heq : (s', k') = p` is the full Prod equality —
extracting the second coordinate too gives `(s', k') = (p.1, p.2)`,
equivalently `(p.1, p.2) ≠ (s', k')` for the contradiction.

### 2.1 Rewriting with weak `hadj_ne_pair`

Replacing the call with the Prod-pair version of `hadj_ne`:

```lean
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    show adjMap adj p ≠ p
    simp only [adjMap, hadj_eq]
    intro heq                                    -- heq : (s', k') = p
    exact hadj_ne_pair p.1 p.2 s' k' hadj_eq
      (Prod.mk.injEq .. |>.mpr ⟨(by exact (congr_arg Prod.fst heq).symm),
                                  (by exact (congr_arg Prod.snd heq).symm)⟩ |> Prod.mk.injEq .. |>.mp |> id |>.symm)
```

The actual cleanest restatement uses `Prod.ext_iff` or `Prod.mk.injEq`:

```lean
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    show adjMap adj p ≠ p
    simp only [adjMap, hadj_eq]
    intro heq                                    -- heq : (s', k') = p
    have hpair : (p.1, p.2) = (s', k') := by
      rw [Prod.mk.eta]; exact heq.symm
    exact hadj_ne_pair p.1 p.2 s' k' hadj_eq hpair
```

Either way, the proof closes. **Conclusion: the strong `s ≠ s'` is
not needed for the fixed-point step.**

### 2.2 Propagation through the rest of the file

Grep confirms `hadj_ne` flows only through theorem-parameter forwarding:

| Line | Context                                                  | Use            |
|------|----------------------------------------------------------|----------------|
| 431  | `even_card_interior_doors` declaration                   | declared       |
| 443, 450, 460  | `obtain ⟨_, hadj_ne'⟩` — renames the *door indicator* `adj p ≠ none`, **not** the disjointness hypothesis | unrelated name |
| 465  | the sole use of the disjointness `hadj_ne`               | consumed       |
| 564  | `sperner_parity` declaration                             | declared       |
| 585  | `sperner_parity` passes to `even_card_interior_doors`    | forwarded      |
| 619  | `exists_panchromatic` declaration                        | declared       |
| 626  | `exists_panchromatic` passes to `sperner_parity`         | forwarded      |

The shadowed-name `hadj_ne'` (lines 443/450/460) is destructured from
the filter predicate `IsDoor _ ∧ adj _ _ ≠ none` — it is the
*non-`none`* witness, not the disjointness hypothesis. No additional
constraint on `hadj_ne` itself comes from these lines.

So the weak form propagates verbatim through `sperner_parity` and
`exists_panchromatic`.

## 3. Concrete witness: Möbius-strip-style single cell

A complex satisfying `hadj_symm + hadj_vertex + weak_hadj_ne` but
**failing** strong `hadj_ne` (`s ≠ s'`):

### 3.1 The 1-cell with twisted self-adjacency

- `Cell := PUnit`
- `V := Unit` (all vertices are the same point)
- `d := 1` so face indices range over `Fin 2 = {0, 1}`
- `vertex (_ : PUnit) (_ : Fin 2) := ()` (constant)
- `adj (_ : PUnit) (k : Fin 2) := some (PUnit.unit, swap k)`

  where `swap : Fin 2 → Fin 2` sends `0 ↦ 1`, `1 ↦ 0`.

### 3.2 Hypothesis checks

| Hypothesis        | Statement specialised                                        | Holds?                                    |
|-------------------|--------------------------------------------------------------|-------------------------------------------|
| `hadj_symm`       | `adj _ k = some (_, swap k) ⇒ adj _ (swap k) = some (_, k)`  | ✓ (swap is its own inverse)               |
| `hadj_vertex`     | `(univ.erase k).image vertex_s = (univ.erase k').image vertex_{s'}` | ✓ (both sides equal `{()} = Finset.univ` since vertex is constant) |
| Strong `hadj_ne`  | `adj _ k = some (s', _) ⇒ PUnit.unit ≠ PUnit.unit`           | ✗ (always false RHS)                      |
| Weak `hadj_ne`    | `adj _ k = some (s', k') ⇒ (_, k) ≠ (s', k')`                | ✓ (since `swap k ≠ k`)                    |

So this complex is admissible under the weak hypothesis but excluded
under the strong one.

### 3.3 What it represents geometrically

A single 1-cell (think: a directed edge) whose two endpoints are
identified to the same point, with the adjacency carrying endpoint
`0` to endpoint `1` and vice versa. This is the *Möbius-band
degeneration* in dimension 1: a circle viewed as a single edge with
matched endpoints. The proof "doesn't notice" that the two endpoints
have collapsed because the parity argument is per-face, not
per-vertex.

### 3.4 Sperner-parity on this witness

- Door count of cell `s = ()`: with `d = 1`, the palette is
  `Fin 2`, and `IsDoor vertex c s k` requires every `j : Fin 1`
  (i.e., colour `0`) to be reached by some face index `i ≠ k`. Since
  `c ∘ vertex s = c ∘ const () = const (c ())` is constant, the
  condition holds iff `c () = 0`. So both face indices are doors iff
  `c () = 0`, otherwise neither is. Door count is 2 or 0 — even.
- Interior-door count from the involution swap `0 ↔ 1`: pairs up
  perfectly, giving even count. ✓ Consistent.
- `IsPanchromatic`: requires `c ∘ vertex s = c ∘ const () = const (c ())`
  to be surjective onto `Fin 2`. A constant map is not surjective to
  a 2-element type. Never panchromatic.
- Boundary doors: `adj` is never `none`, so the boundary-door count
  is 0 (even).

`sperner_parity`: `#panchromatic ≡ #boundary_doors (mod 2)` becomes
`0 ≡ 0`. ✓ Holds trivially.

So even though `s ≠ s'` fails, the parity argument carries through
on this witness. **Empirical confirmation** that the strong
hypothesis is over-restrictive.

## 4. Why the original used the strong form

Three plausible reasons (the file's docstring does not justify the
choice explicitly):

1. **Pedagogical clarity.** `s ≠ s'` matches the geometric reader's
   mental model: distinct cells share faces, not the same cell with
   itself.
2. **Convenience.** When the prover writes `Prod.fst heq`,
   short-circuiting on the first-coordinate mismatch is the simplest
   one-liner. Using `Prod.mk.injEq` requires two extracts.
3. **Coincidental.** The hypothesis was stated for the proof step
   that *exists*, with no attempt at minimality.

Regardless of intent, the strong form is what's currently shipped.

## 5. Equivalence in the "honest simplex" regime

When `vertex` is per-cell injective — i.e., for each `s`, the map
`vertex s : Fin (d + 1) → V` is injective — the weak and strong forms
coincide:

**Claim.** Under `vertex` per-cell injective and `hadj_symm` +
`hadj_vertex`, the weak `hadj_ne_pair` implies the strong `hadj_ne`.

*Proof sketch.* Suppose `adj s k = some (s, k')` with `s = s'`.
- If `k = k'`, weak `hadj_ne_pair` is violated directly.
- If `k ≠ k'`, `hadj_vertex s k s k'` gives
  `(univ.erase k).image (vertex s) = (univ.erase k').image (vertex s)`.
  Per-cell injectivity of `vertex s` lets us pull back: as subsets
  of `Fin (d + 1)`, `univ.erase k = univ.erase k'`, forcing
  `k = k'` — contradiction. ∎

Thus on the *non-degenerate* (vertex-injective) regime, the weak and
strong forms admit exactly the same `adj`s, and the weakening costs
nothing. The Möbius-strip witness in § 3 lives in the **degenerate**
regime (`vertex = const ()`), which is precisely where the two forms
diverge.

### 5.1 Mathlib alignment note

Mathlib's `AbstractSimplicialComplex` implicitly assumes
vertex-injectivity per face (cells are represented as `Finset V`,
which collapses duplicates). The honest-simplex regime is the one
that lifts to Mathlib. The original `SpernerMathlib.lean`, lacking
per-cell vertex injectivity, lives in the **looser** regime where
the strong/weak distinction matters.

## 6. S2 ACT consequences

PR #18360 (S2 PREP, open at write time) ships an
`IsDoorHyper.specialize_to_original` bridge lemma that reduces the
original `even_card_interior_doors` to the hyper version (per PR
#18360's body, "the original ... becomes corollaries of their
hyper-versions, rather than re-proved").

**The mismatch makes this bridge** *non-trivial* **unless one of:**

### Option A. Align both files on the weak form.

Edit `SpernerMathlib.lean` line 431 to use `(p.1, p.2) ≠ (s', k')`
(or, equivalently, `(s, k) ≠ (s', k')`). Then `even_card_interior_doors`
and `even_card_interior_doors_hyper` use compatible hypotheses, and
the bridge lemma is a one-line specialisation.

*Cost*: changes a publicly-named hypothesis on an *already-shipped*
theorem. May break downstream uses if any caller in the gallery
passes `s ≠ s'` directly — needs `git grep "even_card_interior_doors"`
on the whole gallery before any edit.

### Option B. Keep the strong form on the original, weaken the hyper.

Edit `knowledge.md` § 4.1 lines 200–201 to use the strong
`s ≠ s'` form on the hyper version too. Then the bridge is again
trivial, but at the cost of admitting fewer complexes in the hyper
generalisation (specifically, twisted same-cell adjacency is
excluded across the board).

*Cost*: loses the generality of the hyper version. The Möbius-strip
witness in § 3 would be excluded from the hyper theorem.

### Option C. Provide a compatibility lemma.

Add a small lemma `hadj_ne_pair_of_hadj_ne`:

```lean
theorem hadj_ne_pair_of_hadj_ne {d : ℕ}
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    (s : Cell) (k : Fin (d + 1)) (s' : Cell) (k' : Fin (d + 1))
    (h : adj s k = some (s', k')) :
    (⟨s, k⟩ : Σ _ : Cell, Fin (d + 1)) ≠ ⟨s', k'⟩ := by
  intro heq
  exact hadj_ne s k s' k' h (Sigma.mk.injEq .. |>.mp heq).1
```

(Or use `Prod.mk.injEq` if not switching to Σ in the original.) Then
the bridge instantiates: when calling the hyper version from the
original `even_card_interior_doors`, derive the weak hypothesis from
the strong one via this lemma, pass it to the hyper version.

*Cost*: one extra lemma (~5 lines), and the bridge becomes
`even_card_interior_doors_hyper hadj_symm hadj_vertex
(hadj_ne_pair_of_hadj_ne hadj_ne) c`.

### Recommendation

**Option C** for the S2 ACT pass currently being prepared in PR
#18360. It preserves both APIs as-shipped and adds the minimum
required compatibility surface. The cost is one ~5-line lemma vs.
modifying load-bearing hypothesis statements on either side.

If a future refactor pass wants to **upstream** the hyper version to
Mathlib (per knowledge.md § 3.3), **Option A** becomes attractive
since Mathlib's idiomatic style prefers minimal hypotheses on
publicly-named theorems.

## 7. Suggested S2 ACT signature surface (revised from knowledge.md § 4.1)

If Option C is adopted, no edit to knowledge.md § 4.1 is needed (it
already uses the Σ-pair form, which corresponds to weak `hadj_ne`).

The S2 ACT pass should additionally ship:

```lean
/-- The original `hadj_ne` (cell-disjointness) implies the hyper
form `hadj_ne_pair` (face-pair-disjointness). The converse fails:
see `Sperner.NonpureExample.mobius_band_d1` for a complex
satisfying the weak form but not the strong. -/
theorem hadj_ne_pair_of_hadj_ne {d : ℕ}
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    {s : Cell} {k : Fin (d + 1)} {s' : Cell} {k' : Fin (d + 1)}
    (h : adj s k = some (s', k')) :
    (⟨s, k⟩ : Σ _ : Cell, Fin (d + 1)) ≠ ⟨s', k'⟩
```

Total S2 ACT delta from this S1c finding: **+1 lemma (~5 LOC)** to
the file skeleton previewed in PR #18360.

## 8. Risk register

| Risk                                                   | Mitigation                                                                                                                              |
|--------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------|
| Author chooses Option A → downstream callers break.    | Pre-edit grep: `grep -rn "even_card_interior_doors\\|sperner_parity\\|exists_panchromatic" proofs/ src/` to enumerate every callsite.   |
| Author chooses Option B → hyper version loses generality without notice. | Document the regime restriction in `SpernerMathlibHyper.lean` docstring; reference this session note.                         |
| Author chooses Option C → forgets the compatibility lemma. | Adding to S2 PREP's verification checklist (PR #18360 §8) prevents this.                                                              |
| Möbius-strip witness has hidden bug (e.g., `Fin 2` swap not well-defined). | All terms verified concretely in § 3.2; no Lean construction yet, so no build risk.                                            |

## 9. Differentiation from PRs #18282, #18344, #18360

| PR     | Phase | Topic                                                                  | Overlap with this S1c? |
|--------|-------|------------------------------------------------------------------------|------------------------|
| #18282 | S1    | axioms inventory + weakening map + non-pure counter-example + S2 plan  | none — this S1c picks up where § 2.3 left off, refining "load-bearing" into "load-bearing in which form" |
| #18344 | S1b   | `IsDoorHyper top : P` parameter (definition-level correction)          | none — orthogonal hypothesis (S1b touches `IsDoorHyper`, this touches `hadj_ne`) |
| #18360 | S2 PREP | Σ-type ergonomics + file skeleton + `IsDoorHyper.specialize_to_original` bridge | low — this S1c adds **the bridge's missing compatibility lemma** for `hadj_ne`. The bridge in PR #18360 covers `IsDoorHyper ↔ IsDoor`, but does not address `hadj_ne` alignment, which is what this S1c surfaces. |

No `state.md` / `knowledge.md` / `problem.md` / `meta.json` edits
collide with any of those PRs. No edits to `proofs/Proofs/SpernerMathlib.lean`.

## 10. Anti-targets (out of scope for S1c)

- **Editing `SpernerMathlib.lean`**: any line-431 edit is an S2 ACT
  task (Option A above), not S1c.
- **Editing `knowledge.md`**: § 4.1's signature is correct as-is
  under Option C; under Option B it would change, but Option B is
  not the recommendation.
- **Constructing the Möbius-strip witness in Lean**: this is a
  potential S3 deliverable (concrete non-trivial instance of the
  hyper theorem); not load-bearing for the S2 ACT pass.
- **Per-cell vertex injectivity as a new axiom**: discussed in § 5
  as a *regime distinction*, not proposed as a new axiom.
- **Aristotle integration**: no theorem-sorries surfaced by this
  analysis.
- **`loom:review-requested` label**: math-agent policy
  (CLAUDE.md axiom-integrity), not added.

## 11. Honest scope

This file is a **doc-only S1c extension** of PR #18282's S1 OBSERVE.
It does NOT discharge any sorry, modify any Lean source, change any
`meta.json` count, or edit any other research file. The single new
file is this session note.

The finding is mathematically substantive: the strong `hadj_ne :
∀ s k s' k', adj s k = some (s', k') → s ≠ s'` in the original is
**strictly stronger than the involution argument requires**, and the
hyper version in `knowledge.md § 4.1` already uses the weaker
Σ-pair form. A concrete degenerate-vertex witness (Möbius-strip-style
single cell) demonstrates the gap. The S2 ACT pass currently being
prepared in PR #18360 needs to handle the mismatch — Option C (a
~5-line compatibility lemma) is recommended.

No race risk: this is forward-planning only and does not collide
with `state.md`, `knowledge.md`, the `*.lean` source, or any other
file touched by an open PR on this slug.

## 12. Verification log

- `grep -n "hadj_ne" proofs/Proofs/SpernerMathlib.lean` —
  confirmed the strong form is declared at line 431 and consumed
  only at line 465.
- `grep -n "hadj_ne" research/problems/sperner-mathlib-oq-01/knowledge.md` —
  confirmed the hyper form at § 4.1 lines 200–201 is the weak
  Σ-pair form.
- Lines 443/450/460 use `hadj_ne'` as a *destructured filter
  predicate*, not as the disjointness hypothesis (verified by
  inspection of context: `obtain ⟨_, hadj_ne'⟩ := hp` where
  `hp : IsDoor _ ∧ adj _ _ ≠ none` extracts the second conjunct).
- Möbius-strip witness in § 3 verified term-by-term against the
  hypothesis statements; no Lean build performed.

## 13. Estimated cost

| Phase     | This S1c | Downstream S2 ACT additions from this finding |
|-----------|----------|-----------------------------------------------|
| S1c       | doc-only (~400 LOC markdown, this file) | n/a                              |
| S2 ACT    | n/a      | +5 LOC (`hadj_ne_pair_of_hadj_ne` compatibility lemma) |
| S3        | n/a      | +30–50 LOC if Möbius-strip witness is formalised as a `def` + verification `theorem`s |

This S1c does not change the S2 ACT primary scope (hypergraph
generalisation, ~120 LOC). It identifies one additional ~5-line
deliverable.
