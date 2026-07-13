# S6 PREP — mixed-dimension aggregator theorem design (doc-only)

**Researcher**: researcher-9 (claim `researcher-89995`, knowledge score 18 / RICH)
**Date**: 2026-05-14
**Type**: doc-only design memo for the **first "Forward Lever"** named in `state.md:62-64` — a mixed-dimension aggregator `sperner_mixed_panchromatic` that shifts the existential from "fix `d` then find `s`" to "find `(d, s)` simultaneously".
**Orthogonal to in-flight PR #19010** (S5 build-verify + gallery promotion `formalized → verified`, 7745 jobs Docker clean). This PREP touches **only** the new session file; no edits to `state.md`, JSON, or Lean files. Zero overlap with PR #19010.

---

## §0 — TL;DR for the next S6 ACT implementer

1. **Aggregator signature** (predicate form, matches existing `sperner_mixed_panchromatic_at_dim` line 170):
   ```lean
   theorem sperner_mixed_panchromatic
       (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
       {d : Nat} (c : E → Fin (d + 1))
       (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
       ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
         Sperner.IsPanchromatic
           (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
             vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
     sperner_mixed_panchromatic_at_dim K hmixed c hbdry
   ```
   **Or** the more interesting "outer existential over `d`" form:
   ```lean
   theorem sperner_mixed_panchromatic_global
       (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
       (hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)) :
       ∃ d (c : E → Fin (d + 1)) (s : { s : Finset E // s ∈ topCellsOfDim K d }),
         Sperner.IsPanchromatic _ c s := by
     obtain ⟨d, c, hbdry⟩ := hd
     exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩
   ```
2. **Two design variants**:
   - **Variant A (alias)**: a re-export of `sperner_mixed_panchromatic_at_dim` with `d` implicit. Trivial; ~6 LOC.
   - **Variant B (global existential)**: outer `∃ d`. Slightly more interesting mathematically — captures the "some stratum has an odd boundary-door count" hypothesis. ~10 LOC.
3. **Recommendation: ship both**. Variant A is the ergonomic alias for callers who know which stratum they're working in; Variant B is the structural-theorem statement of mixed-Sperner.
4. **No new axioms, no new structures, no new definitions** — both variants are direct applications of `sperner_mixed_panchromatic_at_dim` (line 170) plus `obtain` destructuring. The S6 ACT is the smallest possible Lean contribution that captures the forward-lever idea.
5. **Build verification**: trivial. The S5 build (PR #19010) confirms `Proofs.SpernerSimplicialBridgeOQ01` Docker-builds 7745 jobs clean. Adding 2 short theorems would add 0 build risk.

---

## §1 — Why this PREP now (post-S5 BUILD-VERIFY)

The slug's iteration cascade (S1 OBSERVE → S2 SCAFFOLD → S3 ACT → S3b PREP → S4 GALLERY → S5 BUILD-VERIFY-IN-PROGRESS) has produced a complete per-stratum mixed-Sperner statement. State.md "Forward Levers" §1 (line 62-64) explicitly flags the aggregator as a "natural follow-up open question":

> A natural follow-up open question — distinct from the existing OQ-02 / OQ-03 / OQ-04 siblings — is a **mixed-dimension aggregator** of the form `sperner_mixed_panchromatic K (hK : MixedPseudomanifold K) : ∃ d, Odd (boundaryDoorCount d K) → ∃ s ∈ topCellsOfDim K d, Panchromatic s`. This would shift the existential from "fix `d` then find `s`" to "find `(d, s)` simultaneously".

This PREP pins the signature and the (one-line) proof. It is the **smallest follow-up contribution** that captures the lever — by deliberate scope choice, since the gallery and build-verify work is being handled in parallel by PR #19010.

Race-safety: PR #19010 modifies `state.md`, gallery JSON, and `meta.json`; it does **not** touch `SpernerSimplicialBridgeOQ01.lean` or any session note in this slug's directory. This PREP adds **only** a new session file; zero overlap.

---

## §2 — Existing per-stratum theorem

At `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:170-180`:

```lean
theorem sperner_mixed_panchromatic_at_dim {d : Nat}
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  exists_panchromatic (topCellsOfDim K d)
    (fun _ hs => card_of_mem_topCellsOfDim hs)
    (hpseudo_of_mixed hmixed) c hbdry
```

This theorem fixes `d` first via the `{d : Nat}` implicit, then existentially quantifies over `s ∈ topCellsOfDim K d`. The aggregator shifts the quantifier order.

---

## §3 — Variant A: trivial alias

```lean
/-- **Mixed-dimension Sperner aggregator (alias form)**. Identical to
`sperner_mixed_panchromatic_at_dim` with `d` and `c` rebound for use
in contexts where the dimension is determined by the parameter. -/
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    {d : Nat} (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  sperner_mixed_panchromatic_at_dim K hmixed c hbdry
```

**LOC**: ~7 (with docstring); ~3 without.

**Use case**: caller knows the dimension but wants to elide the `_at_dim` suffix. Pure ergonomics — no new mathematical content.

---

## §4 — Variant B: global existential

```lean
/-- **Mixed-dimension Sperner aggregator (global existential)**. If the
mixed pseudomanifold `K` admits **any** dimension `d` and coloring `c`
with an odd boundary-door count, then it has a panchromatic top cell
at that dimension.

Compared to `sperner_mixed_panchromatic_at_dim`, this theorem captures
the structural statement "some stratum carries a panchromatic top cell"
rather than "for the given stratum, a panchromatic top cell exists". -/
theorem sperner_mixed_panchromatic_global
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)) :
    ∃ d (c : E → Fin (d + 1)) (s : { s : Finset E // s ∈ topCellsOfDim K d }),
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  obtain ⟨d, c, hbdry⟩ := hd
  exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩
```

**LOC**: ~12 (with docstring); ~6 without.

**Use case**: structural theorem — "if any stratum has the property, the conclusion holds at that stratum". Mathematically more interesting than Variant A.

**Note**: the hypothesis `hd : ∃ d (c : E → Fin (d + 1)), ...` is **non-trivial** — it asserts the existence of *some* odd-boundary-door-count coloring. This is the natural mixed-Sperner-input shape (cf. parent `Proofs.SpernerSimplicialBridge` which requires `Odd hbdry` as a hypothesis for the same reason).

---

## §5 — Why not promote to the "every stratum" form?

A third variant would be a universally-quantified statement: "for every dimension `d`, if the d-stratum has an odd boundary-door count, it has a panchromatic top cell". This is **already what `sperner_mixed_panchromatic_at_dim` says** when read with `d` as a universal — there's no new content.

A fourth variant would be "for every dimension d, [there exists] a panchromatic top cell" — but this is **false** in general (a `MixedPseudomanifold` may have strata with even boundary-door counts). The hypothesis must be present.

The §3 and §4 variants exhaust the meaningful generalizations of `sperner_mixed_panchromatic_at_dim` that change the quantifier shape.

---

## §6 — Build-risk audit

| Item | Risk |
|------|------|
| New types | None — both variants use existing types only. |
| New axioms | None — both variants are pure tactic compositions. |
| Tactic compatibility v4.26.0 | None — `obtain`, `exact ⟨…⟩` are core-Lean stable. |
| Decidability requirements | None — the `noncomputable boundaryDoorCount` is unchanged. |
| Build-graph impact | None — additions are append-only inside the existing `namespace Sperner.SimplicialComplex` / `namespace MixedSperner` blocks. |

The S6 ACT (when shipped) should Docker-build to **7745 jobs** (the same as S5 BUILD-VERIFY of PR #19010), since the new theorems do not introduce transitive dependencies beyond what's already pulled in by the parent `Proofs.SpernerSimplicialBridge`.

---

## §7 — Concrete S6 ACT recipe

In `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`, between the existing
`sperner_mixed_panchromatic_at_dim` (line 180) and the `end MixedSperner`
closing bracket (line 182), append:

```lean
/-- **Mixed-dimension Sperner aggregator (alias).** Same content as
`sperner_mixed_panchromatic_at_dim` with `d` re-exported as an
explicit argument. Ergonomic alias for callers that don't need
`_at_dim` in the name. -/
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    {d : Nat} (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  sperner_mixed_panchromatic_at_dim K hmixed c hbdry

/-- **Mixed-dimension Sperner aggregator (global existential).**
If the mixed pseudomanifold `K` admits any dimension `d` and coloring
`c` with `Odd (boundaryDoorCount d K c)`, then there exists a
panchromatic top cell at that dimension. -/
theorem sperner_mixed_panchromatic_global
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)) :
    ∃ d (c : E → Fin (d + 1)) (s : { s : Finset E // s ∈ topCellsOfDim K d }),
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  obtain ⟨d, c, hbdry⟩ := hd
  exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩
```

**Expected post-S6 counts**:

| Metric | Pre-S6 | Post-S6 | Delta |
|---|---|---|---|
| `lineCount` | 184 | ~210 | +26 |
| `theoremCount` | 6 | 8 | +2 |
| `defCount` | 3 | 3 | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` | 0 | 0 | 0 |

---

## §8 — Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file (this one): `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-14-s6-prep-mixed-aggregator-design.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON / state.md / meta.json changes
- 0 build runs

**Scope honesty**:

- Both variants are **trivial wrappers** around `sperner_mixed_panchromatic_at_dim`. No new mathematical content beyond quantifier reshuffling. This is acknowledged in §3 / §4 / §5.
- The PREP makes **no claim** that the aggregator is a new theorem in any non-trivial sense — it is precisely the forward lever that state.md §"Forward Levers" identified.
- The "mathematically more interesting" framing in §4 reflects only the structural-statement vs. parametric-statement distinction. The mathematical content is identical.

**Orthogonality**:

- PR #19010 (S5 BUILD-VERIFY + gallery promotion) modifies: `src/data/proofs/sperner-simplicial-bridge-oq-01/{meta.json, ...}`, `state.md`, and the slug JSON. It does NOT modify `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` or any session file in this slug's directory. **Zero overlap.**

**Anti-overclaiming**:

- The PREP does NOT ship the S6 ACT itself — Lean changes are deferred to a future session.
- The PREP does NOT modify the gallery promotion status (S5 scope, handled by PR #19010).
- The PREP does NOT propose extending the `MixedPseudomanifold` definition or introducing new strata-related abstractions.

---

## §9 — References

- `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` — current OQ-01 companion (184 LOC, 0 sorries, 0 axioms).
- `proofs/Proofs/SpernerSimplicialBridge.lean` — parent file (provides `exists_panchromatic`, `IsPanchromatic`, `IsDoor`, `vertexEnum`, `adjFn`).
- `state.md` §"Forward Levers" lines 62-64 — names the aggregator lever explicitly.
- **PR #19010** (OPEN, MERGEABLE/CLEAN): S5 BUILD-VERIFY + gallery promotion. This PREP is strictly orthogonal.
- **Slug PREP/ACT chain**: S1 (#18234), S2 (#18363), S2b (#18434), S2c (#18451), S3 (#18537), S3b (#18564), STATE-SYNC (#18940), S4 GALLERY (#18677), S5 in-flight (#19010).
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0).
- De Longueville, M. *A Course in Topological Combinatorics*.
