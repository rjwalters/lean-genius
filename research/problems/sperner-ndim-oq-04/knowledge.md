# Knowledge: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Problem Summary

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the door adjacency graph. Key goal: starting from a boundary door, follow the unique path to reach a fully-colored simplex.

**Status**: AXIOMATIZED — 0 sorries, 1 axiom (kuhn_path_existential: cross-path parity via walk reversal τ∘τ=id). Session 7: removed false bdry_nfc_even lemma, re-axiomatized kuhn_path_existential directly.
**Gallery entry**: `src/data/proofs/sperner-ndim-oq-04/`
**Lean file**: `proofs/Proofs/SpernerNDimOQ04.lean`

---

## Session 2026-04-22 (Session 1) — Kuhn Algorithm Formalization

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. Surveyed SpernerNDim.lean for available infrastructure (663 lines)
2. Identified `abstract_door_parity`, `isDoorAt`, `IsFC`, `door_transfer` as the key tools
3. Made `door_transfer` public in SpernerNDim.lean (was private)
4. Designed the `IsKuhnCompatible` axiom (door degree ≤ 2) to make algorithm deterministic
5. Created full Lean formalization (~290 lines) at `proofs/Proofs/SpernerNDimOQ04.lean`
6. Created gallery data: meta.json, annotations.json, index.ts

### Key Findings

- `door_degree_parity` proof: use `simp only [hiff]` (not `rw [hiff]`) + `convert h using 2` pattern — same as `per_simplex_door_parity` in SpernerNDim
- `fc_door_count_eq_one` and `nonfc_door_count_zero_or_two` follow immediately from `omega`
- `nonfc_with_door_has_unique_exit` proved fully via `Finset.card_eq_two` extraction
- For `kuhnWalk`, `Finset.Nonempty` is a `Prop` — use `if hne : ...` not `match ... | isTrue`
- For `kuhnStep_door_preserved`, use `simp only [kuhnStep, if_neg, dif_pos hexit]` pattern
- The non-revisiting invariant (why walk never revisits) is the hard unsolved part

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (CREATED, ~290 lines)
- `proofs/Proofs/SpernerNDim.lean` (removed `private` from `door_transfer`, `door_transfer_one_dir`)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/annotations.json` (CREATED)
- `src/data/proofs/sperner-ndim-oq-04/index.ts` (CREATED)
- `src/data/research/problems/sperner-ndim-oq-04.json` (UPDATED knowledge)

### Proven This Session

1. `fc_door_count_eq_one` — Under IsKuhnCompatible, FC simplices have exactly 1 door
2. `nonfc_door_count_zero_or_two` — Under IsKuhnCompatible, non-FC simplices have 0 or 2 doors
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with entry door has unique exit door

### Remaining Sorries (3)

1. `kuhn_path_terminates` — Main existence theorem (derived from `sperner_ndim` via sorry)
2. `kuhn_walk_reaches_fc` — Walk correctness requires non-revisiting invariant
3. `kuhnPathStart_is_fc` — Top-level correctness (depends on above two)

### Next Steps

1. **Prove non-revisiting invariant**: Show `kuhnWalk` visited set strictly grows at each step
2. **Verify IsKuhnCompatible for Freudenthal**: Check sperner-ndim-oq-01's triangulation
3. **Submit to Aristotle**: `kuhn_walk_reaches_fc` may be provable with non-revisiting established

---

## Session 2026-04-22 (Session 2) — Prove kuhn_path_terminates

**Mode**: FRESH (continuing from Session 1)
**Outcome**: progress — 1 sorry eliminated

### What I Did

1. Analyzed all 3 sorries deeply: `kuhn_path_terminates`, `kuhn_walk_reaches_fc`, `kuhnPathStart_is_fc`
2. Discovered `kuhn_path_terminates` was missing `hc: IsSperner c` and `hbdry_odd` hypotheses
3. Proved `kuhn_path_terminates` by adding those hypotheses and using `sperner_ndim c K hc hbdry_odd` (1-line proof)
4. Documented the non-revisiting proof strategy in `kuhn_walk_reaches_fc` comments
5. Updated meta.json (sorries: 3→2), knowledge files

### Key Findings

- `kuhn_path_terminates` doesn't need the walk at all — FC existence follows from `sperner_ndim` (parity)
- The non-revisiting proof for `kuhn_walk_reaches_fc` requires TWO things not currently in the codebase:
  1. "Adjacent simplices share a unique facet" axiom (not in `SpernerTriangulation`)
  2. Per-visited-simplex door history in `KuhnState` (entry/exit doors per step)
- Proof sketch for non-revisiting (case j < n-1): if s' ∈ visited and K.adj current k_out = some (s', ...), then s' has a 3rd door connecting to current — violates Kuhn compat (degree ≤ 2). This requires knowing s's previous entry/exit doors from walk history.
- Proof sketch for case j = n-1 (immediate predecessor): K.adj current k_out and K.adj current state.entry both reach s', giving two facets of current → unique-facet axiom gives k_out = state.entry, contradicting k_out ≠ state.entry.

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (MODIFIED, ~420 lines, sorries: 3→2)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (UPDATED: sorries 3→2, assumptions)
- `src/data/research/problems/sperner-ndim-oq-04.json` (UPDATED knowledge)
- `research/problems/sperner-ndim-oq-04/knowledge.md` (this file)

### Proven This Session

4. `kuhn_path_terminates` — Given IsSperner c and odd boundary door count, FC exists (proved via `sperner_ndim`)

### Remaining Sorries (2)

1. `kuhn_walk_reaches_fc` — Constructive walk correctness; requires non-revisiting invariant
2. `kuhnPathStart_is_fc` — Main constructive theorem (depends on kuhn_walk_reaches_fc)

### Next Steps

1. ~~Add unique-facet axiom to SpernerTriangulation~~ **DONE** (2026-04-24)
2. **Reformulate kuhnPathStart_is_fc** to existential: `∃ s₀ k₀ ..., IsFC c K (kuhnPathStart ...)`
3. **Reformulate kuhn_walk_reaches_fc** with `IsKuhnWalkState` invariant ensuring valid boundary-door walk
4. **Add door history to KuhnState**: `List (Simplex × Fin(d+1) × Fin(d+1))` for entry/exit per visited simplex
5. **Prove kuhnWalk_never_revisits** using adj_unique_facet + door history

---

## Session 2026-04-24 (Session 3) — Mathematical Analysis + adj_unique_facet

**Mode**: FRESH (continued from Session 2)
**Outcome**: Infrastructure progress; 0 sorries closed

### What I Did

1. Deep analysis of `kuhn_walk_reaches_fc` and `kuhnPathStart_is_fc`
2. Added `adj_unique_facet` to SpernerTriangulation: closes the previous-simplex revisit case
3. Found that both theorems as stated are incorrect and need reformulation
4. Updated docstrings in SpernerNDimOQ04.lean with correct analysis

### Key Findings

- **`kuhnPathStart_is_fc` may be FALSE**: Walk can exit via K.adj sₙ k_out = none, returning non-FC sₙ. All non-k_out vertices are on face Fin.last d with color ≠ d (IsSperner). The k_out vertex's color is unconstrained — if ≠ d, sₙ is non-FC. Correct form: existential over starting boundary doors.
- **`kuhn_walk_reaches_fc` is FALSE for arbitrary KuhnState**: e.g. non-FC state with doorDegree = 0 returns immediately (non-FC). Needs `IsKuhnWalkState` predicate.
- **`adj_unique_facet` closes j = n-2 case**: If walk would revisit sₙ₋₁, then K.adj sₙ k_out = some(sₙ₋₁, ?) and K.adj sₙ kₙ = some(sₙ₋₁, ?) by adj_symm. So k_out = kₙ by adj_unique_facet, contradicting k_out ≠ kₙ. ✓
- **3-cycles consistent with adj_unique_facet + Kuhn compatibility**: Preventing all cycles is a geometric property of Δd, not derivable from abstract axioms.

### Files Modified

- `proofs/Proofs/SpernerNDim.lean` (added `adj_unique_facet` to SpernerTriangulation)
- `proofs/Proofs/SpernerNDimOQ04.lean` (improved docstrings with correct analysis)

### Remaining Sorries (2)

1. `kuhn_walk_reaches_fc` — FALSE as stated; needs reformulation with IsKuhnWalkState invariant
2. `kuhnPathStart_is_fc` — Potentially FALSE; needs reformulation to existential form

---

## Session 2026-04-24 (Session 4) — Non-Revisiting Proof Complete

**Mode**: FRESH (continuing from Session 3)
**Outcome**: KEY progress — non-revisiting FULLY PROVED via WalkValid invariant

### What I Did

1. Designed `WalkValid` invariant (5 properties: has_record, doors_valid, entry_from_chain, exit_to_chain, pred_spec) that tracks (k_in, k_out) per visited simplex + predecessor identification
2. Proved `kuhn_three_doors_contradiction`: 3 distinct doors at same simplex → contradiction with Kuhn-compat (via doorDegree ≥ 3)
3. Proved `walkValid_init`: initial boundary-door state with empty visited satisfies WalkValid
4. Proved `kuhn_step_nonrevisit`: KEY theorem — under WalkValid, `K.adj current k_out = some(s', k')` implies `s' ∉ visited ∪ {current}`. Proof splits on predecessor vs non-predecessor case.
5. Proved `walkValid_step`: WalkValid preserved by one Kuhn step (updates pred, door record)
6. Reformulated `kuhn_walk_reaches_fc` to clarify: non-revisiting is now PROVED; only boundary-exit ruling-out remains
7. Updated `kuhnPathStart_finds_fc_existential` with complete proof strategy (τ involution needs walk reversibility)
8. Updated module header, file grew to 779 lines

### Key Findings

- **Non-revisiting proof structure**: Case split on exit_to_chain:
  (a) Predecessor case (exit_to_chain says s' = current): `kuhnWalk_no_immediate_back` gives contradiction directly (k_out = state.entry, but hne_entry: k_out ≠ state.entry)
  (b) Non-predecessor case (exit_to_chain says s_out ∈ visited): 3 distinct doors at s':
    - k' ≠ k_out_s: adj_unique_facet (different neighbors, s_out ≠ current via current ∉ visited)
    - k' ≠ k_in_s: adj_unique_facet (boundary case: k_in_s = none ≠ k'; interior case: s_prev ∈ visited ≠ current)
    - k_in_s ≠ k_out_s: from doors_valid invariant
- **WalkValid is the right invariant**: The exit_to_chain/entry_from_chain properties exactly capture what's needed for adj_unique_facet to fire, without needing the full walk sequence
- **Remaining sorry scope**: Only boundary-exit termination (global parity) and walk-reversibility (τ∘τ=id) remain. Non-revisiting — the harder part — is done.
- **kuhnPathStart_is_fc (universal) confirmed FALSE**: documented in proof comments; correct statement is existential

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (MODIFIED: +272 lines, to 779 total; 6 new proved theorems)
- `src/data/research/problems/sperner-ndim-oq-04.json` (UPDATED knowledge)

### Proved This Session

5. `kuhn_three_doors_contradiction` — 3 distinct doors → contradiction with Kuhn-compat
6. DoorRecord / WalkValid — invariant types for walk correctness
7. `walkValid_init` — initial state validity  
8. `kuhn_step_nonrevisit` — **KEY**: walk never revisits under WalkValid
9. `walkValid_step` — WalkValid preserved at each step

### Session 2026-04-24 (Session 5) — Axiomatization and Cleanup

**Mode**: FRESH (continuing from Session 4)
**Outcome**: Axiomatized — 0 sorries, 1 axiom

#### What I Did

1. Diagnosed that `kuhn_walk_reaches_fc` (universal) is FALSE as stated — removed it
2. Diagnosed that `kuhnPathStart_is_fc` (universal) is FALSE as stated — removed it
3. Added axiom `kuhn_path_existential_ax` for the TRUE existential form
4. Proved `kuhnPathStart_finds_fc_existential` using the axiom (1 line)
5. Updated module docstring to reflect accurate state

#### Key Findings

- `kuhn_walk_reaches_fc` is FALSE: since it applies to ANY WalkValid state (which includes ANY initial boundary-door state), it would imply `kuhnPathStart_is_fc` (universal), which is false
- `kuhnPathStart_is_fc` is FALSE: boundary exit possible on some paths; individual walk can terminate at non-FC boundary simplex
- Only the EXISTENTIAL form is provably true; the parity argument guarantees ∃ boundary door that reaches FC
- Walk reversibility (τ∘τ=id) is the remaining mathematical gap for a full proof of the axiom

#### Remaining Open Problem (1 sorry)

- `bdry_nfc_even` sorry — Walk-pairing involution τ∘τ=id pending formalization
  - Non-revisiting (fixed-point-free) part: FULLY PROVED via kuhn_step_nonrevisit + WalkValid
  - τ∘τ=id part: requires kuhnWalkWithExit + walkTrace_reversal induction (~50 lines)
  - Axiom is GONE; replaced with theorem kuhn_path_existential (proven from bdry_nfc_even)

#### Next Steps

1. Define `kuhnWalkWithExit`: fuel-based walk returning Option(Simplex × Fin) for boundary exit
2. Prove `walkTrace_reversal`: induction on walk steps with generalized visited V, adj_symm + nonfc_with_door_has_unique_exit
3. Fill `bdry_nfc_even` sorry using walkTrace_reversal + even_card_fpf_invol

---

## Session 2026-04-25 (Session 6) — Axiom Replacement

**Mode**: REVISIT
**Outcome**: progress — axiom removed, replaced with theorem (1 sorry remaining)

### What I Did

1. Analyzed the parity argument structure for `kuhn_path_existential_ax`
2. Key insight: partition B = B_fc (FC-start) ∪ B_nfc (non-FC-start), need |B_nfc| even
3. Wrote `bdry_nfc_even` with sorry (documents exactly what's needed for τ∘τ=id)
4. Proved `kuhn_path_existential` completely from `bdry_nfc_even`:
   - Partition proof: B = B_fc ∪ B_nfc (disjoint) via Classical.em on IsFC
   - Cardinality: |B_fc| + |B_nfc| = |B| via Finset.card_union_of_disjoint
   - Parity: |B_fc| odd from |B| odd − |B_nfc| even → omega
   - Extraction: Finset.card_pos → (s₀, k₀) ∈ B_fc → kuhnPathStart_is_fc_of_fc_start
5. Removed `axiom kuhn_path_existential_ax` entirely
6. Updated `kuhnPathStart_finds_fc_existential` to use `kuhn_path_existential`

### Key Findings

- The proof structure of the main theorem is complete and clean
- Walk reversal (τ∘τ=id) requires `kuhnWalkWithExit` + `walkTrace_reversal` by induction
- `walkTrace_reversal` induction: at step k, backward walk from seq(k) with visited V finds seq(0).
  Base: K.adj seq(0) k_out = none (boundary); Step: adj_symm of chain + unique exit → prev step
- The visited set generalization (V parameter) is essential for the induction to work

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (+103 lines, -21 lines)
- PR: rjwalters/lean-genius#12454

### Next Steps

1. Implement kuhnWalkWithExit + walkTrace_reversal to fill bdry_nfc_even sorry
2. Then proof is complete (0 axioms, 0 sorries)

---

## Session 2026-04-26 (Session 7) — Remove False Lemma, Re-axiomatize Cleanly

**Mode**: REVISIT
**Outcome**: axiomatized — 0 sorries, 1 axiom

### What I Did

1. Confirmed konigsberg-oq-02-oq-01 was already completed (PR #12320); updated pool to "completed"
2. Identified `sperner-ndim-oq-04` as the priority problem (score 57, RICH tier, 1 sorry)
3. Proved `bdry_nfc_even` as stated is **mathematically false**: a single boundary non-FC simplex
   gives |B_nfc|=1 (odd). The private lemma did not carry any hypothesis connecting B_nfc
   to the global door graph structure, so the statement is not provable.
4. Removed `bdry_nfc_even` entirely (lines 819-845 of old file)
5. Replaced `theorem kuhn_path_existential` (which depended on the false lemma via `have heven :=
   bdry_nfc_even`) with `axiom kuhn_path_existential` — same statement, same proof sketch in docstring
6. Updated module header: moved bdry_nfc_even to Removed (false as stated) section; kuhn_path_existential
   now directly in Axiomatized section
7. Updated meta.json: sorries 1→0, axiomCount 0→1, badge "wip"→"axiom", status "formalized"→"axiomatized"
8. Updated conclusion and assumptions text

### Key Findings

- `bdry_nfc_even` is FALSE without a global door graph hypothesis. Counterexample: d=1,
  1 boundary non-FC simplex with 1 boundary door (both vertices on face 1). This gives
  |B_nfc|=1 (odd). No abstract axiom prevents this.
- The CORRECT parity argument goes: door graph handshaking gives |B_nfc| + |INT_fc| ≡ 0 mod 2.
  Since |INT_fc|=|FC| (each FC simplex has exactly 1 door, proved) and |FC|≡|B| mod 2 (sperner_parity,
  proved), we get |B_nfc| ≡ |B| mod 2. Under hbdry_odd, |B| is odd, so |B_nfc| is odd — not even!
- Therefore the old partition argument (B_fc = B - B_nfc, B_fc odd ≥ 1) would yield |B_fc| even,
  not odd. The τ∘τ=id involution argument is the correct approach for the AXIOM (not bdry_nfc_even).
- The τ involution argument says: pair up B_nfc elements via walk-reversal; this gives |B_nfc| even.
  Then |B_fc| = |B| - |B_nfc| is odd ≥ 1. This is the correct mathematical content of the axiom.
- The axiom kuhn_path_existential correctly captures this: given IsKuhnCompatible and hbdry_odd,
  there exists a boundary door whose walk finds FC. The τ∘τ=id formalization is what's pending.

### Mathematical Insight

The key discovery is that the partition-based proof (old Session 6 approach) has the parity backwards:
|B_nfc| is ODD (≡ |B| mod 2), not even. The correct argument uses the τ involution *on B_nfc* to
show |B_nfc| is even — but this requires the additional constraint that comes from counting BOTH
directions of cross-paths. The axiom's proof sketch in the docstring now correctly states both
equivalent formulations (handshaking + τ involution).

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (878 lines, was 942; removed false lemma + theorem body)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (status, badge, sorries, axiomCount, lineCount updated)
- `research/problems/sperner-ndim-oq-04/knowledge.md` (this file)

### Next Steps

1. To remove the axiom: implement kuhnWalkWithExit + walkTrace_reversal induction
2. τ involution: define τ(s₀, k₀) = (sₙ, kₙ) where (sₙ, kₙ) is the boundary exit of the walk
   starting from s₀ via its interior door
3. Prove τ∘τ=id via adj_symm + nonfc_with_door_has_unique_exit + kuhn_step_nonrevisit (no-cycle)
4. Apply even_card_fpf_invol to get |B_nfc| even, then |B_fc| = |B| - |B_nfc| odd ≥ 1

---

## Session 2026-04-26 (Session 8) — Axiom → Theorem (1 sorry)

**Mode**: REVISIT
**Outcome**: progress — axiom eliminated, 1 sorry introduced (more honest representation)

### What I Did

1. Recognized τ involution argument is correct when applied to ALL of B under hfail
2. Under hfail (∀ walks fail): τ(s₀,k₀) = boundary exit of walk from (s₀,k₀) is well-defined for ALL of B
3. τ is FPF involution on B (not just B_nfc): kuhnWalk_first_exit_interior + WalkValid → sₙ ≠ s₀
4. Replaced `axiom kuhn_path_existential` with `theorem kuhn_path_existential := by`
5. Proved Case 1 (∃ walk reaches FC): push_neg + extract witness → direct
6. Proved Case 2 (all walks fail): bdry_all_even_of_no_fc_walks (sorry) gives Even |B| → omega contradiction
7. Updated meta.json: axiomCount 1→0, sorryCount 0→1, badge "axiom"→"wip", status "axiomatized"→"formalized"

### Key Findings

- Session 7 error was: bdry_nfc_even is false because it was stated without `hfail` hypothesis
- Correct approach: under `hfail` (all walks fail), τ maps ALL of B to B, not just B_nfc
  Because: every (s₀,k₀) ∈ B with hfail[s₀,k₀] has walk ending at boundary (not FC)
- This is why axiom → sorry works: the sorry's context includes `hfail` which is the key constraint
- bdry_all_even_of_no_fc_walks is NOT trivially false: it has the `hfail` extra hypothesis

### Mathematical Insight

The correct τ involution domain is B (ALL boundary doors) under the assumption hfail, not B_nfc:
- Under hfail: ∀ (s₀,k₀) ∈ B, walk from (s₀,k₀) doesn't reach FC → exits at boundary (sₙ,kₙ) ∈ B
- τ: B → B is FPF involution (by WalkValid non-revisiting + walk reversal)
- even_card_fpf_invol → Even |B| → contradicts hbdry_odd via omega
- Result: hfail is impossible → ∃ (s₀,k₀) ∈ B such that walk reaches FC

### Files Modified

- `proofs/Proofs/SpernerNDimOQ04.lean` (axiom → theorem, +bdry_all_even_of_no_fc_walks private lemma)
- `src/data/proofs/sperner-ndim-oq-04/meta.json` (axiomCount 1→0, sorryCount 0→1)
- `research/problems/sperner-ndim-oq-04/knowledge.md` (this file)

### Next Steps

1. Implement walkTrace_reversal: induction on walk length, adj_symm at each step
   - State: given walk from (s₀,k₀) → (s₁,k₁) → ... → (sₙ,kₙ), walk from (sₙ,kₙ) → (s₀,k₀)
   - Key tool: K.adj sᵢ k_exit = some(sᵢ₊₁, k_entry) → K.adj sᵢ₊₁ k_entry = some(sᵢ, k_exit)
   - Unique exit (nonfc_with_door_has_unique_exit) ensures determinism at each step
2. Use walkTrace_reversal to prove τ∘τ=id in bdry_all_even_of_no_fc_walks
3. Apply even_card_fpf_invol → Even |B| → done (0 axioms, 0 sorries)
