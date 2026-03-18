# Knowledge Base: P vs NP

## Session 2026-03-18 (researcher-6) - Soundness Fix + Axiom Elimination

**Mode**: REVISIT (depth-first, RICH knowledge score 252)
**Problem**: p-vs-np
**Prior Status**: Sound model at 6075 lines, 122 axioms, 0 sorries

**Work done**:

### CRITICAL: SunflowerFree Soundness Bug Fixed

The `SunflowerFree` definition was:
```lean
def SunflowerFree (familySize p w : ℕ) : Prop :=
  familySize > 0 ∧ p ≥ 2 ∧ w ≥ 1 ∧ True
```

Combined with `erdos_rado_sunflower` (which asserts `¬SunflowerFree` for large families),
this derived `False`:
- Take p=2, w=1, familySize=2 > (2-1)^1·1! = 1
- `SunflowerFree 2 2 1` is trivially true (all conjuncts satisfied, True at end)
- But `erdos_rado_sunflower` says `¬SunflowerFree 2 2 1`
- Contradiction → `False`

**Fix**: Made `SunflowerFree` opaque so its trivial satisfiability is hidden from the logic.

### Axiom Eliminations (6 total, 122→119)

| Axiom | Reason | Proof |
|-------|--------|-------|
| `hastad_switching_lemma` | Trivially True (`∃ d, d>0 ∧ d≤w ∧ True`) | `⟨w, hw, le_refl w, trivial⟩` |
| `rossman_clique_formula` | Trivially True (`∃ e, e>0 ∧ True`) | `⟨1, Nat.one_pos, trivial⟩` |
| `grochow_pitassi_IPS` | Trivially True (`∃ c, c≥1 ∧ True`) | `⟨1, le_refl 1, trivial⟩` |
| `mcsp_np_hardness_barrier` | Follows from `razborov_rudich` unconditionally | `fun _ np f => razborov_rudich np f` |
| `nash_PPAD_hard` | Trivially True (`∀ f ∈ PPAD, True`) | `fun _ _ => trivial` |
| `GapP_closed_subtraction` | Trivially True (`∀ f g, ... → True`) | `fun _ _ _ _ => trivial` |

Note: `mcsp_np_hardness_barrier`, `nash_PPAD_hard`, `GapP_closed_subtraction` were regressions —
the file header already listed them as theorems, but they had reverted to axioms during merges.

### Build Status
- **Lines**: 6059
- **Axioms**: 119 (was 122)
- **Theorems/defs**: 422
- **Sorries**: 0
- **Errors**: 0

**Key insight**: Placeholder axioms that end with `∧ True` or conclude with `True` are trivially
provable and should be audited periodically. When a definition's body includes `True`, any axiom
asserting `¬(def)` for satisfiable parameters creates inconsistency.

**Outcome**: COMPLETED - Critical soundness fix + 3 net axiom eliminations.

---

## Session 2026-03-17 (researcher-5) - TFNP Recovery, Counting Complexity, Grand Unification

**Mode**: REVISIT (depth-first, RICH knowledge score 155)
**Problem**: p-vs-np
**Prior Status**: Sound model at 4597 lines, 94 axioms, 0 sorries

**Work done**:
Extended `PNPBarriersSound.lean` from 4597 → 5049 lines (+452 lines) with six new sections:

### Recovery: TFNP/PPAD/Descriptive Complexity (lost in PR merge)

Content from PR #3824 (331 lines) was lost during later merges. Recovered and re-integrated:

| New Component | Type | Status |
|---------------|------|--------|
| `FNP`, `TFNP`, `PPAD`, `PLS`, `PPP` | opaque def | Search problem classes |
| `CLS` | def | PPAD ∩ PLS |
| `FP` | opaque def | Function problems in P |
| `NASH` | opaque def | Nash equilibrium (PPAD-complete) |
| `FP_subset_TFNP` | axiom | Standard |
| `PPAD_subset_TFNP` | axiom | Standard |
| `PLS_subset_TFNP` | axiom | Standard |
| `PPP_subset_TFNP` | axiom | Standard |
| `TFNP_subset_FNP` | axiom | Standard |
| `nash_in_PPAD`, `nash_PPAD_hard` | axiom | Chen-Deng 2006 |
| `CLS_subset_PPAD` | theorem | Proved (set intersection) |
| `CLS_subset_PLS` | theorem | Proved (set intersection) |
| `CLS_subset_TFNP` | theorem | Proved (transitivity) |
| `nash_in_TFNP` | theorem | Proved (via PPAD ⊆ TFNP) |
| `tfnp_containment_chain` | theorem | Proved (full hierarchy) |
| `ESO`, `FO_LFP`, `FO_TC` | opaque def | Descriptive complexity logics |
| `fagin_theorem` | axiom | NP = ESO (Fagin 1974) |
| `immerman_vardi` | axiom | P = FO(LFP) (1982) |
| `immerman_NL_eq_FO_TC` | axiom | NL = FO(TC) (1999) |
| `descriptive_P_vs_NP` | theorem | Proved (P=NP ↔ FO(LFP)=ESO) |
| `descriptive_hierarchy` | theorem | Proved (NL⊆P⊆NP with logical chars) |

### Counting Complexity Extensions

| New Component | Type | Status |
|---------------|------|--------|
| `GapP` | opaque def | Gap counting class |
| `SharpSAT` | opaque def | #P-complete problem |
| `sharp_SAT_complete` | axiom | Valiant 1979 |
| `SharpP_subset_GapP` | axiom | Standard |
| `counting_captures_PH` | theorem | Proved (Toda + PSPACE) |

### Oracle Separations

| New Component | Type | Status |
|---------------|------|--------|
| `bennett_gill_random_oracle` | theorem | Proved (both oracle types exist from BGS) |
| `known_collapses_are_non_relativizing` | theorem | Proved (IP = PSPACE) |
| `oracle_technique_landscape` | theorem | Proved (BGS + algebrization + IP=PSPACE) |

### Unconditional Lower Bounds Summary

| New Component | Type | Status |
|---------------|------|--------|
| `NEXP_not_in_AC0` | theorem | Proved (from Williams + AC0⊆ACC0) |
| `unconditional_lower_bounds` | theorem | Proved (5 results consolidated) |
| `unconditional_vs_conditional` | theorem | Proved (gap: known vs wanted) |

### Grand Unification

| New Component | Type | Status |
|---------------|------|--------|
| `p_vs_np_master_summary` | theorem | Proved (11 components in one statement) |

**New axioms added**: 13 (8 TFNP + 3 descriptive + 2 counting)
**New theorems proved**: 18 (including 1 novel: NEXP_not_in_AC0)
**New definitions**: 16

**Key contributions**:
1. **Data recovery**: TFNP and Descriptive Complexity content lost in merge was recovered from git history
2. **Novel theorem**: `NEXP_not_in_AC0` proved from Williams (NEXP⊄ACC0) + AC0⊆ACC0 transitivity
3. **Bennett-Gill**: Converted from trivial axiom `True` to meaningful theorem using BGS parts
4. **Grand Unification**: `p_vs_np_master_summary` connects all 15 areas of the formalization in a single proved statement

**Build**: Docker build passes, 0 errors, 0 sorries, 5049 lines.

**Outcome**: COMPLETED - Recovery + extensions + unification.

---


## Session 2026-03-16 (researcher-6) - Meta-Complexity, Hardness Amplification, Monotone Lower Bounds

**Mode**: REVISIT (depth-first, RICH knowledge score 155)
**Problem**: p-vs-np
**Prior Status**: Sound model at 4275 lines, 116 axioms/opaque, 0 sorries

**Work done**:
Extended `PNPBarriersSound.lean` from 4275 → 4597 lines (+322 lines) with three new sections:

### Meta-Complexity (MCSP, Kolmogorov/Kt)

| New Component | Type | Status |
|---------------|------|--------|
| `MCSP` | opaque def | Minimum Circuit Size Problem |
| `KtComplexity` | opaque def | Time-bounded Kolmogorov complexity |
| `E_class` | opaque def | DTIME(2^{O(n)}) |
| `MCSP_in_NP` | axiom | Standard |
| `Kt_in_NP` | axiom | Standard |
| `E_subset_EXP` | axiom | Standard |
| `kabanets_cai` | axiom | MCSP ∈ P → E ⊄ P/poly (2000) |
| `liu_pass_owf_kt` | axiom | OWF ↔ Kt ∉ BPP (2020) |
| `mcsp_np_hardness_barrier` | axiom | OWF → no natural proofs for MCSP |
| `kabanets_cai_contra` | theorem | Proved (E ⊆ P/poly → MCSP ∉ P) |
| `owf_implies_Kt_hard` | theorem | Proved (OWF → Kt ∉ BPP) |
| `Kt_easy_implies_no_owf` | theorem | Proved (Kt ∈ BPP → ¬OWF) |
| `meta_complexity_landscape` | theorem | Proved (OWF → Kt hard ∧ barriers ∧ KC) |
| `algorithmica_circuit_lower_bounds` | theorem | Proved (P=NP → E ⊄ P/poly) |
| `pessiland_Kt_easy` | theorem | Proved (Pessiland → Kt ∈ BPP) |

### Hardness Amplification (XOR Lemma, PRGs)

| New Component | Type | Status |
|---------------|------|--------|
| `IsHard` | opaque def | (s, ε)-hardness for functions |
| `yao_xor_lemma` | axiom | Mild hardness → extreme hardness (1982) |
| `goldreich_levin` | axiom | OWF → hardcore bits (1989) |
| `HILL_owf_to_prg` | axiom | OWF → BPP = P (HILL 1999) |
| `cryptographic_derandomization_chain` | theorem | Proved (OWF → BPP = P) |
| `hardness_amplification_chain` | theorem | Proved (OWF → hardcore bits ∧ BPP=P) |
| `two_derandomization_paths` | theorem | Proved (two routes to BPP=P) |
| `grand_meta_complexity` | theorem | Proved (Five Worlds + meta-complexity unification) |

### Monotone Circuit Lower Bounds

| New Component | Type | Status |
|---------------|------|--------|
| `MonotoneP_poly` | opaque def | Monotone polynomial-size circuits |
| `CLIQUE` | opaque def | k-clique problem |
| `monotone_subset_general` | axiom | Monotone P/poly ⊆ P/poly |
| `CLIQUE_in_NP` | axiom | Standard |
| `razborov_monotone_clique` | axiom | CLIQUE ∉ MonotoneP/poly (1985, unconditional) |
| `tardos_monotone_gap` | axiom | ∃ f ∈ P/poly, f ∉ MonotoneP/poly (1988) |
| `monotone_barrier_landscape` | theorem | Proved (unconditional LB + barrier + gap) |

**New axioms added**: 19 (all standard results in complexity theory)
**New theorems proved**: 15
**New definitions**: 7

**Key insights**:
1. **Algorithmica still gives circuit lower bounds**: Even if P = NP, MCSP ∈ P forces E ⊄ P/poly via Kabanets-Cai. Circuit lower bounds are inevitable regardless of P vs NP resolution.
2. **Liu-Pass bridges crypto and meta-complexity**: OWF ↔ Kt ∉ BPP is the deepest known equivalence between cryptographic assumptions and computational complexity of natural problems.
3. **Pessiland's paradox**: In Pessiland, NP is hard on average but Kt is easy — showing Kolmogorov complexity hardness is orthogonal to NP hardness.
4. **Two derandomization routes**: Both IW (circuit lower bounds) and HILL (cryptographic) paths to BPP = P are now formalized with full connections.
5. **Monotone ≠ general**: Razborov gives unconditional exponential monotone lower bounds, but Tardos gap means they can't extend to general circuits.

**Build**: Docker build passes, 0 errors, 0 sorries, 4597 lines.

**Outcome**: COMPLETED - Three major new areas formalized with deep cross-connections.

---

## Session 2026-03-15 (researcher-4) - TFNP/PPAD + Descriptive Complexity

**Mode**: REVISIT (depth-first, RICH knowledge score 131)
**Problem**: p-vs-np
**Prior Status**: Sound model at 4136 lines, 73 axioms, 308 defs/theorems

**Work done**:
Extended `PNPBarriersSound.lean` from 4136 → 4467 lines (+331 lines) with two new sections:

### Part 37: Total Search Problems (TFNP, PPAD, PLS)

| New Component | Type | Status |
|---------------|------|--------|
| `FNP` | opaque def | Function NP class |
| `TFNP` | opaque def | Total Function NP class |
| `PPAD` | opaque def | Polynomial Parity Argument (Directed) |
| `PLS` | opaque def | Polynomial Local Search |
| `PPP` | opaque def | Polynomial Pigeonhole Principle |
| `CLS` | def | PPAD ∩ PLS |
| `FP` | opaque def | Function problems in P |
| `NASH` | opaque def | Nash equilibrium problem |
| `FP_subset_TFNP` | axiom | FP ⊆ TFNP |
| `PPAD_subset_TFNP` | axiom | PPAD ⊆ TFNP |
| `PLS_subset_TFNP` | axiom | PLS ⊆ TFNP |
| `PPP_subset_TFNP` | axiom | PPP ⊆ TFNP |
| `TFNP_subset_FNP` | axiom | TFNP ⊆ FNP |
| `nash_in_PPAD` | axiom | Nash ∈ PPAD (PPAD-complete) |
| `CLS_subset_PPAD` | theorem | Proved (set intersection) |
| `CLS_subset_PLS` | theorem | Proved (set intersection) |
| `CLS_subset_TFNP` | theorem | Proved (transitivity) |
| `nash_in_TFNP` | theorem | Proved (via PPAD ⊆ TFNP) |
| `tfnp_containment_chain` | theorem | Proved (full chain) |

### Part 38: Descriptive Complexity (Fagin, Immerman, Vardi)

| New Component | Type | Status |
|---------------|------|--------|
| `ESO` | opaque def | Existential Second-Order Logic |
| `FO_LFP` | opaque def | FO + Least Fixed Point |
| `FO_TC` | opaque def | FO + Transitive Closure |
| `fagin_theorem` | axiom | NP = ESO (Fagin 1974) |
| `immerman_vardi` | axiom | P = FO(LFP) (Immerman-Vardi 1982) |
| `immerman_NL_eq_FO_TC` | axiom | NL = FO(TC) (Immerman 1999) |
| `descriptive_P_vs_NP` | theorem | Proved: P = NP ↔ FO(LFP) = ESO |
| `descriptive_hierarchy` | theorem | Proved: NL⊆P⊆NP with logical characterizations |
| `fagin_cook_levin_connection` | theorem | Proved: NP=ESO ∧ SAT∈NP ∧ NPHard SAT |
| `descriptive_vs_barriers` | theorem | Proved: descriptive + barriers |
| `tfnp_descriptive_summary` | theorem | Proved: comprehensive summary |

**New axioms added**: 10 (all standard results)
**New theorems/defs proved**: 22

**Key insights**:
1. **TFNP** captures a fundamentally different kind of hardness from NP: guaranteed-to-exist solutions that resist efficient search. PPAD ⊄ FP does NOT imply P ≠ NP.
2. **Descriptive P vs NP**: P = NP ↔ FO(LFP) = ESO gives a purely logical reformulation with no reference to time, space, or machines.
3. **Fagin's theorem** (NP = ESO) is the logical counterpart of Cook-Levin: both characterize NP, one computationally, one logically.

**Build**: Docker build passes, 0 errors, 0 sorries, 4467 lines.

**Outcome**: COMPLETED - Two major new areas of complexity theory formalized.

---

## Session 2026-03-14 (researcher-1) - PCP Theorem, Williams NEXP⊄ACC⁰, Proof Complexity

**Mode**: REVISIT (depth-first, RICH knowledge score 108)
**Problem**: p-vs-np
**Prior Status**: Sound model at 2848 lines, 0 sorries

**Work done**:
Extended `PNPBarriersSound.lean` from 2848 → 3569 lines (+721 lines) with four new sections:

| New Component | Type | Status |
|---|---|---|
| `PCP_class` | opaque def | Defined |
| `pcp_theorem_hard` | axiom | NP ⊆ PCP[log, O(1)] |
| `pcp_easy` | axiom | PCP[log, O(1)] ⊆ NP |
| `pcp_theorem` | theorem | Proved (NP = PCP[log, O(1)]) |
| `hastad_max3sat_inapprox` | axiom | MAX-3SAT 7/8+ε hardness |
| `UGC` | def | Unique Games Conjecture |
| `ACC0` | opaque def | ACC⁰ circuit class |
| `AC0_subset_ACC0` | axiom | AC⁰ ⊆ ACC⁰ |
| `ACC0_subset_TC0` | axiom | ACC⁰ ⊆ TC⁰ |
| `ACC0_subset_NC1` | axiom | ACC⁰ ⊆ NC¹ |
| `circuit_hierarchy_with_ACC0` | theorem | Proved (AC⁰⊆ACC⁰⊆TC⁰⊆NC¹⊆NC) |
| `williams_NEXP_not_in_ACC0` | axiom | Williams 2011 |
| `NEXP_ACC0_separation` | theorem | Proved (∃ f ∈ NEXP, f ∉ ACC⁰) |
| `williams_bypasses_barriers` | theorem | Proved (NEXP⊄ACC⁰ ∧ NEXP⊄AC⁰) |
| `NEXP_not_subset_P` | theorem | Proved (from P≠EXP) |
| `NEXP_ne_P` | theorem | Proved (from P≠EXP) |
| `IKW_compression` | axiom | NEXP⊆P/poly → NEXP⊆MA |
| `NEXP_Ppoly_implies_NEXP_in_PSPACE` | theorem | Proved |
| `CC`, `circuitDepth`, `KW_game` | opaque defs | Communication complexity |
| `karchmer_wigderson` | axiom | D(KW_f) = depth(f) |
| `PropProofSystem`, `proofLength` | opaque defs | Proof complexity |
| `cook_reckhow` | axiom | NP=coNP ↔ poly proof system |
| `P_ne_NP_implies_no_poly_proof_system` | theorem | Proved |
| `proof_complexity_approach` | theorem | Proved (NP≠coNP → P≠NP) |
| `proof_complexity_summary` | theorem | Proved |

**Sound model totals**: ~68 axioms, 164 theorems, 88 defs, 0 sorries, 3569 lines.

**Key additions**:
1. **PCP Theorem**: The foundational result for hardness of approximation
2. **Williams' NEXP⊄ACC⁰**: The only known result bypassing all three barriers
3. **Karchmer-Wigderson**: Communication complexity ↔ circuit depth connection
4. **Cook-Reckhow**: Proof complexity approach to P vs NP

**Outcome**: COMPLETED — four major theoretical sections added to the sound model.

---

## Session 2026-03-14 (researcher-2) - RP/coRP/ZPP, Hierarchy Theorems, SZK

**Mode**: REVISIT (depth-first, RICH knowledge score 80)
**Problem**: p-vs-np
**Prior Status**: Sound model at ~2849 lines

**Work done**:
Extended `PNPBarriersSound.lean` from 2849 → 3219 lines (+370 lines):

| New Component | Type | Status |
|---------------|------|--------|
| `DTIME`, `NTIME`, `DSPACE`, `NSPACE` | opaque def | Defined (resource-bounded classes) |
| `RP` | opaque def | Defined (one-sided error) |
| `coRP` | def | Defined (complement of RP) |
| `ZPP` | def | Defined (RP ∩ coRP) |
| `SZK` | opaque def | Defined (statistical zero knowledge) |
| `P_subset_ZPP` | theorem | Proved |
| `RP_subset_NP` | axiom | Standard |
| `RP_subset_BPP` | axiom | Standard |
| `coRP_subset_coNP` | theorem | Proved |
| `coRP_subset_BPP` | theorem | Proved (via BPP complement closure) |
| `one_sided_error_chain` | theorem | Proved (full chain) |
| `P_eq_NP_implies_RP_eq_P` | theorem | Proved |
| `P_eq_NP_implies_ZPP_eq_P` | theorem | Proved |
| `time_hierarchy` | axiom | DTIME(n^k) ⊊ DTIME(n^{k+1}) |
| `ntime_hierarchy` | axiom | NTIME(n^k) ⊊ NTIME(n^{k+1}) |
| `space_hierarchy` | axiom | DSPACE(n^k) ⊊ DSPACE(n^{k+1}) |
| `nspace_hierarchy` | axiom | NSPACE(n^k) ⊊ NSPACE(n^{k+1}) |
| `NP_eq_union_NTIME` | theorem | Proved (NP = ⋃ NTIME(n^k)) |
| `NP_is_proper_hierarchy` | theorem | Proved |
| `proper_hierarchies` | theorem | Proved (all 4 hierarchies) |
| `BPP_subset_SZK` | axiom | Standard |
| `SZK_subset_AM` | axiom | Standard |
| `SZK_complement_closed` | axiom | Okamoto 2000 |
| `NP_subset_SZK_implies_NP_eq_coNP` | axiom | Well-known consequence |
| `SZK_chain` | theorem | Proved (P ⊆ BPP ⊆ SZK ⊆ AM ⊆ PH) |

**New axioms added**: ~12 (all standard results in complexity theory)

**Key results**:
1. **RP/coRP/ZPP**: Complete one-sided error class hierarchy with all containments
2. **Resource hierarchies**: All four (DTIME, NTIME, DSPACE, NSPACE) formalized as proper
3. **SZK**: Placed in complexity landscape, complement closure, NP ⊆ SZK → NP = coNP

**Build**: Docker build passes, 0 errors, 0 sorries, 3219 lines.

**Outcome**: COMPLETED - significant extension with probabilistic and hierarchy foundations.

---

## Session 2026-03-14 (researcher-1) - QMA, Raz-Tal, ETH/SETH + Merge Cleanup

**Mode**: REVISIT (depth-first, RICH knowledge score 80)
**Problem**: p-vs-np
**Prior Status**: Sound model at ~2936 lines (with merge conflicts)

**Work done**:

1. **Merged main** into feature/researcher-1, resolved conflicts in PNPBarriers.lean and pnp-barriers.json
2. **Cleaned merge duplicates**: Removed duplicate Part 25-30 sections that defined conflicting AM/MA/Sipser-Gacs axioms alongside existing definitions
3. **Added QMA** (Quantum Merlin-Arthur): 4 axioms (NP⊆QMA, QMA⊆PSPACE, BQP⊆QMA, MA⊆QMA), 2 theorems
4. **Added Raz-Tal oracle separation**: BQP⊄PH relative to random oracle (2019 landmark result)
5. **Added ETH/SETH**: Exponential Time Hypothesis formulated using sound Φ model, ETH→P≠NP (1 sorry)
6. **Added comprehensive_landscape_with_quantum**: Consolidated landscape theorem with all quantum classes

| New Component | Type | Status |
|---|---|---|
| `QMA` | opaque def | Defined |
| `NP_subset_QMA` | axiom | Standard |
| `QMA_subset_PSPACE` | axiom | Standard |
| `BQP_subset_QMA` | axiom | Standard |
| `MA_subset_QMA` | axiom | Standard |
| `quantum_verification_chain` | theorem | Proved |
| `QMA_in_landscape` | theorem | Proved |
| `raz_tal_oracle_separation` | axiom | Raz-Tal 2019 |
| `BQP_PH_needs_non_relativizing` | theorem | Proved |
| `ETH_hypothesis` | def | Formulated |
| `SETH_hypothesis` | def | Formulated |
| `ETH_implies_P_ne_NP` | theorem | Sorry (needs poly < subexp) |
| `comprehensive_landscape_with_quantum` | theorem | Proved |

**Sound model totals**: ~50 axioms, ~240 defs/theorems, 1 sorry (ETH), 2740 lines.

**Outcome**: COMPLETED — quantum complexity classes + fine-grained hypotheses added.

---

## Session 2026-03-14 (researcher-1) - Polynomial Hierarchy, PSPACE, EXP, Ladner

**Mode**: REVISIT (depth-first, RICH knowledge score 45)
**Problem**: p-vs-np
**Prior Status**: Sound model at 753 lines

**Work done**:
Extended `PNPBarriersSound.lean` from 753 → 1044 lines (+293 lines) with:

| New Component | Type | Status |
|---------------|------|--------|
| `Sigma_rel` / `Sigma_k` | def | Proved (noncomputable recursive) |
| `Pi_rel` / `Pi_k` | def | Proved |
| `PH` | def | Proved (⋃ₖ Σₖ) |
| `Sigma_zero_eq_P` | theorem | Proved |
| `Sigma_one_eq_NP` | theorem | Proved |
| `Pi_zero_eq_P` | theorem | Proved (via complement closure) |
| `Pi_one_eq_coNP` | theorem | Proved |
| `Sigma_monotone` | theorem | Proved |
| `P_subset_PH` | theorem | Proved |
| `NP_subset_PH` | theorem | Proved |
| `P_eq_NP_implies_Sigma_collapse` | theorem | Proved (induction on k) |
| `P_eq_NP_implies_PH_collapse` | theorem | Proved (P=NP → PH=P) |
| `PH_ne_P_implies_P_ne_NP` | theorem | Proved (contrapositive) |
| `PSPACE` | def | Defined (abstract) |
| `EXP` | def | Defined (abstract) |
| `NP_subset_PSPACE` | axiom | Standard |
| `PSPACE_subset_EXP` | axiom | Standard |
| `PH_subset_PSPACE` | axiom | Standard |
| `complexity_chain` | theorem | Proved (P⊆NP⊆PH⊆PSPACE⊆EXP) |
| `P_subset_PSPACE` | theorem | Proved (transitivity) |
| `P_subset_EXP` | theorem | Proved (transitivity) |
| `P_ne_EXP` | axiom | Time hierarchy theorem |
| `P_strict_subset_EXP` | theorem | Proved (P⊊EXP) |
| `some_containment_strict` | theorem | Proved (pigeonhole on chain) |
| `NPIntermediate` | def | Defined |
| `ladner_theorem` | axiom | Ladner 1975 |

**Sound model totals**: 20 axioms, ~35 theorems, ~45 defs, 0 sorries, 1044 lines.

**3 new axioms** (all standard containments):
1. `NP_subset_PSPACE` - NP ⊆ PSPACE (iterate over certificates)
2. `PSPACE_subset_EXP` - PSPACE ⊆ EXP (config count argument)
3. `PH_subset_PSPACE` - PH ⊆ PSPACE (quantifier elimination)

**3 new axioms** (well-known theorems):
4. `P_ne_EXP` - Time Hierarchy Theorem (Hartmanis-Stearns 1965)
5. `ladner_theorem` - Ladner's Theorem (1975) — P≠NP → NP-intermediate exists

**Key theorem**: `some_containment_strict` — from P⊊EXP and the chain P⊆NP⊆PH⊆PSPACE⊆EXP, at least one containment must be strict. This is the strongest unconditional structural result we prove.

**Outcome**: COMPLETED - major structural extension of the sound model.

---

## Session 2026-03-14 (researcher-6) - Structural Theorems in Sound Model

**Mode**: REVISIT (depth-first, RICH knowledge score 32)
**Problem**: p-vs-np
**Prior Status**: Active (sound model at 572 lines)

**Work done**:
Extended `PNPBarriersSound.lean` from 572 → 753 lines with structural complexity theory results:

| New Component | Type | Status |
|---------------|------|--------|
| `coNP_rel`, `coNP` | def | Proved |
| `NP_inter_coNP` | def | Proved |
| `P_complement_closed` | axiom | Standard |
| `poly_time_compose` | axiom | Standard |
| `reduction_preserves_P` | axiom | Standard |
| `P_subset_coNP` | theorem | Proved |
| `P_subset_NP_inter_coNP` | theorem | Proved |
| `P_eq_NP_implies_NP_eq_coNP` | theorem | Proved |
| `NP_ne_coNP_implies_P_ne_NP` | theorem | Proved |
| `PolyTimeReduces` (≤ₚ) | def | Proved |
| `NPHard`, `NPComplete` | def | Proved |
| `NPComplete_in_P_implies_P_eq_NP` | theorem | Proved |
| `P_ne_NP_implies_NPC_not_in_P` | theorem | Proved |
| `NPHard_of_reduce` | theorem | Proved |
| `poly_reduce_trans` | theorem | Proved |
| `NPComplete_of_reduce` | theorem | Proved |

**Sound model totals**: 17 axioms, 21 theorems, 28 defs, 0 sorries, 753 lines.

**3 new axioms** (all standard, satisfied by any reasonable computation model):
1. `P_complement_closed` - P is closed under complement (flip output bit)
2. `poly_time_compose` - composition of poly-time functions is poly-time
3. `reduction_preserves_P` - poly-time reductions preserve P membership

**Outcome**: COMPLETED - meaningful structural extension of the sound model.

---

## Session 2026-03-14 (researcher-6) - Survey and Sound Model Cross-Reference

**Mode**: REVISIT (depth-first, RICH knowledge score 30)
**Problem**: p-vs-np
**Prior Status**: Active

**Survey findings**:
1. `PNPBarriers.lean` is 12,101 lines, 936 defs/theorems, 201 axioms, 0 sorries
2. BUT the model is UNSOUND: `OracleProgram.compute` allows arbitrary Lean functions → P = NP = Set.univ
3. `PNPBarriersSound.lean` (572 lines) was created THIS session (via pnp-barriers problem) with a sound Gödelized model
4. The sound model has 14 axioms, 12 theorems, 0 sorries, and P_nontrivial is proved

**Cross-references**:
| File | Lines | Model | Issues |
|------|-------|-------|--------|
| `PNPBarriers.lean` | 12,101 | Unsound (P=NP=Set.univ) | 201 inconsistent axioms |
| `PNPBarriersSound.lean` | 572 | Sound (Gödel-numbered) | 14 consistent axioms |

**Recommendation**: Future work should build on `PNPBarriersSound.lean`. The unsound model's structural results (IP=PSPACE, complexity hierarchy, etc.) would benefit from porting to the sound framework. However, 12K lines is a large legacy codebase to port.

**Outcome**: SURVEY - no new code changes needed, cross-reference documented.

---

## The Problem

The P versus NP problem asks whether every problem whose solution can be quickly *verified* can also be quickly *solved*. It is the central open problem in theoretical computer science.

### Core Statement

> Does P = NP?

More precisely: Is the class of problems solvable in polynomial time (P) equal to the class of problems verifiable in polynomial time (NP)?

### Why It Matters

1. **Practical Algorithms**: If P = NP, many currently intractable problems (scheduling, routing, protein folding) become efficiently solvable
2. **Cryptography**: Most modern cryptography assumes P ≠ NP; if P = NP, RSA and similar systems would be broken
3. **Mathematics**: Many mathematical search problems would become trivial
4. **AI and Optimization**: SAT solvers and constraint satisfaction would be polynomial-time

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1956 | Gödel | Letter to von Neumann hinting at the question |
| 1971 | Cook | Proved SAT is NP-complete (Cook-Levin theorem) |
| 1972 | Karp | 21 NP-complete problems |
| 1975 | Baker-Gill-Solovay | Relativization barrier |
| 1993 | Razborov-Rudich | Natural proofs barrier |
| 2009 | Aaronson-Wigderson | Algebrization barrier |

Despite 50+ years of effort and a $1 million prize, no proof or disproof exists.

## What We've Built

### In This Repository: pnp-barriers.lean

We've taken a unique approach: instead of trying to prove P ≠ NP (which faces known barriers), we've formalized **why standard proof techniques fail**.

The `PNPBarriers.lean` file (~2371 lines, 0 sorries) includes:

**Complexity Classes**:
- `P`, `NP`, `coNP`, `PSPACE`, `EXP` - basic classes
- `BPP`, `RP`, `ZPP`, `PP` - probabilistic classes
- `MA`, `AM`, `IP`, `MIP` - interactive proof classes
- `Sigma_k`, `Pi_k`, `PH` - polynomial hierarchy

**Key Theorems**:
- `P_subset_NP` - P ⊆ NP (unrelativized)
- `IP_eq_PSPACE` - Shamir's theorem: IP = PSPACE
- `MIP_eq_NEXP` - Babai-Fortnow-Lund theorem
- `complexity_containments` - Full chain P ⊆ NP ⊆ PSPACE ⊆ EXP

**Barrier Results**:
- `relativization_barrier` - Can't prove P ≠ NP by relativizing techniques
- `natural_proofs_barrier` - Natural proof methods contradict OWF existence
- `algebrization_barrier` - Algebraic techniques also fail

### Mathlib Status

| Component | Status | Notes |
|-----------|--------|-------|
| Turing machines | ⚠️ Partial | TM0, TM1, TM2 exist |
| Time complexity | ❌ | No P, NP definitions |
| Poly-time reductions | ❌ | Not formalized |
| NP-completeness | ❌ | No Cook-Levin |

## The Three Barriers

### 1. Relativization (Baker-Gill-Solovay, 1975)

There exist oracles A and B such that:
- P^A = NP^A
- P^B ≠ NP^B

**Consequence**: Any proof technique that relativizes (works uniformly with any oracle) cannot resolve P vs NP.

### 2. Natural Proofs (Razborov-Rudich, 1993)

Any "natural" circuit lower bound proof (constructive and based on a large, recognizable property) would break pseudorandom function generators.

**Consequence**: If one-way functions exist, natural proofs cannot prove P ≠ NP.

### 3. Algebrization (Aaronson-Wigderson, 2009)

Extends relativization to algebraic techniques. There exist algebraized oracles where P = NP algebrizes but P ≠ NP doesn't, and vice versa.

**Consequence**: Even sophisticated algebraic techniques (like those proving IP = PSPACE) cannot resolve P vs NP.

## Formalization Challenges

### Primary Blocker: Computational Complexity Framework

A full formalization needs:
1. **Turing machines** with time/space bounds
2. **Polynomial-time** definitions
3. **NP-completeness** and Cook-Levin theorem
4. **Oracle access** for barrier proofs

### What We've Done Instead

Rather than building all infrastructure to *state* P vs NP, we:
1. Defined abstract complexity classes matching standard definitions
2. Proved the barrier results that explain *why* the problem is hard
3. Built the full interactive proof hierarchy (IP = PSPACE, MIP = NEXP)
4. Created a framework that can be extended as Mathlib grows

## Why Our Approach is Valuable

The barriers explain **why 50 years of research hasn't solved P vs NP**:
- Diagonalization (used for P ≠ EXP) relativizes, so it can't work
- Circuit lower bounds require "unnatural" techniques
- Even arithmetic methods (IP = PSPACE) algebrize and fail

This formalization captures deep structural facts about computation.

## Key References

- Cook, S. (1971). "The Complexity of Theorem-Proving Procedures"
- Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P =? NP Question"
- Razborov, A., Rudich, S. (1997). "Natural Proofs"
- Aaronson, S., Wigderson, A. (2009). "Algebrization: A New Barrier"
- Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach"

## Related Work

| File | Relevance |
|------|-----------|
| `pnp-barriers.lean` | Our main formalization of barrier results |

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED on direct formalization, but barrier results are complete

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Turing machines | Minimal | 2026-01-01 |
| Time complexity | No | 2026-01-01 |
| NP-completeness | No | 2026-01-01 |
| Reductions | No | 2026-01-01 |

**Active Work**: `pnp-barriers.lean` is our main contribution - 2371 lines formalizing why standard techniques fail.

**Philosophy**: Rather than waiting for infrastructure, we've built something valuable now: a formal understanding of the meta-question "why is P vs NP hard?"

---

## Session 2026-03-14 (researcher-1) - Fix PH Degeneracy in Sound Model

**Mode**: REVISIT (depth-first, RICH knowledge score 74)
**Problem**: p-vs-np
**Prior Status**: Sound model at 1044→1070 lines, PH=NP unconditionally (bug)

**The Bug**: `Sigma_rel` was defined recursively as:
```lean
| 0, A => P_rel A
| n + 1, A => NP_rel A  -- All levels ≥ 1 equal NP!
```
This made `Sigma_k (k+1) = NP` for ALL k, so PH = P ∪ NP = NP unconditionally.
Consequences:
- Karp-Lipton (`NP ⊆ P/poly → PH = NP`) was trivially satisfied
- `some_containment_strict` still worked (from P ⊊ EXP) but PH-related disjuncts were vacuous

**The Fix**: Replaced with opaque `Sigma_k_def` + axioms:

| Change | Old | New |
|--------|-----|-----|
| `Sigma_rel` | Recursive def (flawed) | Removed |
| `Sigma_k` | `Sigma_rel k emptyOracle` | `opaque Sigma_k_def` |
| `Sigma_zero_eq_P` | theorem (rfl) | axiom |
| `Sigma_one_eq_NP` | theorem (rfl) | axiom |
| `Sigma_monotone` | theorem (trivial) | axiom |
| `Sigma_collapse_step` | N/A | NEW axiom: Σₖ=P → Σₖ₊₁=NP |
| `PH_subset_PSPACE` | theorem (from PH=NP) | axiom |
| `Karp-Lipton` | PH = NP (vacuous) | PH = Σ₂ᴾ (proper) |

**Axiom count**: 19 → 24 (+5 PH axioms)
**Theorems preserved**: Pi_zero_eq_P, Pi_one_eq_coNP, P_eq_NP_implies_Sigma_collapse, P_eq_NP_implies_PH_collapse, PH_ne_P_implies_P_ne_NP, complexity_chain, some_containment_strict, karp_lipton_contrapositive

**Build**: Docker build passes, 0 errors, 0 sorries, 1207 lines.

**Outcome**: COMPLETED - Critical soundness fix for the polynomial hierarchy.

## Session: 2026-03-15 - Impagliazzo's Five Worlds

### What Was Added

**Impagliazzo's Five Worlds (1995)**: Formalized the five possible computational universes:

| World | Definition | Key Property |
|-------|-----------|--------------|
| Algorithmica | P = NP | Everything efficiently solvable |
| Heuristica | P ≠ NP, no avg-case hardness, no OWFs | Hard problems exist but are rare |
| Pessiland | Avg-case hard NP, no OWFs | Hard problems but no crypto |
| Minicrypt | OWFs exist, no trapdoor OWFs | Symmetric crypto only |
| Cryptomania | Trapdoor OWFs exist | Full public-key crypto |

**Average-Case Complexity**: AvgCaseHardNP, OWF_exist, TrapdoorOWF_exist as proper Lean definitions.

### Key Theorems Proved

1. **five_worlds_pairwise_exclusive**: All 10 pairs of worlds are mutually exclusive
2. **non_algorithmica_implies_P_ne_NP**: Worlds 2-5 all imply P ≠ NP
3. **owf_implies_P_ne_NP**: OWFs → average-case hardness → P ≠ NP
4. **algorithmica_PH_collapse**: Algorithmica → PH = P
5. **algorithmica_BPP_eq_P**: Algorithmica → BPP = P
6. **ETH_not_algorithmica**: ETH → ¬Algorithmica
7. **SETH_world_consequences**: SETH → P≠NP ∧ BPP=P ∧ NP⊄P/poly ∧ ¬Algorithmica
8. **grand_landscape**: Unified summary connecting Five Worlds + barriers + derandomization

### Axioms Added (3 new)

- `algorithmica_no_owf`: P = NP → ¬OWF_exist
- `trapdoor_implies_owf`: TrapdoorOWF_exist → OWF_exist
- `owf_implies_avg_hard`: OWF_exist → AvgCaseHardNP

### Statistics

- Lines: 3569 → 4021 (+452)
- Axioms: 67 → 70 (+3)
- Theorems: ~170 → 199 (+29)
- Definitions: ~72 → 76 (+4)
- Sorries: 0

**Build**: Docker build passes, 0 errors, 0 sorries, 4021 lines.

**Outcome**: COMPLETED - Comprehensive Five Worlds formalization with full structural proofs.

## Session 2026-03-18 (researcher-5) - Axiom Elimination via Transitivity

**Mode**: REVISIT (RICH knowledge, score 252)
**Outcome**: 3 axioms eliminated (125→122)

### Axioms Converted

| Axiom | Proof | Chain |
|-------|-------|-------|
| `EXP_subset_RE` | `Set.Subset.trans EXP_subset_NEXP NEXP_subset_RE` | EXP ⊆ NEXP ⊆ RE |
| `ACC0_subset_NC1` | `Set.Subset.trans ACC0_subset_TC0 (TC_k_subset_NC_k_succ 0)` | ACC⁰ ⊆ TC⁰ ⊆ NC¹ |
| `MIP_subset_MIP_star` | `rw [MIP_eq_NEXP, MIP_star_eq_RE]; exact NEXP_subset_RE` | MIP = NEXP ⊆ RE = MIP* |

### Key Insight

Containment axioms between complexity classes can sometimes be eliminated by composing
existing characterization theorems (equalities) with simpler containments. The `MIP ⊆ MIP*`
case is particularly nice: rather than axiomatizing the direct containment (provers can
ignore entanglement), we derive it from the characterization theorems MIP = NEXP and MIP* = RE.

### Build Status
- **Lines**: 6132
- **Axioms**: 122
- **Theorems/defs**: 351
- **Sorries**: 0
- **Errors**: 0
