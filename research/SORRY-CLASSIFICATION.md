# Sorry Classification Guide

## Purpose

This guide helps decide **what to send to Aristotle** (proof search tool), NOT what problems we attempt.

**Our mission is to tackle OPEN problems!** But we need to use tools appropriately:
- **Claude** → Strategic reasoning, creative approaches, attempting OPEN problems
- **Aristotle** → Tactical proof search for results with KNOWN proofs

## Classification Tiers (for Aristotle Submission)

### TRIVIAL (Minutes)
**Aristotle time:** 1-10 minutes
**Send to Aristotle:** Yes

Characteristics:
- Direct application of existing lemmas
- Simple case analysis
- Basic arithmetic/computation

Examples:
```lean
theorem two_plus_two : 2 + 2 = 4 := by sorry
theorem mem_singleton : x ∈ ({x} : Set α) := by sorry
```

### HARD (Hours)
**Aristotle time:** 10 minutes - 6+ hours
**Send to Aristotle:** Yes, ideal for overnight runs

Characteristics:
- Known mathematical result that needs formalization
- Proof exists in literature but not in Lean
- Complex but established techniques

Examples:
```lean
-- Hard: Known counting argument
theorem sidon_lower_bound : A.max' hne ≥ A.card * (A.card - 1) / 2 := by sorry

-- Hard: Erdős-Turán bound (1941)
theorem sidon_upper_bound : A.card ≤ Nat.sqrt N + O(N^(1/4)) := by sorry

-- Hard: Erdős #728 - paper proof exists, took 6 hours to formalize
theorem erdos_728 : (good_triples C ε).Infinite := by sorry
```

### OPEN (Creative Work Required)
**Aristotle time:** Will spin forever (no known proof to find)
**Send to Aristotle:** No - work on these OURSELVES
**Send to Claude:** YES! This is our main mission!

Characteristics:
- Unsolved mathematical conjecture
- No known proof exists
- Requires creative insight, not proof search

Examples:
```lean
-- OPEN: The actual Erdős conjecture #340
-- Aristotle can't help - WE need to attempt this!
theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
    ∃ C, ∀ᶠ N in atTop, N^(1/2 - ε) ≤ C * greedySidonCount N := by
  sorry -- OUR TARGET - work on this manually!
```

## The Key Insight

| Tool | Strength | Use For |
|------|----------|---------|
| **Claude** | Strategic reasoning, creativity | OPEN problems, proof architecture |
| **Aristotle** | Proof search, tactic grinding | HARD problems with known proofs |
| **Both** | Complementary | Claude designs, Aristotle fills gaps |

**Aristotle found Erdős #728** because a proof EXISTED (in a paper). It formalized known mathematics.

**Aristotle spun on Erdős #340** because NO proof exists. That's for US to discover!

## Aristotle Companion Files (DEPRECATED — early multi-sorry pattern)

> **Status (2026-06-05):** This multi-sorry companion-file pattern is **superseded** by the
> [Harmonic Submission Format (recommended)](#harmonic-submission-format-recommended) below.
> Harmonic's published examples (the `StatementOnly_IMO2025P*.lean` files in
> [harmonic-ai/IMO2025](https://github.com/harmonic-ai/IMO2025)) and the
> [Aristotle paper](https://arxiv.org/html/2510.01346v1) make clear that Aristotle's MCTS
> proof search is conditioned on **proof state + history + informal proof statement**, and
> that the intended unit of submission is **one theorem per file**, not a companion file
> with N supporting lemmas. Batching multiple sorries in one file dilutes the MCTS
> budget across unrelated subgoals and starves the value function of informal context.
>
> Existing `*Aristotle.lean` companion files remain valid as a **fallback** — they still
> work — but new submissions should follow the StatementOnly format. See the new section
> below. (Subsequent issue: migrate the submission pipeline to the StatementOnly
> convention.)

The original (now-deprecated) recommended way to submit work to Aristotle was via
**companion files**:

```
proofs/Proofs/Erdos340Problem.lean       ← main file: axioms, main conjecture
proofs/Proofs/Erdos340Aristotle.lean     ← companion: only routine lemma sorries
```

Companion files are **Tier 1** in the submission pipeline — the Aristotle agent submits them first before falling back to regular `*Problem.lean` files.

### Creating a Companion File

```bash
# Create alongside your main proof file
touch proofs/Proofs/Erdos340Aristotle.lean
```

Use this template:
```lean
/-
  Aristotle targets for Erdős Problem #340
  Routine supporting lemmas for automated proof search.
  See Erdos340Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos340

-- Routine lemmas that are NOT the main conjecture
lemma orderedPairsLt_card (A : Finset ℕ) : A.card * (A.card - 1) ≤ ... := by sorry
lemma sidon_lower_bound (A : Finset ℕ) (hA : IsSidon A) : ... := by sorry

end Erdos340
```

### What Goes in a Companion File

| Include | Exclude |
|---------|---------|
| Monotonicity lemmas | The main open conjecture |
| Cardinality bounds | `axiom` declarations |
| Known counting arguments | Definition sorries |
| Standard inequalities | Placeholder `True` theorems |
| Lemmas supporting the main proof | Any `sorry` on a definition |

**Converting axioms for companion files**: If your main file uses `axiom` for supporting results, convert them in the companion file:
```lean
-- In main file (correct semantic — marks result as assumed):
axiom sidon_bound (A : Finset ℕ) : A.card ≤ Nat.sqrt N + 1

-- In companion file (Aristotle will attempt to prove):
theorem sidon_bound (A : Finset ℕ) : A.card ≤ Nat.sqrt N + 1 := by sorry
```

### Pre-Submission Checklist

Before the Aristotle agent submits your companion file:

1. **List all sorries:**
   ```bash
   grep -n "sorry" proofs/Proofs/Erdos340Aristotle.lean
   ```

2. **Verify each sorry:**
   - [ ] Is this a known result? → HARD (include)
   - [ ] Is this computational? → TRIVIAL (include)
   - [ ] Is this an open conjecture? → OPEN (do NOT include — keep in main file)
   - [ ] Is this a definition sorry? → Remove (blocks everything)
   - [ ] Is this an axiom? → Convert to `theorem ... := by sorry`

3. **The file is ready when:**
   - No definition sorries
   - No `axiom` declarations
   - No open conjectures
   - All sorries are TRIVIAL or HARD supporting lemmas

The Aristotle agent auto-detects companion files. No manual submission needed.

## Naming Convention

To help identify OPEN problems, use this naming pattern:

```lean
-- OPEN problems: use problem name directly
theorem erdos_340 ...        -- Open Erdős #340
theorem goldbach ...         -- Open Goldbach conjecture
theorem riemann_hypothesis   -- Open Riemann hypothesis

-- Provable results: use descriptive names
theorem sidon_lower_bound ...      -- Provable counting argument
theorem sidon_upper_bound ...      -- Provable Erdős-Turán bound
theorem greedySidon_growth_third   -- Provable known result
```

## Aristotle Runtime Expectations

| Classification | Typical Runtime | Success Rate |
|----------------|-----------------|--------------|
| TRIVIAL        | 1-10 min        | ~95%         |
| HARD           | 10 min - 6 hr   | ~60-80%      |
| OPEN           | ∞ (stuck at 5%) | 0%           |

## Example: Erdős #340

```
File: Erdos340GreedySidon.lean

Sorries:
├── orderedPairsLt_card      → HARD (counting lemma)
├── sidon_lower_bound        → HARD (uses counting + pigeonhole)
├── sidon_upper_bound        → HARD (Erdős-Turán bound)
├── greedySidon_growth_third → HARD (known N^(1/3) result)
├── _22_mem_diffSet          → TRIVIAL (computational)
├── _33_mem_diffSet_iff      → TRIVIAL (computational)
└── erdos_340                → OPEN ⚠️ DO NOT SUBMIT

Action: Create Erdos340-provable.lean without erdos_340
```

## Critical: Definition Sorries vs Theorem Sorries

**Aristotle only handles theorem/lemma sorries. It skips definition sorries entirely.**

### What Aristotle Can Prove

```lean
-- ✅ THEOREM SORRY - Aristotle will attempt this
theorem sidon_lower_bound (A : Finset ℕ) : A.max' hne ≥ A.card * (A.card - 1) / 2 := by
  sorry

-- ✅ LEMMA SORRY - Aristotle will attempt this
lemma computeA_22 : computeA (![2, 2] : HomologyClass 2) = 10 := by
  sorry
```

### What Aristotle Skips

```lean
-- ❌ DEFINITION SORRY - Aristotle skips, blocks dependent theorems
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ := by sorry

-- ❌ DEF SORRY - Aristotle skips
def danzerPoints : Finset (EuclideanSpace ℝ (Fin 2)) := sorry

-- ❌ PLACEHOLDER THEOREM - No real content to prove
theorem erdos_39 : True := by sorry
```

### Why This Matters

When a definition has a sorry, any theorem using it cannot be proved meaningfully:

```lean
-- Definition has sorry
noncomputable def turanNumber : ℕ → ℕ → ℕ := by sorry

-- Theorem depends on undefined definition - Aristotle can't help
theorem turan_bound (n k : ℕ) : turanNumber n k ≤ ... := by
  sorry  -- Would need turanNumber to be defined first
```

### Pre-Submission Checklist (Updated)

Before running `./research/scripts/aristotle-submit.sh`:

1. **Check for definition sorries:**
   ```bash
   grep -n "def.*:=.*sorry\|def.*:= by.*sorry" your-file.lean
   ```

2. **If definition sorries exist:**
   - Either provide the actual definition
   - Or use an axiom with clear documentation
   - Or don't submit (Aristotle won't make progress)

3. **Check for placeholder theorems:**
   ```bash
   grep -n "theorem.*: True" your-file.lean
   ```
   These provide no value to Aristotle.

### Runtime Expectations (Updated)

| Sorry Type | Aristotle Behavior | Success Rate |
|------------|-------------------|--------------|
| Theorem sorry (TRIVIAL) | Attempts, ~1-10 min | ~95% |
| Theorem sorry (HARD) | Attempts, ~10 min - 6 hr | ~60-80% |
| Theorem sorry (OPEN) | Spins forever | 0% |
| **Definition sorry** | **SKIPS entirely** | **0%** |
| **Placeholder True** | Marks complete, no value | N/A |

## Early Successes That Motivate the New Format

The following two cases were our earliest Aristotle wins. They predate the formal
documentation of Harmonic's `StatementOnly_*.lean` convention, but in hindsight they
foreshadow exactly *why* that convention works: a single clean theorem statement (or a
small, tightly-related cluster) with complete definitions and no open conjectures is the
shape Aristotle's MCTS handles well. Both stories remain accurate as positive existence
proofs — they are *not* retracted — but new submissions should use the Harmonic format
documented below, which makes these conditions explicit and uniform.

### Success Story: Erdős #728

Aristotle successfully proved Erdős #728 in 6 hours:
- Input: File with HARD sorries only (no OPEN conjectures)
- Output: 1,416 lines of complete proof
- Result: Zero sorries, builds successfully

This demonstrates that HARD problems are worth overnight runs! In the Harmonic-format
framing, Erdős #728 succeeded because the file effectively *was* a one-statement
submission — the supporting lemmas were tightly coupled to the main result and the
informal context (the paper) was implicit in the lemma names and structure.

### Success Story: MotivicFlagMapsProvable

Aristotle proved ALL 10 theorems in an overnight run:
- Input: File with complete definitions, only theorem sorries
- Theorems: GL5_class, Fl5_class, GLn_product_expansion, computeA cases
- Result: Zero sorries, builds successfully

**Key**: All definitions were complete. Only theorems had sorries. This is consistent
with Harmonic's `StatementOnly` discipline — definitions are settled before submission,
not derived as part of the search.

## Failure Patterns (January 2026, revised June 2026)

Jobs that returned "complete" but made no progress:

| Problem | Issue | Outcome |
|---------|-------|---------|
| erdos-58 | `chromaticNumber` definition sorry | Theorems axiomatized |
| erdos-59 | `turanNumber`, `countFreeGraphs` def sorries | No proofs |
| erdos-97 | `danzerPoints` definition sorry | Construction skipped |
| erdos-39/494/605/645/650 | Placeholder `True` theorems | No meaningful work |
| (many `*Aristotle.lean`) | **Multi-sorry batching dilutes MCTS budget** | Search exhausts on first hard subgoal, returns partial / no progress |
| (many `*Aristotle.lean`) | **Missing informal-problem `/-` block** | Value function lacks English context to condition on; search drifts |
| (any submission) | No `-- Proof attempt:` scaffolding | Aristotle has no human-supplied hint; Rivin reports scaffolding flipped his Pólya–Szegő dataset from 2.8% to 100% solved |
| (concurrency) | Submitting >5 projects simultaneously | Harmonic's server cap is 5 hard / ~3 soft; queue backs up, jobs time out |

**Lessons**:
- Only submit files where definitions are complete.
- Submit **one theorem per file** (Harmonic `StatementOnly_*.lean` convention).
- Include an informal problem statement at the top of every file.
- Provide a (possibly wrong) proof attempt as scaffolding when feasible.
- Throttle to ~3 concurrent jobs, use async polling (no `--wait`).

## Syntax Compatibility Issues (January 2026)

**Aristotle's parser differs from local Mathlib.** Files that compile locally may fail to load in Aristotle's environment.

### Known Incompatibilities

| Syntax | Problem | Workaround |
|--------|---------|------------|
| `/-!` docstrings | "unexpected token `/-!`" | Use `/-` instead |
| Complex namespaces | "unexpected name after `end`" | Simplify namespace structure |
| Some type inference | "function expected" errors | Add explicit type annotations |
| Advanced Mathlib APIs | Version mismatch | Stick to stable, well-known APIs |

### Failure Examples (January 2026)

These files compiled locally but failed in Aristotle:

| Problem | Failure Mode | Root Cause |
|---------|--------------|------------|
| erdos-208 | "Unexpected axioms added" | Environment load failure |
| erdos-63 | "Unexpected axioms added" | Environment load failure |
| erdos-107 | "function expected at `f`" | Type inference issues |
| erdos-57 | "unexpected name after `end`" | Namespace parsing |
| erdos-266 | "unexpected token `/-!`" | Docstring section syntax |
| erdos-213 | "Unexpected axioms added" | Environment load failure |

### Pre-Submission Syntax Check

Before submitting, verify:

```bash
# Check for /-! docstring sections (may cause parsing errors)
grep -n "/-!" your-file.lean

# Check for complex namespace usage
grep -n "^namespace\|^end " your-file.lean

# Ensure imports are minimal and standard
head -20 your-file.lean | grep "^import"
```

### Best Practices for Aristotle Compatibility

1. **Use simple docstrings**: `/-` instead of `/-!`
2. **Minimize namespace nesting**: Flat structure preferred
3. **Explicit type annotations**: Don't rely heavily on inference
4. **Standard imports only**: `import Mathlib` is safest
5. **Test with simpler files first**: Submit incrementally

### When Aristotle Fails to Load

If you see "Aristotle failed to load this code into its environment":

1. **Check the error messages** in the returned `-solved.lean` file
2. **Simplify the syntax** based on the specific errors
3. **Consider manual proof** if syntax issues persist
4. **Report patterns** to improve future guidance

### Recovery Strategy

For files that fail to load:

```bash
# Move to failed directory for reference
mv aristotle-results/new/ProblemX-solved.lean aristotle-results/failed/

# Update job status in registry
# Change status from "submitted" to "failed"
# Add outcome describing the failure mode
```

## Harmonic Submission Format (recommended)

> **Status (2026-06-05):** This is the **current recommended format** for all new
> Aristotle submissions, derived from a 2026-06-05 study of Harmonic's published Aristotle
> system (the IMO-2025 gold-medal run), Harmonic's open-source
> [`harmonic-ai/IMO2025`](https://github.com/harmonic-ai/IMO2025) example files, Igor
> Rivin's 100% verified Pólya–Szegő dataset, and the `aristotlelib` / `lean-aristotle-mcp`
> client tooling. See the [Citations](#citations) section at the bottom for full sources.
>
> If you are setting up a new submission, **start here**. Use the deprecated multi-sorry
> companion file only as a fallback for legacy pipelines.

### Why the format matters

Aristotle is Harmonic's IMO-level proof-search engine. Internally it runs **Monte Carlo
Tree Search (MCTS) over Lean tactics, conditioned on `(proof state, history, informal
proof)`**. The informal natural-language problem statement is *not* decoration — it is
part of the input to Aristotle's value function. Three implications follow:

1. **One theorem per file.** MCTS has a finite budget per project. Splitting that budget
   across N sorries in a multi-sorry companion file shrinks the per-sorry budget and lets
   one hard subgoal starve the rest. Harmonic's own input format is exactly one statement
   per `StatementOnly_*.lean` file.
2. **Informal context up top.** A `/-` block at the top of the file describing the
   problem in English gives the value function something to condition on. Submitting bare
   `:= by sorry` with no English context is throwing away a free signal.
3. **Scaffolded proof attempts help.** Rivin's Pólya–Szegő dataset went from 2.8% solved
   (raw statements) to 100% solved (statements + a partial, sometimes wrong, proof
   attempt as scaffolding). The attempt acts as a prior over the search tree.

### One-theorem-per-file convention

Mirror Harmonic's naming. For each Aristotle target, create a dedicated file:

```
proofs/Proofs/StatementOnly_Erdos340_SidonLowerBound.lean
proofs/Proofs/StatementOnly_Erdos340_SidonUpperBound.lean
proofs/Proofs/StatementOnly_Erdos728_GoodTriples.lean
```

Each file contains **exactly one** `theorem` declaration with a single `sorry`. No
supporting lemmas, no other sorries. If you need supporting lemmas, give each its own
`StatementOnly_*.lean` file and submit them as independent Aristotle projects.

### Required `/-` informal-problem block

Every `StatementOnly_*.lean` file **must** open with a `/- ... -/` block that states the
problem in English (and gives the answer when the statement is a "determine all"
problem). This mirrors Harmonic's IMO 2025 P1 file, which begins:

```lean
/-
A line in the plane is called sunny if it is not parallel to any of the x-axis,
the y-axis, and the line x+y=0.
Let n ≥ 3 be a given integer. Determine all nonnegative integers k such that
there exist n distinct lines in the plane satisfying both of the following:
- for all positive integers a and b with a+b ≤ n+1, the point (a, b) is on at
  least one of the lines; and
- exactly k of the n lines are sunny.

Answer: 0, 1, 3
-/
```

Use `/-` (not `/-!`) — Aristotle's parser still rejects `/-!` docstring sections in some
configurations.

### Standardized `set_option` block (verbatim from Harmonic)

Copy this block verbatim into every `StatementOnly_*.lean` file, immediately after the
import and `open` lines. It is taken from
[`HarmonicLean/StatementOnly_IMO2025P1.lean`](https://github.com/harmonic-ai/IMO2025/blob/main/HarmonicLean/StatementOnly_IMO2025P1.lean):

```lean
import HarmonicLean.Imports

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section
```

Notes on the block:

- `set_option maxHeartbeats 0` disables the heartbeat limit entirely so long
  searches do not abort on elaboration cost.
- `relaxedAutoImplicit false` and `autoImplicit false` force every variable to be
  bound explicitly — Aristotle's prompts assume this and can be misled by implicit
  insertions.
- The `pp.*` options make pretty-printed proof states unambiguous, so the value
  function sees the same syntax the elaborator does.
- `noncomputable section` matches Harmonic's project conventions and avoids
  spurious "failed to compile definition" errors on classical reasoning.
- The single `import HarmonicLean.Imports` is Harmonic's curated Mathlib bundle.
  If you do not have access to that import, substitute `import Mathlib` — the
  rest of the block is unchanged.

### Optional `-- Proof attempt:` scaffolding (Rivin pattern)

Igor Rivin's Pólya–Szegő experiment ([blog post](https://igorrivin.github.io/research/polya-szego-aristotle/),
[GitHub](https://github.com/igorrivin/polya-szego-lean)) showed that including a
partial proof attempt — **even one that is wrong** — flipped the success rate from
2.8% to 100% across 80 inequality problems. Treat the attempt as a *prior* the MCTS
can refine, not as a binding commitment.

Append it just below the theorem statement, like this:

```lean
namespace Erdos340Statement

theorem sidon_lower_bound (A : Finset ℕ) (hA : IsSidon A) :
    A.max' hne ≥ A.card * (A.card - 1) / 2 := by
  sorry

-- Proof attempt: a sketch of the expected argument. Aristotle is free to ignore
-- this; it exists only to seed the MCTS prior.
-- 1. Count ordered pairs (i, j) with i < j in A; there are card * (card - 1) / 2.
-- 2. By Sidon-ness, all pairwise differences are distinct, so the differences
--    inject into {1, ..., max'}.
-- 3. Conclude max' ≥ card * (card - 1) / 2.

end Erdos340Statement
```

The `-- Proof attempt:` block is plain Lean comments; it never affects elaboration.

### Async submission, polling, and concurrency

Submit jobs in **async mode** (do *not* pass `--wait` to `aristotlelib`). Aristotle jobs
take minutes to hours — sometimes 6+ hours for HARD problems — and a blocking submit ties
up the CLI for no benefit. Poll for status from the registry instead.

Concurrency limits observed from Harmonic:

- **Hard cap:** 5 simultaneous projects per account.
- **Soft cap:** ~3 simultaneous projects before the queue starts noticeably backing up.
- Our previous configuration targeting 10 concurrent projects exceeds the hard cap and
  produces queue timeouts; current pipelines should target ~3.

Recommended workflow with `aristotlelib`:

```bash
# Submit one StatementOnly_*.lean file as a project (async)
aristotle submit proofs/Proofs/StatementOnly_Erdos340_SidonLowerBound.lean

# Poll later — does NOT block
aristotle status <project-id>

# Retrieve the solved file when status is "complete"
aristotle fetch <project-id> -o aristotle-results/new/
```

For an MCP-style integration (one sorry at a time, persistent connection), see
[`septract/lean-aristotle-mcp`](https://github.com/septract/lean-aristotle-mcp), which
exposes a `prove_sorry` tool over MCP. That wrapper assumes the same one-theorem-per-file
discipline.

### Migration from the deprecated companion-file pattern

If you have an existing `*Aristotle.lean` companion file with N sorries:

1. Identify the theorem-sorries (skip `def`, `axiom`, and `True` placeholders).
2. For each remaining sorry, create a `StatementOnly_<Problem>_<LemmaName>.lean` file
   following the format above.
3. Copy the relevant minimal definitions/imports into each new file.
4. Add an informal `/-` block describing what that one lemma says and why it should be
   provable.
5. (Optional but recommended) Sketch a proof attempt in a `-- Proof attempt:` block.
6. Submit each new file as an independent project (respecting the ~3-concurrent cap).

Do not delete the original `*Aristotle.lean` companion file until the StatementOnly
submissions have succeeded — keep it as a fallback.

## Citations

Sources studied for the Harmonic Submission Format section (all consulted 2026-06-05):

- Harmonic, "Aristotle: IMO-level Automated Theorem Proving" — <https://arxiv.org/html/2510.01346v1>
  — System paper describing Aristotle's MCTS over Lean tactics conditioned on proof state, history, and informal proof; gold-medal IMO 2025 performance.
- `harmonic-ai/IMO2025` GitHub — <https://github.com/harmonic-ai/IMO2025>
  — Harmonic's official `StatementOnly_IMO2025P*.lean` submission files; canonical source for the file format, `set_option` block, and `/-` informal-problem block used in this guide.
- Igor Rivin, "Polya-Szego + Aristotle: From 2.8% to 100% Verified Proofs" — <https://igorrivin.github.io/research/polya-szego-aristotle/>
  — Empirical demonstration that adding partial proof-attempt scaffolding raises Aristotle's success rate from 2.8% to 100% on 80 inequality problems.
- `igorrivin/polya-szego-lean` GitHub — <https://github.com/igorrivin/polya-szego-lean>
  — The 80 verified inputs and outputs from Rivin's run; useful as a reference corpus for the scaffolding pattern.
- `aristotlelib` on PyPI — <https://pypi.org/project/aristotlelib/>
  — The official Aristotle CLI / client library we already use; documents async submission, polling, and the project-based submission model.
- `septract/lean-aristotle-mcp` GitHub — <https://github.com/septract/lean-aristotle-mcp>
  — MCP wrapper around Aristotle exposing a `prove_sorry` tool; reference implementation of the async per-sorry usage pattern.
- Aristotle landing page — <https://aristotle.harmonic.fun/>
  — Harmonic's public-facing description of Aristotle; confirms provenance (Harmonic, not Morph Labs) and high-level positioning.
