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

## Pre-Submission Checklist

Before running `./research/scripts/aristotle-submit.sh`:

1. **List all sorries:**
   ```bash
   grep -n "sorry" your-file.lean
   ```

2. **Classify each one:**
   - [ ] Is this a known result? → HARD (submit)
   - [ ] Is this computational? → TRIVIAL (submit)
   - [ ] Is this an open conjecture? → OPEN (do NOT submit)

3. **Separate if needed:**
   If your file contains OPEN conjectures, create a separate file:
   ```bash
   # Create provable-only version
   cp Erdos340.lean Erdos340-provable.lean
   # Remove or comment out OPEN theorems
   ```

4. **Submit provable sorries only:**
   ```bash
   ./research/scripts/aristotle-submit.sh Erdos340-provable.lean erdos-340 "Excluding open conjecture"
   ```

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

## Success Story: Erdős #728

Aristotle successfully proved Erdős #728 in 6 hours:
- Input: File with HARD sorries only (no OPEN conjectures)
- Output: 1,416 lines of complete proof
- Result: Zero sorries, builds successfully

This demonstrates that HARD problems are worth overnight runs!

## Success Story: MotivicFlagMapsProvable

Aristotle proved ALL 10 theorems in an overnight run:
- Input: File with complete definitions, only theorem sorries
- Theorems: GL5_class, Fl5_class, GLn_product_expansion, computeA cases
- Result: Zero sorries, builds successfully

**Key**: All definitions were complete. Only theorems had sorries.

## Failure Patterns (January 2026)

Jobs that returned "complete" but made no progress:

| Problem | Issue | Outcome |
|---------|-------|---------|
| erdos-58 | `chromaticNumber` definition sorry | Theorems axiomatized |
| erdos-59 | `turanNumber`, `countFreeGraphs` def sorries | No proofs |
| erdos-97 | `danzerPoints` definition sorry | Construction skipped |
| erdos-39/494/605/645/650 | Placeholder `True` theorems | No meaningful work |

**Lesson**: Only submit files where definitions are complete.

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
