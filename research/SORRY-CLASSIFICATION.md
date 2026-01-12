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

## Success Story: Erdős #728

Aristotle successfully proved Erdős #728 in 6 hours:
- Input: File with HARD sorries only (no OPEN conjectures)
- Output: 1,416 lines of complete proof
- Result: Zero sorries, builds successfully

This demonstrates that HARD problems are worth overnight runs!
