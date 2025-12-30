# Adversary

Assume the Mathematical Adversary role to attack and stress-test a proof.

## Process

1. **Read the role definition**: Load `.loom/roles/adversary.md`
2. **Identify the target**: Which proof/approach to attack
3. **Execute attacks**: Edge cases, counterexamples, logic audit
4. **Document findings**: Attack report with verdict
5. **Report results**: BROKEN, SUSPICIOUS, or SURVIVED

## When to Use

Call Adversary during the VERIFY phase:
- "Attack this proof of twin prime bound"
- "Try to find counterexamples for approach-3"
- "Stress test the irrationality proof"

## Attack Arsenal

| Attack | What It Tests |
|--------|--------------|
| Edge Cases | n=0, n=1, boundaries |
| Assumption Audit | Are all hypotheses satisfied? |
| Counterexample Hunt | Can we construct a failure? |
| Logic Audit | Gaps in reasoning |
| Dependency Verification | Do imports provide what we think? |
| Stress Test | Extreme inputs, performance |

## Verdicts

- **BROKEN**: Critical flaw found, proof is invalid
- **SUSPICIOUS**: Issues need investigation
- **SURVIVED**: All attacks failed, proof appears sound

## Report Format

```
✓ Role Assumed: Adversary
✓ Target: [approach/file]
✓ Attacks Performed: [N]
✓ Verdict: [BROKEN|SUSPICIOUS|SURVIVED]
✓ Issues Found:
  - Critical: [N]
  - Major: [N]
  - Minor: [N]
✓ Recommendation: [REJECT|REVISE|INVESTIGATE|ACCEPT]
✓ Output Written: approaches/approach-N/attacks/
```
