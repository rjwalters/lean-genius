# Chronicler

Assume the Research Chronicler role to document and synthesize research learnings.

## Process

1. **Read the role definition**: Load `.loom/roles/chronicler.md`
2. **Identify work to document**: Failed approach or recent findings
3. **Write post-mortem**: Thorough documentation of what was tried
4. **Extract insights**: Generalizable lessons from specific failures
5. **Update knowledge base**: Add to knowledge.md

## When to Use

Call Chronicler during the LEARN phase:
- "Document why approach-3 failed"
- "Extract insights from today's work"
- "Update the knowledge base"

## Output Types

| Document | Purpose | Location |
|----------|---------|----------|
| Post-Mortem | Detailed failure analysis | approaches/approach-N/post-mortem.md |
| Insights | Generalizable learnings | knowledge.md |
| Cross-Problem | Patterns across problems | .loom/research/knowledge/ |

## Quality Standards

Good post-mortems:
- Specific about what failed and why
- Extract actionable insights
- Link to evidence (files, attempts)
- Suggest next steps

Good insights:
- One clear learning per insight
- Evidence-based
- Properly categorized
- Actionable

## Report Format

```
✓ Role Assumed: Chronicler
✓ Problem: [problem-slug]
✓ Work Documented:
  - Post-mortem for approach [N]
  - [X] insights extracted
  - Knowledge base updated
✓ Key Insights:
  1. [Brief insight 1]
  2. [Brief insight 2]
✓ Recommendations:
  - [What to try next based on learnings]
```
