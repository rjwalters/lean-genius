# Aristotle MCP Server

MCP (Model Context Protocol) server for integrating [Harmonic Aristotle](https://aristotle.harmonic.fun/) theorem proving into Claude Code workflows.

## Overview

This server enables Claude to use Aristotle's powerful proof search capabilities during the OODA loop research process. It provides a strategic integration where:

- **Claude controls strategy** (what to prove, how to structure lemmas)
- **Aristotle handles tactics** (filling sorries, finding proofs)

## Prerequisites

1. **uv** - Modern Python package manager
   ```bash
   curl -LsSf https://astral.sh/uv/install.sh | sh
   ```

2. **Aristotle API Key** - Get from [aristotle.harmonic.fun](https://aristotle.harmonic.fun/)

3. **Set environment variable**:
   ```bash
   # Add to ~/.zshrc (Mac) or ~/.bashrc (Linux)
   export ARISTOTLE_API_KEY='arstl_your_key_here'
   ```

## Installation

```bash
cd mcp-servers/aristotle
pnpm install
pnpm build
```

## Configuration

Add to your Claude Code MCP config (`~/.claude/config.json`):
```json
{
  "mcpServers": {
    "aristotle": {
      "command": "node",
      "args": ["/path/to/lean-genius/mcp-servers/aristotle/dist/index.js"],
      "env": {
        "ARISTOTLE_API_KEY": "arstl_your_key_here"
      }
    }
  }
}
```

## Available Tools

### `aristotle_prove`

Submit a Lean 4 file with sorries for automated proof completion.

```
Use when:
- You've structured the proof but have sorries you can't fill
- Manual proof search has stalled
- Complex lemmas requiring deep search
```

### `aristotle_informal`

Submit a natural language math problem for formalization and proof.

```
Use cases:
- Convert textbook problems to Lean
- Explore conjectures (true or false?)
- Get counterexamples for invalid statements
- Quick sanity checks during ORIENT phase
```

### `aristotle_version`

Verify Aristotle CLI is working and check version.

## OODA Loop Integration

The MCP server is designed to integrate with the research OODA loop:

### OBSERVE Phase
- Claude identifies the problem, reads existing proofs
- No Aristotle needed yet

### ORIENT Phase
- Claude analyzes proof structure, identifies lemmas needed
- Can use `aristotle_informal` to sanity-check conjectures
- Aristotle can provide counterexamples for invalid statements

### DECIDE Phase
- Claude decides which sorries to attempt manually vs delegate
- **Delegation criteria:**
  - Technical lemmas with clear specifications → Aristotle
  - Novel mathematical insights needed → Manual first
  - Stuck after 2-3 manual attempts → Escalate to Aristotle

### ACT Phase
- Claude writes proof skeleton with sorries
- Uses `aristotle_prove` for delegated sorries
- **Async workflow:**
  1. Submit to Aristotle (returns project_id)
  2. Continue working on other parts
  3. Check `aristotle_status` periodically
  4. Retrieve with `aristotle_solution` when complete

### LEARN Phase
- Analyze Aristotle's solutions for patterns
- Document what worked/didn't work
- Update proof strategy based on results

## Example Workflow

```lean
-- proof_skeleton.lean
theorem my_theorem : ∀ n : ℕ, n + 0 = n := by
  intro n
  sorry  -- Claude: "This is a standard lemma, delegate to Aristotle"
```

Claude's process:
1. Creates skeleton with strategic sorries
2. Calls `aristotle_prove` with the file
3. Gets project_id, continues other work
4. Checks status after 5 minutes
5. Retrieves solution, integrates into proof
6. Documents the approach in LEARN phase

## Comparison: Manual vs Aristotle

| Aspect | Manual (Claude) | Aristotle |
|--------|-----------------|-----------|
| Strategic planning | ✅ Excellent | ❌ None |
| Novel insights | ✅ Can reason | ❌ Search only |
| Technical lemmas | ⚠️ Slow | ✅ Fast |
| Counterexamples | ⚠️ Limited | ✅ Strong |
| Transparency | ✅ Full | ⚠️ Black box |
| Context awareness | ✅ Full conversation | ⚠️ File-level only |

## Best Practices

1. **Structure first**: Write clean proof skeletons before delegating
2. **Good names**: Use descriptive lemma names and type signatures
3. **Small sorries**: Break complex goals into multiple small sorries
4. **Include context**: Pass relevant import files
5. **Check early**: Don't wait hours - check status after 5-10 min
6. **Learn from solutions**: Study Aristotle's tactics for patterns

## Troubleshooting

### "API key not set"
Ensure `ARISTOTLE_API_KEY` is in your environment or MCP config.

### "Could not find proof"
- Try breaking into smaller lemmas
- Provide more context files
- Check if the statement is actually provable
- Look for typos in types

### Timeout
Complex proofs can take hours. Use async mode and check periodically.

## License

MIT
