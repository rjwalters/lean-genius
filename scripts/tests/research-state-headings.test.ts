// Run: pnpm exec tsx scripts/tests/research-state-headings.test.ts
//
// #43679: parseState must recognise the per-iteration heading style that
// long-running problems use (`### Next action (S10)`, newest iteration
// first) and not silently produce empty focus / nextAction on regeneration,
// while still preferring the canonical `## Current Focus` / `## Next Action`
// sections when they exist.
import assert from 'node:assert/strict'
import { parseState } from '../research/build.js'

const registry = { phase: 'ACTIVE', started: '2026-01-01' } as Parameters<typeof parseState>[1]

const canonical = `# Current State
**Phase**: ACTIVE
## Current Focus
Prove the lemma.
## Next Action
Run the build.
## Iteration 2 (r, 2026-02-02) — S2 ACT: newer stuff
### Next action (S2)
Ignored: canonical wins.
`
let st = parseState(canonical, registry)
assert.equal(st.focus, 'Prove the lemma.')
assert.equal(st.nextAction, 'Run the build.')

const perIteration = `# Current State
**Phase**: ACTIVE
**Iteration**: 3

## Iteration 3 (researcher-2, 2026-03-03) — S3 ACT: close the discriminant chain

Body of the newest iteration.

### Next action (S3 ACT step 1)
Prove \`discr_eq_eight\` via the trace form.

Second paragraph stays in the section.

### Files modified
- Foo.lean

## Iteration 2 (researcher-1, 2026-02-02) — S2 PREP

### Next action (S2)
Older, must not win.
`
st = parseState(perIteration, registry)
assert.equal(st.nextAction, 'Prove `discr_eq_eight` via the trace form.\n\nSecond paragraph stays in the section.')
assert.equal(st.focus, 'S3 ACT: close the discriminant chain')

const stepsVariant = `## Iteration 1 (r, 2026-01-01)
### Next steps
Do the thing.
`
st = parseState(stepsVariant, registry)
assert.equal(st.nextAction, 'Do the thing.')
assert.equal(st.focus, '')

const nothing = `# Current State\n**Phase**: ACTIVE\n`
st = parseState(nothing, registry)
assert.equal(st.nextAction, '')
assert.equal(st.focus, '')

console.log('research-state-headings: 4 cases passed')
