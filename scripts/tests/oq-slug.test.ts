#!/usr/bin/env npx tsx
/**
 * Unit tests for the OQ slug / lineage foundation (issue #39825).
 *
 * Covers:
 *   - lineage computation (parentSlug / rootSlug / depth / ancestry)
 *   - bounded slug generation (sequential + hash), boundedness & stability
 *   - the migration planner (deterministic, no-op on shallow trees)
 *   - the redirect map loader + `_redirects` render format
 *
 * No test framework is installed in this repo; this is a self-contained tsx
 * script that exits non-zero if any assertion fails (mirrors scripts/tests/*).
 *
 * Run: pnpm tsx scripts/tests/oq-slug.test.ts
 */

import * as fs from 'fs'
import * as os from 'os'
import * as path from 'path'
import {
  oqDepth,
  lineageDepth,
  hasLineageSegment,
  parentSlug,
  rootSlug,
  computeLineage,
  ancestrySlugs,
  ancestrySlugsFromMeta,
  type LineageEntry,
  boundedSlugSequential,
  boundedSlugHash,
  shortHash,
  nextSequentialSlug,
} from '../../src/lib/oq-slug.js'
import { buildPlan } from '../gallery/migrate-oq-slugs.js'
import { loadRedirects, renderRedirectsFile } from '../gallery/build-redirects.js'

let PASS = 0
let FAIL = 0
function ok(desc: string, cond: boolean): void {
  if (cond) {
    PASS++
  } else {
    FAIL++
    console.error(`  FAIL: ${desc}`)
  }
}
function eq<T>(desc: string, actual: T, expected: T): void {
  const a = JSON.stringify(actual)
  const e = JSON.stringify(expected)
  if (a === e) {
    PASS++
  } else {
    FAIL++
    console.error(`  FAIL: ${desc}\n        expected ${e}\n        got      ${a}`)
  }
}

const DEEP = 'abel-ruffini-oq-04-oq-02-oq-02-oq-08-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01'

// --- depth ---------------------------------------------------------------
eq('oqDepth of the 11-hop abel-ruffini chain', oqDepth(DEEP), 11)
eq('oqDepth of a root', oqDepth('abel-ruffini'), 0)
eq('oqDepth of empty', oqDepth(''), 0)
eq('lineageDepth counts mixed types', lineageDepth('erdos-1018-oq-04-incomplete-01-oq-01'), 3)
eq('oqDepth ignores incomplete hops', oqDepth('erdos-1018-oq-04-incomplete-01-oq-01'), 2)
ok('hasLineageSegment on a chain', hasLineageSegment('a-oq-01'))
ok('hasLineageSegment false on a root', !hasLineageSegment('pythagorean-theorem'))
// A base slug that merely contains "-plus-1" is not a lineage segment.
eq('non-lineage numeric suffix is depth 0', oqDepth('n-plus-1'), 0)
ok('non-lineage numeric suffix has no lineage segment', !hasLineageSegment('n-plus-1'))

// --- parent / root -------------------------------------------------------
eq('parent drops the last oq hop', parentSlug('a-oq-04-oq-02'), 'a-oq-04')
eq('parent of a single-hop child is the root', parentSlug('a-oq-04'), 'a')
eq('parent of a root is null', parentSlug('abel-ruffini'), null)
eq('root strips all hops', rootSlug(DEEP), 'abel-ruffini')
eq('root strips mixed types', rootSlug('erdos-1018-oq-04-incomplete-01-oq-01'), 'erdos-1018')
eq('root of a root is itself', rootSlug('pythagorean-theorem'), 'pythagorean-theorem')
eq('computeLineage bundles parent+root', computeLineage('a-oq-04-oq-02'), {
  parentSlug: 'a-oq-04',
  rootSlug: 'a',
})
eq('ancestrySlugs root→parent order', ancestrySlugs('a-oq-04-oq-02'), ['a', 'a-oq-04'])
eq('ancestrySlugs of a root is empty', ancestrySlugs('a'), [])

// --- bounded slug generation --------------------------------------------
eq('sequential bounded slug format', boundedSlugSequential('abel-ruffini', 7), 'abel-ruffini-oq007')
eq('sequential normalizes a deep root arg', boundedSlugSequential(DEEP, 7), 'abel-ruffini-oq007')
// Boundedness: the minted slug does NOT grow with ancestry depth.
ok(
  'bounded slug is shorter than the deep chain',
  boundedSlugSequential(rootSlug(DEEP), 999).length < DEEP.length
)
// A bounded slug reads as depth 0 (not re-parsed as another hop).
eq('bounded slug has oqDepth 0', oqDepth(boundedSlugSequential('abel-ruffini', 7)), 0)
// A bounded slug's parent/root resolve back to the root.
eq('parent of a bounded slug is the root', parentSlug('abel-ruffini-oq007'), 'abel-ruffini')
eq('root of a bounded slug is the root', rootSlug('abel-ruffini-oq007'), 'abel-ruffini')
ok('sequential rejects non-positive seq', (() => {
  try {
    boundedSlugSequential('a', 0)
    return false
  } catch {
    return true
  }
})())

// hash form: stable + bounded + collision-resistant across distinct paths
eq('hash is deterministic', boundedSlugHash(DEEP), boundedSlugHash(DEEP))
ok('hash slug shares the root prefix', boundedSlugHash(DEEP).startsWith('abel-ruffini-oq'))
ok(
  'distinct ancestries get distinct hash slugs',
  boundedSlugHash('a-oq-01-oq-02') !== boundedSlugHash('a-oq-02-oq-01')
)
eq('shortHash length honored', shortHash('anything', 6).length, 6)
eq('shortHash is stable', shortHash('erdos-396'), shortHash('erdos-396'))

// nextSequentialSlug picks max+1 over existing bounded siblings
eq(
  'nextSequentialSlug seeds past existing bounded siblings',
  nextSequentialSlug('erdos-396', ['erdos-396-oq001', 'erdos-396-oq004', 'unrelated-oq009']),
  'erdos-396-oq005'
)
eq(
  'nextSequentialSlug ignores legacy -oq-NN siblings',
  nextSequentialSlug('erdos-396', ['erdos-396-oq-01', 'erdos-396-oq-02']),
  'erdos-396-oq001'
)

// --- migration planner ---------------------------------------------------
const sample = [
  'abel-ruffini',
  'abel-ruffini-oq-01',
  'abel-ruffini-oq-01-oq-02',
  'abel-ruffini-oq-01-oq-02-oq-03', // depth 3 — below default threshold 4
  'abel-ruffini-oq-01-oq-02-oq-03-oq-04', // depth 4 — migrate
  'erdos-396-oq-01-oq-01-oq-02-oq-02', // depth 4 — migrate
  'erdos-396-oq-01-oq-01-oq-02-oq-03', // depth 4 — migrate (same root)
]
const plan4 = buildPlan(sample, { minDepth: 4, useHash: false })
eq('planner selects exactly the depth>=4 entries', plan4.length, 3)
ok(
  'planner mints bounded, non-growing slugs',
  plan4.every((r) => r.newSlug.length < r.oldSlug.length && oqDepth(r.newSlug) === 0)
)
ok(
  'planner sets root correctly',
  plan4.every((r) => r.rootSlug === rootSlug(r.oldSlug))
)
// Per-root sequential numbering with no collisions.
const erdosRows = plan4.filter((r) => r.rootSlug === 'erdos-396').map((r) => r.newSlug)
eq('erdos-396 descendants numbered sequentially', erdosRows, ['erdos-396-oq001', 'erdos-396-oq002'])
ok('all new slugs unique', new Set(plan4.map((r) => r.newSlug)).size === plan4.length)
// Deterministic: same input → same plan.
eq('planner is deterministic', buildPlan(sample, { minDepth: 4, useHash: false }), plan4)
// Higher threshold shrinks the cohort.
eq('min-depth 5 yields no migrations here', buildPlan(sample, { minDepth: 5, useHash: false }).length, 0)

// --- redirect map + _redirects format -----------------------------------
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'oq-redirects-'))
const emptyPath = path.join(tmp, 'empty.json')
fs.writeFileSync(
  emptyPath,
  JSON.stringify({ $comment: 'meta ignored', redirects: {} })
)
eq('loadRedirects on the empty foundation map', loadRedirects(emptyPath), {})

const popPath = path.join(tmp, 'pop.json')
fs.writeFileSync(
  popPath,
  JSON.stringify({
    $comment: 'x',
    redirects: {
      'abel-ruffini-oq-04-oq-02': 'abel-ruffini-oq007',
      'erdos-396-oq-01-oq-01': 'erdos-396-oq001',
    },
  })
)
eq('loadRedirects drops $-metadata and keeps pairs', loadRedirects(popPath), {
  'abel-ruffini-oq-04-oq-02': 'abel-ruffini-oq007',
  'erdos-396-oq-01-oq-01': 'erdos-396-oq001',
})

const rendered = renderRedirectsFile(loadRedirects(popPath))
ok('render emits a 301 rule per entry', rendered.includes('/proof/abel-ruffini-oq-04-oq-02  /proof/abel-ruffini-oq007  301'))
ok('render sorts rules (erdos before... no: abel before erdos)',
  rendered.indexOf('/proof/abel-ruffini') < rendered.indexOf('/proof/erdos-396'))
ok('render has a header comment', rendered.startsWith('# Auto-generated'))

// invalid slugs are rejected
const badPath = path.join(tmp, 'bad.json')
fs.writeFileSync(badPath, JSON.stringify({ redirects: { 'ok-slug': 'bad slug with spaces' } }))
ok('loadRedirects rejects an invalid target slug', (() => {
  try {
    loadRedirects(badPath)
    return false
  } catch {
    return true
  }
})())

const selfPath = path.join(tmp, 'self.json')
fs.writeFileSync(selfPath, JSON.stringify({ redirects: { 'same-slug': 'same-slug' } }))
ok('loadRedirects rejects a self-redirect', (() => {
  try {
    loadRedirects(selfPath)
    return false
  } catch {
    return true
  }
})())

fs.rmSync(tmp, { recursive: true, force: true })

// --- ancestrySlugsFromMeta (meta-preferring lineage, #39828) --------------
{
  // Resolver over a small lineage table. Entries WITHOUT a parentSlug field
  // (undefined) model legacy entries that carry no lineage metadata.
  const table: Record<string, LineageEntry> = {
    r: { slug: 'r', parentSlug: null }, // known root
    'r-oq001': { slug: 'r-oq001', parentSlug: 'r-oq-01-oq-01' }, // migrated, legacy parent
    'r-oq002': { slug: 'r-oq002', parentSlug: 'r-oq001' }, // migrated, bounded parent
    'x-oq-01': { slug: 'x-oq-01', parentSlug: undefined }, // legacy, no meta
  }
  const resolve = (s: string): LineageEntry | undefined => table[s]

  eq('meta walk: root has empty ancestry', ancestrySlugsFromMeta('r', resolve), [])
  eq(
    'meta walk: bounded slug recovers legacy parent ancestry',
    ancestrySlugsFromMeta('r-oq001', resolve),
    ['r', 'r-oq-01', 'r-oq-01-oq-01']
  )
  eq(
    'meta walk: chains through a migrated bounded parent',
    ancestrySlugsFromMeta('r-oq002', resolve),
    ['r', 'r-oq-01', 'r-oq-01-oq-01', 'r-oq001']
  )
  eq(
    'meta walk: entry without lineage metadata falls back to slug-parsing',
    ancestrySlugsFromMeta('x-oq-01', resolve),
    ancestrySlugs('x-oq-01')
  )
  eq(
    'meta walk: unknown slug falls back to slug-parsing',
    ancestrySlugsFromMeta('y-oq-03-oq-01', resolve),
    ancestrySlugs('y-oq-03-oq-01')
  )
  // Cycle guard: a → b → a must terminate.
  const cyclic: Record<string, LineageEntry> = {
    a: { slug: 'a', parentSlug: 'b' },
    b: { slug: 'b', parentSlug: 'a' },
  }
  ok('meta walk: cycle-guarded (terminates)', Array.isArray(ancestrySlugsFromMeta('a', (s) => cyclic[s])))
}

// --- summary -------------------------------------------------------------
console.log(`\noq-slug tests: ${PASS} passed, ${FAIL} failed`)
if (FAIL > 0) process.exit(1)
