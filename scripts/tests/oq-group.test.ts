#!/usr/bin/env npx tsx
/**
 * Unit tests for the gallery OQ grouping (issue #39826, epic #39821).
 *
 * Covers:
 *   - grouping a root problem's OQ descendants under one group
 *   - header selection (true root vs shallowest-descendant fallback)
 *   - descendant ordering (root→leaf) and group ordering (input order preserved)
 *   - status classification + rollup summary aggregation & formatting
 *
 * No test framework is installed in this repo; this is a self-contained tsx
 * script that exits non-zero if any assertion fails (mirrors scripts/tests/*).
 *
 * Run: pnpm tsx scripts/tests/oq-group.test.ts
 */

import {
  groupListings,
  classifyListing,
  summarize,
  formatRollupSummary,
} from '../../src/lib/oq-group.js'
import type { ProofListing } from '../../src/types/proof.js'

let PASS = 0
let FAIL = 0
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
function ok(desc: string, cond: boolean): void {
  if (cond) {
    PASS++
  } else {
    FAIL++
    console.error(`  FAIL: ${desc}`)
  }
}

/** Minimal ProofListing factory — only slug/status/badge/title matter here. */
function L(
  slug: string,
  status: ProofListing['status'] = 'verified',
  badge?: ProofListing['badge']
): ProofListing {
  return {
    id: slug,
    title: slug,
    slug,
    description: '',
    status,
    badge,
    tags: [],
    annotationCount: 0,
  }
}

// --- classifyListing -------------------------------------------------------
eq('verified status → verified', classifyListing(L('a', 'verified')), 'verified')
eq('complete status → verified', classifyListing(L('a', 'complete')), 'verified')
eq('axiomatized status → axiomatized', classifyListing(L('a', 'axiomatized')), 'axiomatized')
eq('open-question status → wip', classifyListing(L('a', 'open-question')), 'wip')
eq('pending status → wip', classifyListing(L('a', 'pending')), 'wip')
eq('wip badge overrides status → wip', classifyListing(L('a', 'verified', 'wip')), 'wip')
eq('disputed status → other', classifyListing(L('a', 'disputed')), 'other')

// --- summarize -------------------------------------------------------------
{
  const s = summarize([
    L('a-oq-01', 'verified'),
    L('a-oq-02', 'verified'),
    L('a-oq-03', 'verified', 'wip'),
    L('a-oq-04', 'axiomatized'),
  ])
  eq('summary total', s.total, 4)
  eq('summary verified', s.verified, 2)
  eq('summary wip', s.wip, 1)
  eq('summary axiomatized', s.axiomatized, 1)
  eq('summary other', s.other, 0)
}

// --- formatRollupSummary ---------------------------------------------------
eq(
  'format 15 sub-results (14 verified, 1 WIP)',
  formatRollupSummary({ total: 15, verified: 14, axiomatized: 0, wip: 1, other: 0 }),
  '15 sub-results (14 verified, 1 WIP)'
)
eq('format singular', formatRollupSummary({ total: 1, verified: 1, axiomatized: 0, wip: 0, other: 0 }), '1 sub-result (1 verified)')
eq('format empty → null', formatRollupSummary({ total: 0, verified: 0, axiomatized: 0, wip: 0, other: 0 }), null)

// --- groupListings: erdos-396-style family --------------------------------
{
  const listings: ProofListing[] = [
    L('erdos-396', 'axiomatized', 'wip'),
    L('erdos-396-oq-04', 'verified'),
    L('erdos-396-oq-04-oq-01', 'verified'),
    L('erdos-396-oq-04-oq-01-oq-01', 'verified'),
    L('erdos-396-oq-04-oq-01-oq-02', 'verified', 'wip'),
  ]
  const groups = groupListings(listings)
  eq('one group for the erdos-396 family', groups.length, 1)
  const g = groups[0]
  eq('group root', g.rootSlug, 'erdos-396')
  eq('header is the true root', g.header.slug, 'erdos-396')
  eq('descendant count', g.descendants.length, 4)
  eq(
    'descendants ordered root→leaf',
    g.descendants.map((d) => d.slug),
    [
      'erdos-396-oq-04',
      'erdos-396-oq-04-oq-01',
      'erdos-396-oq-04-oq-01-oq-01',
      'erdos-396-oq-04-oq-01-oq-02',
    ]
  )
  eq('rollup counts verified', g.summary.verified, 3)
  eq('rollup counts wip', g.summary.wip, 1)
}

// --- groupListings: header fallback when the root entry is absent ----------
{
  const listings: ProofListing[] = [
    L('abel-ruffini-oq-04', 'verified'),
    L('abel-ruffini-oq-04-oq-02', 'verified'),
  ]
  const groups = groupListings(listings)
  eq('one group even without the true root', groups.length, 1)
  eq('root slug still computed', groups[0].rootSlug, 'abel-ruffini')
  eq('header falls back to shallowest', groups[0].header.slug, 'abel-ruffini-oq-04')
  eq('remaining are descendants', groups[0].descendants.map((d) => d.slug), ['abel-ruffini-oq-04-oq-02'])
}

// --- groupListings: standalone entries + group ordering --------------------
{
  const listings: ProofListing[] = [
    L('pythagorean-theorem'),
    L('erdos-396'),
    L('erdos-396-oq-01'),
    L('cantor-diagonal'),
  ]
  const groups = groupListings(listings)
  eq('three groups', groups.length, 3)
  eq('group order preserves input order', groups.map((g) => g.rootSlug), [
    'pythagorean-theorem',
    'erdos-396',
    'cantor-diagonal',
  ])
  ok('standalone entries have no descendants', groups[0].descendants.length === 0 && groups[2].descendants.length === 0)
  eq('grouped entry has one descendant', groups[1].descendants.length, 1)
}

// --- groupListings: meta-preferring path (bounded slugs, #39828) ----------
{
  // Listing factory carrying the backfilled lineage meta. Bounded slugs read
  // as lineageDepth 0, so correct grouping/ordering MUST come from the meta.
  function LM(
    slug: string,
    rootSlug: string,
    parentSlug: string | null,
    status: ProofListing['status'] = 'verified'
  ): ProofListing {
    return { ...L(slug, status), rootSlug, parentSlug }
  }

  const listings: ProofListing[] = [
    L('erdos-396', 'axiomatized', 'wip'),
    // Deliberately out of depth order to exercise meta-depth sorting.
    LM('erdos-396-oq003', 'erdos-396', 'erdos-396-oq002'),
    LM('erdos-396-oq001', 'erdos-396', 'erdos-396'),
    LM('erdos-396-oq002', 'erdos-396', 'erdos-396-oq001'),
    // A bounded slug whose SLUG-parsed root ('weird') differs from its meta
    // rootSlug — grouping must prefer the meta field and land under erdos-396.
    LM('weird-oq009', 'erdos-396', 'erdos-396-oq003'),
  ]
  const groups = groupListings(listings)
  eq('meta grouping: single group despite mismatched slug root', groups.length, 1)
  const g = groups[0]
  eq('meta grouping: root from meta field', g.rootSlug, 'erdos-396')
  eq('meta grouping: header is the true root', g.header.slug, 'erdos-396')
  eq(
    'meta grouping: descendants ordered by meta-depth (root→leaf)',
    g.descendants.map((d) => d.slug),
    ['erdos-396-oq001', 'erdos-396-oq002', 'erdos-396-oq003', 'weird-oq009']
  )
  eq('meta grouping: all four descendants captured', g.descendants.length, 4)
}

// --- groupListings: header fallback via meta-depth when root absent --------
{
  function LM(slug: string, rootSlug: string, parentSlug: string | null): ProofListing {
    return { ...L(slug), rootSlug, parentSlug }
  }
  const listings: ProofListing[] = [
    LM('e-oq002', 'e', 'e-oq001'),
    LM('e-oq001', 'e', 'e'), // shallowest (depth 1) — should become header
  ]
  const groups = groupListings(listings)
  eq('meta fallback: one group', groups.length, 1)
  eq('meta fallback: header is shallowest by meta-depth', groups[0].header.slug, 'e-oq001')
  eq('meta fallback: remaining is descendant', groups[0].descendants.map((d) => d.slug), ['e-oq002'])
}

// ---------------------------------------------------------------------------
if (FAIL > 0) {
  console.error(`\noq-group.test: ${FAIL} failed, ${PASS} passed`)
  process.exit(1)
}
console.log(`oq-group.test: all ${PASS} assertions passed`)
