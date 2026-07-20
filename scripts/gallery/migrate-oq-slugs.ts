#!/usr/bin/env npx tsx
/**
 * OQ slug migration planner (issue #39825, epic #39821).
 *
 * Computes, for every gallery entry that carries an OQ ancestry in its slug:
 *   - the bounded replacement slug (`<root>-oqNNN`, sequential per root),
 *   - the `parentSlug` / `rootSlug` lineage values,
 * and PRINTS the plan. It writes NOTHING by default — this is a dry run.
 *
 * The actual mass migration (renaming directories, backfilling lineage into
 * meta.json, and populating src/data/proofs/redirects.json) is deferred to
 * issue #39828, which will invoke this with `--apply`.
 *
 * Usage:
 *   pnpm tsx scripts/gallery/migrate-oq-slugs.ts            # dry run (default)
 *   pnpm tsx scripts/gallery/migrate-oq-slugs.ts --json     # machine-readable plan
 *   pnpm tsx scripts/gallery/migrate-oq-slugs.ts --min-depth 4
 *   pnpm tsx scripts/gallery/migrate-oq-slugs.ts --apply    # gated; NOT run in #39825
 *
 * Options:
 *   --min-depth N   Only re-slug entries with >= N OQ hops (default 4, matching
 *                   the epic's ~347-entry cohort). Lineage (parent/root) is
 *                   still reported for shallower entries.
 *   --hash          Use the stable hash bounded form instead of sequential.
 *   --json          Emit the plan as JSON instead of a table.
 *   --apply         Execute the plan (rename dirs, backfill lineage, write
 *                   redirects). GATED — prints a notice and exits unless the
 *                   migration is explicitly authorized under #39828.
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'
import {
  oqDepth,
  lineageDepth,
  rootSlug,
  parentSlug,
  boundedSlugSequential,
  boundedSlugHash,
} from '../../src/lib/oq-slug.js'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)

const PROOFS_DATA_DIR = path.join(__dirname, '../../src/data/proofs')
const REDIRECTS_SOURCE = path.join(PROOFS_DATA_DIR, 'redirects.json')

interface PlanRow {
  oldSlug: string
  newSlug: string
  parentSlug: string | null
  rootSlug: string
  oqDepth: number
  lineageDepth: number
}

interface Args {
  minDepth: number
  useHash: boolean
  json: boolean
  apply: boolean
}

function parseArgs(argv: string[]): Args {
  const args: Args = { minDepth: 4, useHash: false, json: false, apply: false }
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    if (a === '--apply') args.apply = true
    else if (a === '--hash') args.useHash = true
    else if (a === '--json') args.json = true
    else if (a === '--min-depth') args.minDepth = parseInt(argv[++i], 10)
    else if (a.startsWith('--min-depth=')) args.minDepth = parseInt(a.split('=')[1], 10)
  }
  if (!Number.isInteger(args.minDepth) || args.minDepth < 0) args.minDepth = 4
  return args
}

/** Directory names under src/data/proofs that are real gallery entries. */
function listEntrySlugs(dir: string): string[] {
  if (!fs.existsSync(dir)) return []
  return fs
    .readdirSync(dir, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name)
    .filter((name) => fs.existsSync(path.join(dir, name, 'meta.json')))
}

/**
 * Build the migration plan. Pure over its inputs so it is unit-testable:
 * given the full set of existing slugs and options, returns the ordered plan.
 *
 * Sequential numbering is deterministic: within each root, the descendants that
 * meet the depth threshold are sorted lexicographically and numbered starting
 * after the highest bounded ordinal already present under that root (so a
 * re-run, or a partially-migrated tree, does not renumber existing entries).
 */
export function buildPlan(allSlugs: string[], opts: { minDepth: number; useHash: boolean }): PlanRow[] {
  const existing = new Set(allSlugs)

  // Seed each root's sequential counter past any bounded slug already present.
  const seqByRoot = new Map<string, number>()
  for (const slug of allSlugs) {
    const root = rootSlug(slug)
    const m = new RegExp(`^${escapeRegExp(root)}-oq(\\d+)$`).exec(slug)
    if (m) {
      const n = parseInt(m[1], 10)
      seqByRoot.set(root, Math.max(seqByRoot.get(root) ?? 0, n))
    }
  }

  // Candidates: entries at/over the depth threshold, grouped by root, sorted
  // for stable numbering.
  const candidates = allSlugs
    .filter((s) => oqDepth(s) >= opts.minDepth)
    .sort((a, b) => (rootSlug(a) === rootSlug(b) ? (a < b ? -1 : a > b ? 1 : 0) : rootSlug(a) < rootSlug(b) ? -1 : 1))

  const plan: PlanRow[] = []
  for (const oldSlug of candidates) {
    const root = rootSlug(oldSlug)
    let newSlug: string
    if (opts.useHash) {
      newSlug = boundedSlugHash(oldSlug)
    } else {
      let seq = (seqByRoot.get(root) ?? 0) + 1
      newSlug = boundedSlugSequential(root, seq)
      // Guard against an (extremely unlikely) collision with an unrelated slug.
      while (existing.has(newSlug)) {
        seq += 1
        newSlug = boundedSlugSequential(root, seq)
      }
      seqByRoot.set(root, seq)
    }
    existing.add(newSlug)
    plan.push({
      oldSlug,
      newSlug,
      parentSlug: parentSlug(oldSlug),
      rootSlug: root,
      oqDepth: oqDepth(oldSlug),
      lineageDepth: lineageDepth(oldSlug),
    })
  }
  return plan
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
}

function printTable(plan: PlanRow[]): void {
  if (plan.length === 0) {
    console.log('No entries at or over the depth threshold — nothing to migrate.')
    return
  }
  console.log(`\nOLD SLUG  →  NEW SLUG   (parent | root | oqDepth)\n`)
  for (const r of plan) {
    console.log(`  ${r.oldSlug}`)
    console.log(`    → ${r.newSlug}`)
    console.log(`      parent=${r.parentSlug ?? '(root)'}  root=${r.rootSlug}  oqDepth=${r.oqDepth}`)
  }
  // Depth histogram over the migrated cohort.
  const hist = new Map<number, number>()
  for (const r of plan) hist.set(r.oqDepth, (hist.get(r.oqDepth) ?? 0) + 1)
  console.log(`\nMigrating ${plan.length} entr${plan.length === 1 ? 'y' : 'ies'}. OQ-depth histogram:`)
  for (const d of [...hist.keys()].sort((a, b) => a - b)) {
    console.log(`  depth ${d}: ${hist.get(d)}`)
  }
}

function main(): void {
  const args = parseArgs(process.argv.slice(2))
  const allSlugs = listEntrySlugs(PROOFS_DATA_DIR)
  const plan = buildPlan(allSlugs, { minDepth: args.minDepth, useHash: args.useHash })

  if (args.apply) {
    console.error(
      '\n✋ --apply is gated. The mass re-slug (renaming ~347 directories, backfilling\n' +
        '   parentSlug/rootSlug, and populating redirects.json) is deferred to issue\n' +
        '   #39828. This foundation script only PRINTS the plan.\n\n' +
        '   To execute the migration under #39828, remove this guard in a dedicated PR\n' +
        '   after review. Refusing to write anything now.\n'
    )
    process.exitCode = 2
    return
  }

  if (args.json) {
    console.log(
      JSON.stringify(
        {
          minDepth: args.minDepth,
          scheme: args.useHash ? 'hash' : 'sequential',
          totalEntries: allSlugs.length,
          migrating: plan.length,
          redirectsSource: path.relative(path.join(__dirname, '../..'), REDIRECTS_SOURCE),
          plan,
        },
        null,
        2
      )
    )
  } else {
    console.log(`Scanned ${allSlugs.length} gallery entries under src/data/proofs/.`)
    console.log(`Scheme: ${args.useHash ? 'hash' : 'sequential'}; min OQ depth: ${args.minDepth}.`)
    printTable(plan)
    console.log(`\n(Dry run — no files changed. Mass migration is deferred to #39828.)`)
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  main()
}
