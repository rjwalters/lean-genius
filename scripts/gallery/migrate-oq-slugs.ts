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
 *   --apply         Execute the plan under issue #39828: rename entry
 *                   directories to their bounded slug, backfill
 *                   parentSlug/rootSlug into each moved meta.json, remap every
 *                   crossReference / [[slug]] link gallery-wide, and populate
 *                   src/data/proofs/redirects.json with the old→new pairs.
 *                   Run `pnpm build` afterward to regenerate listings + the
 *                   Cloudflare `_redirects` file.
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

// ---------------------------------------------------------------------------
// Migration executor (--apply, issue #39828)
// ---------------------------------------------------------------------------

/**
 * Re-serialize a parsed meta.json while PRESERVING the file's original
 * non-ASCII encoding, so re-writing an entry only diffs the fields we changed.
 *
 * Gallery meta.json files are machine-written and each is internally consistent:
 * either every non-ASCII char is `\uXXXX`-escaped (the file's bytes are pure
 * ASCII) or they are stored raw UTF-8. `JSON.stringify` always emits raw
 * UTF-8, so for an originally-escaped file we re-apply the escaping to match.
 */
function serializeMeta(obj: unknown, originalText: string): string {
  const wasAsciiEscaped = !/[^\x00-\x7f]/.test(originalText)
  let out = JSON.stringify(obj, null, 2)
  if (wasAsciiEscaped) {
    out = out.replace(/[\u0080-\uffff]/g, (c) => '\\u' + c.charCodeAt(0).toString(16).padStart(4, '0'))
  }
  return out + '\n'
}

/** Remap a parent slug through the rename map: migrated → new, else unchanged. */
function remap(slug: string | null, renameMap: Map<string, string>): string | null {
  if (slug === null) return null
  return renameMap.get(slug) ?? slug
}

interface ApplyResult {
  renamed: number
  metasRewritten: number
  referencesUpdated: number
  redirectsWritten: number
}

/**
 * Execute a migration plan against `src/data/proofs`:
 *   1. rename each entry directory `oldSlug` → `newSlug`;
 *   2. rewrite the moved meta.json: `id`/`slug` → new, and backfill
 *      `meta.parentSlug` (remapped through the plan) + `meta.rootSlug`;
 *   3. gallery-wide, remap every crossReference value and `[[slug]]` link that
 *      points at a migrated old slug (pure text replace — no re-serialization,
 *      so untouched files keep their exact bytes);
 *   4. merge the old→new pairs into redirects.json.
 */
function applyPlan(plan: PlanRow[], dataDir: string, redirectsSource: string): ApplyResult {
  const renameMap = new Map<string, string>(plan.map((r) => [r.oldSlug, r.newSlug]))

  // --- 1 & 2: rename dirs + rewrite the moved metas -----------------------
  let renamed = 0
  let metasRewritten = 0
  for (const row of plan) {
    const oldDir = path.join(dataDir, row.oldSlug)
    const newDir = path.join(dataDir, row.newSlug)
    if (!fs.existsSync(oldDir)) {
      throw new Error(`applyPlan: source directory missing: ${oldDir}`)
    }
    if (fs.existsSync(newDir)) {
      throw new Error(`applyPlan: target directory already exists: ${newDir}`)
    }
    fs.renameSync(oldDir, newDir)
    renamed++

    const metaPath = path.join(newDir, 'meta.json')
    const originalText = fs.readFileSync(metaPath, 'utf8')
    const meta = JSON.parse(originalText) as {
      id?: string
      slug?: string
      meta?: Record<string, unknown>
    }
    meta.id = row.newSlug
    meta.slug = row.newSlug
    meta.meta = meta.meta ?? {}
    // parentSlug follows the migration: if the parent was itself re-slugged use
    // its new bounded slug, otherwise keep the (still-live) legacy parent.
    meta.meta.parentSlug = remap(row.parentSlug, renameMap)
    meta.meta.rootSlug = row.rootSlug
    fs.writeFileSync(metaPath, serializeMeta(meta, originalText))
    metasRewritten++
  }

  // --- 3: gallery-wide reference remap (crossReferences + [[slug]] links) ---
  // A quoted exact match (`"<old>"`) only hits JSON string VALUES equal to an
  // old slug — i.e. crossReference proofId/targetId (object or bare-string
  // form) — never a slug embedded in prose. Longest-first alternation keeps a
  // shorter old slug from shadowing a longer one that shares its prefix.
  const olds = plan.map((r) => r.oldSlug).sort((a, b) => b.length - a.length)
  const alt = olds.map(escapeRegExp).join('|')
  const quotedRe = new RegExp(`"(${alt})"`, 'g')
  const linkRe = new RegExp(`\\[\\[(${alt})\\]\\]`, 'g')

  let referencesUpdated = 0
  for (const name of fs.readdirSync(dataDir, { withFileTypes: true })) {
    if (!name.isDirectory()) continue
    const metaPath = path.join(dataDir, name.name, 'meta.json')
    if (!fs.existsSync(metaPath)) continue
    const text = fs.readFileSync(metaPath, 'utf8')
    // Cheap prefilter: only touch files that actually mention a migrated slug.
    if (!text.includes('-oq-')) continue
    const updated = text
      .replace(quotedRe, (_m, s: string) => `"${renameMap.get(s)}"`)
      .replace(linkRe, (_m, s: string) => `[[${renameMap.get(s)}]]`)
    if (updated !== text) {
      fs.writeFileSync(metaPath, updated)
      referencesUpdated++
    }
  }

  // --- 4: populate redirects.json -----------------------------------------
  const redirectsRaw = fs.existsSync(redirectsSource)
    ? (JSON.parse(fs.readFileSync(redirectsSource, 'utf8')) as {
        $comment?: string
        redirects?: Record<string, string>
        [k: string]: unknown
      })
    : { redirects: {} }
  const redirects: Record<string, string> = { ...(redirectsRaw.redirects ?? {}) }
  for (const row of plan) redirects[row.oldSlug] = row.newSlug
  // Sort keys for a stable, churn-free diff.
  const sortedRedirects: Record<string, string> = {}
  for (const k of Object.keys(redirects).sort()) sortedRedirects[k] = redirects[k]
  redirectsRaw.redirects = sortedRedirects
  fs.writeFileSync(redirectsSource, JSON.stringify(redirectsRaw, null, 2) + '\n')

  return {
    renamed,
    metasRewritten,
    referencesUpdated,
    redirectsWritten: plan.length,
  }
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
    if (plan.length === 0) {
      console.log('No entries at or over the depth threshold — nothing to migrate.')
      return
    }
    console.log(
      `Applying migration: ${plan.length} entr${plan.length === 1 ? 'y' : 'ies'} ` +
        `(min OQ depth ${args.minDepth}, ${args.useHash ? 'hash' : 'sequential'} scheme).`
    )
    const result = applyPlan(plan, PROOFS_DATA_DIR, REDIRECTS_SOURCE)
    console.log(
      `\n✅ Migration applied:\n` +
        `   ${result.renamed} directories renamed to bounded slugs\n` +
        `   ${result.metasRewritten} meta.json rewritten (id/slug + parentSlug/rootSlug backfilled)\n` +
        `   ${result.referencesUpdated} other meta.json had crossReferences / [[links]] remapped\n` +
        `   ${result.redirectsWritten} old→new pairs written to redirects.json\n\n` +
        `   Next: run \`pnpm build\` to regenerate listings.json + public/_redirects.\n`
    )
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
