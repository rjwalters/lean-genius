#!/usr/bin/env npx tsx
/**
 * Gallery meta.json size guardrail.
 *
 * Autonomous enrichment (see .lean/roles/enricher.md) historically only ever
 * "deepened" fields with lower bounds and no upper bound, so the most-visited
 * entries bloated without limit (abel-ruffini grew to ~646 KB vs a ~13 KB gallery
 * median). This check flags any src/data/proofs/<id>/meta.json that exceeds the
 * per-file cap so regressions are caught early. Root cause + guardrails: #30347.
 * Cleanup of the already-bloated entries is tracked separately in #30348.
 *
 * Defaults to WARN mode (prints offenders, exits 0) so it can run inside the
 * build without breaking on the entries that are still pending #30348 cleanup.
 *
 * Run:
 *   npx tsx scripts/gallery/check-meta-size.ts            # warn: list over-cap entries
 *   npx tsx scripts/gallery/check-meta-size.ts <id>       # check a single entry
 *   npx tsx scripts/gallery/check-meta-size.ts --strict   # fail (exit 1) on non-allowlisted offenders
 *   npx tsx scripts/gallery/check-meta-size.ts --report   # one-shot report of all entries over the report threshold (feeds #30348)
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)
const ROOT = path.join(__dirname, '../..')
const PROOFS_DIR = path.join(ROOT, 'src/data/proofs')

// Per-file cap: ~3x the gallery p99 (~34 KB). See #30347.
const FILE_CAP_BYTES = 60 * 1024
// Lower threshold used only for the one-shot --report (feeds cleanup issue #30348).
const REPORT_THRESHOLD_BYTES = 30 * 1024

// Per-collection caps (mirrors .lean/roles/enricher.md). Informational in warn
// mode; counted toward failures in --strict mode.
const COLLECTION_CAPS: Record<string, number> = {
  'overview.keyInsights': 12,
  crossReferences: 20,
  references: 25,
  relatedProblems: 15,
  'conclusion.openQuestions': 15,
}

// Known-bloated entries that predate the guardrails. They are exempt from
// --strict failure until #30348 redistributes their content. Do NOT add new
// entries here — fix the bloat instead.
const ALLOWLIST = new Set<string>([
  'abel-ruffini',
  'abel-ruffini-galois-extensions',
])

const STRICT = process.argv.includes('--strict')
const REPORT = process.argv.includes('--report')
const SINGLE_ID = process.argv.slice(2).find((a) => !a.startsWith('--'))

function kb(bytes: number): string {
  return `${(bytes / 1024).toFixed(1)} KB`
}

function getNested(obj: unknown, dottedKey: string): unknown {
  return dottedKey.split('.').reduce<unknown>((acc, key) => {
    if (acc && typeof acc === 'object' && key in (acc as Record<string, unknown>)) {
      return (acc as Record<string, unknown>)[key]
    }
    return undefined
  }, obj)
}

interface Offender {
  id: string
  bytes: number
  overCollections: string[]
}

function listEntryIds(): string[] {
  if (SINGLE_ID) return [SINGLE_ID]
  if (!fs.existsSync(PROOFS_DIR)) return []
  return fs
    .readdirSync(PROOFS_DIR, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name)
    .sort()
}

function inspectEntry(id: string): { bytes: number; overCollections: string[] } | null {
  const metaPath = path.join(PROOFS_DIR, id, 'meta.json')
  if (!fs.existsSync(metaPath)) return null
  const bytes = fs.statSync(metaPath).size

  const overCollections: string[] = []
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, 'utf8'))
    for (const [key, cap] of Object.entries(COLLECTION_CAPS)) {
      const value = getNested(meta, key)
      if (Array.isArray(value) && value.length > cap) {
        overCollections.push(`${key}=${value.length} (cap ${cap})`)
      }
    }
  } catch {
    // Malformed JSON is caught by other build steps; size still reported.
  }

  return { bytes, overCollections }
}

function main(): void {
  const ids = listEntryIds()
  if (ids.length === 0) {
    console.error(`No gallery entries found under ${path.relative(ROOT, PROOFS_DIR)}`)
    process.exit(SINGLE_ID ? 1 : 0)
  }

  const offenders: Offender[] = []
  const reportRows: Offender[] = []

  for (const id of ids) {
    const result = inspectEntry(id)
    if (!result) {
      if (SINGLE_ID) {
        console.error(`Entry "${id}" has no meta.json`)
        process.exit(1)
      }
      continue
    }
    const row: Offender = { id, bytes: result.bytes, overCollections: result.overCollections }
    if (result.bytes > FILE_CAP_BYTES || result.overCollections.length > 0) {
      offenders.push(row)
    }
    if (result.bytes > REPORT_THRESHOLD_BYTES) {
      reportRows.push(row)
    }
  }

  if (REPORT) {
    reportRows.sort((a, b) => b.bytes - a.bytes)
    console.log(`# Gallery meta.json over ${kb(REPORT_THRESHOLD_BYTES)} (feeds #30348)`)
    console.log(`# ${reportRows.length} entries, cap is ${kb(FILE_CAP_BYTES)}\n`)
    for (const row of reportRows) {
      const flag = row.bytes > FILE_CAP_BYTES ? 'OVER-CAP' : 'over-report'
      console.log(`${kb(row.bytes).padStart(10)}  ${flag.padEnd(11)}  ${row.id}`)
    }
    return
  }

  const overCap = offenders.filter((o) => o.bytes > FILE_CAP_BYTES)
  const nonAllowlistedOverCap = overCap.filter((o) => !ALLOWLIST.has(o.id))

  if (offenders.length === 0) {
    console.log(`meta.json size check: all ${ids.length} entries within caps (file ≤ ${kb(FILE_CAP_BYTES)}).`)
    return
  }

  console.log(`meta.json size check: ${overCap.length} entr${overCap.length === 1 ? 'y' : 'ies'} over the ${kb(FILE_CAP_BYTES)} file cap:`)
  overCap
    .sort((a, b) => b.bytes - a.bytes)
    .forEach((o) => {
      const tag = ALLOWLIST.has(o.id) ? ' [allowlisted — see #30348]' : ''
      console.log(`  ${kb(o.bytes).padStart(10)}  ${o.id}${tag}`)
    })

  const collectionOffenders = offenders.filter((o) => o.overCollections.length > 0)
  if (collectionOffenders.length > 0) {
    console.log(`\nEntries over a per-collection cap:`)
    collectionOffenders.forEach((o) => {
      console.log(`  ${o.id}: ${o.overCollections.join(', ')}`)
    })
  }

  console.log(
    `\nGuardrails: .lean/roles/enricher.md (per-file ≤ ${kb(FILE_CAP_BYTES)}). ` +
      `Cleanup of pre-existing bloat: #30348.`,
  )

  if (STRICT && nonAllowlistedOverCap.length > 0) {
    console.error(
      `\nFAIL (--strict): ${nonAllowlistedOverCap.length} non-allowlisted entr${nonAllowlistedOverCap.length === 1 ? 'y' : 'ies'} over the file cap.`,
    )
    process.exit(1)
  }
}

main()
