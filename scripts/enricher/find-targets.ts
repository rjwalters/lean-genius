#!/usr/bin/env npx tsx
/**
 * Find proof gallery entries that need enrichment
 *
 * Reads all proof directories, joins with enrichment tracker,
 * computes quality score, and returns priority-sorted list.
 *
 * Quality score heuristic:
 * - Annotation count (0-25 points)
 * - Presence of mathContext in annotations (0-10 points)
 * - Presence of significance in annotations (0-10 points)
 * - overview.historicalContext length (0-10 points)
 * - overview.keyInsights count (0-10 points)
 * - conclusion presence and depth (0-15 points)
 * - sections count (0-10 points)
 * - cross-references / relatedConcepts (0-10 points)
 *
 * Priority: (1 / (passes + 1)) * (100 - quality)
 *
 * Usage:
 *   npx tsx scripts/enricher/find-targets.ts           # Show top 10 targets
 *   npx tsx scripts/enricher/find-targets.ts --all     # Show all targets
 *   npx tsx scripts/enricher/find-targets.ts --json    # Output as JSON
 *   npx tsx scripts/enricher/find-targets.ts --stats   # Show statistics only
 *   npx tsx scripts/enricher/find-targets.ts --next    # Show single highest-priority target
 */

import * as fs from 'fs'
import * as path from 'path'

const GALLERY_DIR = 'src/data/proofs'
const TRACKER_FILE = 'src/data/proofs/enrichment-tracker.json'

interface TrackerEntry {
  passes: number
  lastEnriched: string | null
  quality: number
}

interface Tracker {
  version: number
  entries: Record<string, TrackerEntry>
}

interface TargetInfo {
  id: string
  galleryPath: string
  quality: number
  passes: number
  lastEnriched: string | null
  priority: number
  qualityBreakdown: {
    annotations: number
    mathContext: number
    significance: number
    historicalContext: number
    keyInsights: number
    conclusion: number
    sections: number
    crossRefs: number
  }
}

function loadTracker(): Tracker {
  if (fs.existsSync(TRACKER_FILE)) {
    try {
      return JSON.parse(fs.readFileSync(TRACKER_FILE, 'utf-8'))
    } catch {
      // Corrupted file, start fresh
    }
  }
  return { version: 1, entries: {} }
}

function computeQuality(galleryPath: string): { score: number; breakdown: TargetInfo['qualityBreakdown'] } {
  const breakdown = {
    annotations: 0,
    mathContext: 0,
    significance: 0,
    historicalContext: 0,
    keyInsights: 0,
    conclusion: 0,
    sections: 0,
    crossRefs: 0,
  }

  // Read meta.json
  const metaPath = path.join(galleryPath, 'meta.json')
  let meta: any = null
  if (fs.existsSync(metaPath)) {
    try {
      meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
    } catch { /* skip */ }
  }

  // Read annotations.json
  const annotationsPath = path.join(galleryPath, 'annotations.json')
  let annotations: any[] = []
  if (fs.existsSync(annotationsPath)) {
    try {
      const parsed = JSON.parse(fs.readFileSync(annotationsPath, 'utf-8'))
      annotations = Array.isArray(parsed) ? parsed : []
    } catch { /* skip */ }
  }

  // Annotation count (0-25 points, 5 per annotation up to 5)
  breakdown.annotations = Math.min(25, annotations.length * 5)

  // mathContext presence in annotations (0-10 points)
  const withMathContext = annotations.filter((a: any) => a.mathContext && a.mathContext.length > 0)
  breakdown.mathContext = Math.min(10, withMathContext.length * 3)

  // significance presence in annotations (0-10 points)
  const withSignificance = annotations.filter((a: any) => a.significance && a.significance.length > 0)
  breakdown.significance = Math.min(10, withSignificance.length * 3)

  if (meta) {
    // historicalContext length (0-10 points)
    const hc = meta.overview?.historicalContext || ''
    if (hc.length > 500) breakdown.historicalContext = 10
    else if (hc.length > 200) breakdown.historicalContext = 7
    else if (hc.length > 50) breakdown.historicalContext = 4
    else if (hc.length > 0) breakdown.historicalContext = 2

    // keyInsights count (0-10 points, 2 per insight up to 5)
    const insights = meta.overview?.keyInsights || []
    breakdown.keyInsights = Math.min(10, insights.length * 2)

    // conclusion presence and depth (0-15 points)
    const conclusion = meta.conclusion
    if (conclusion) {
      if (conclusion.summary) breakdown.conclusion += 5
      if (conclusion.implications) breakdown.conclusion += 5
      if (conclusion.openQuestions && conclusion.openQuestions.length > 0) breakdown.conclusion += 5
    }

    // sections count (0-10 points, 2 per section up to 5)
    const sections = meta.sections || []
    breakdown.sections = Math.min(10, sections.length * 2)
  }

  // Cross-references / relatedConcepts (0-10 points)
  const withRelated = annotations.filter((a: any) => a.relatedConcepts && a.relatedConcepts.length > 0)
  breakdown.crossRefs = Math.min(10, withRelated.length * 3)

  const score = Object.values(breakdown).reduce((sum, v) => sum + v, 0)
  return { score: Math.min(100, score), breakdown }
}

function findTargets(): TargetInfo[] {
  const tracker = loadTracker()
  const targets: TargetInfo[] = []

  if (!fs.existsSync(GALLERY_DIR)) {
    console.error(`Gallery directory not found: ${GALLERY_DIR}`)
    process.exit(1)
  }

  const entries = fs.readdirSync(GALLERY_DIR, { withFileTypes: true })
    .filter(d => d.isDirectory())
    .map(d => d.name)

  for (const id of entries) {
    const galleryPath = path.join(GALLERY_DIR, id)
    const metaPath = path.join(galleryPath, 'meta.json')

    // Must have meta.json to be a valid entry
    if (!fs.existsSync(metaPath)) continue

    const { score, breakdown } = computeQuality(galleryPath)
    const trackerEntry = tracker.entries[id]
    const passes = trackerEntry?.passes ?? 0
    const lastEnriched = trackerEntry?.lastEnriched ?? null

    // Priority: (1 / (passes + 1)) * (100 - quality)
    const priority = (1 / (passes + 1)) * (100 - score)

    targets.push({
      id,
      galleryPath,
      quality: score,
      passes,
      lastEnriched,
      priority,
      qualityBreakdown: breakdown,
    })
  }

  // Sort by priority descending (highest priority first)
  targets.sort((a, b) => b.priority - a.priority)

  return targets
}

function getStats(targets: TargetInfo[]) {
  const total = targets.length
  const avgQuality = targets.reduce((sum, t) => sum + t.quality, 0) / total
  const passDistribution: Record<number, number> = {}
  for (const t of targets) {
    passDistribution[t.passes] = (passDistribution[t.passes] || 0) + 1
  }

  const qualityBuckets = {
    '0-20 (needs work)': targets.filter(t => t.quality <= 20).length,
    '21-40 (basic)': targets.filter(t => t.quality > 20 && t.quality <= 40).length,
    '41-60 (decent)': targets.filter(t => t.quality > 40 && t.quality <= 60).length,
    '61-80 (good)': targets.filter(t => t.quality > 60 && t.quality <= 80).length,
    '81-100 (excellent)': targets.filter(t => t.quality > 80).length,
  }

  return {
    total,
    averageQuality: avgQuality,
    qualityBuckets,
    passDistribution,
    needsEnrichment: targets.filter(t => t.quality < 80).length,
  }
}

function printStats(targets: TargetInfo[]): void {
  const stats = getStats(targets)

  console.log(`Enrichment Target Statistics`)
  console.log(`============================`)
  console.log(`Total gallery entries: ${stats.total}`)
  console.log(`Average quality score: ${stats.averageQuality.toFixed(1)}`)
  console.log(``)
  console.log(`Quality distribution:`)
  for (const [bucket, count] of Object.entries(stats.qualityBuckets)) {
    const bar = '#'.repeat(Math.ceil(count / 20))
    console.log(`  ${bucket.padEnd(24)} ${String(count).padStart(5)} ${bar}`)
  }
  console.log(``)
  console.log(`Pass distribution:`)
  for (const [passes, count] of Object.entries(stats.passDistribution).sort(([a], [b]) => Number(a) - Number(b))) {
    console.log(`  ${passes} passes: ${count} entries`)
  }
  console.log(``)
  console.log(`Entries needing enrichment: ${stats.needsEnrichment}`)
}

// Main
const args = process.argv.slice(2)
const targets = findTargets()

if (args.includes('--stats')) {
  if (args.includes('--json')) {
    console.log(JSON.stringify(getStats(targets), null, 2))
  } else {
    printStats(targets)
  }
} else if (args.includes('--json')) {
  console.log(JSON.stringify(targets, null, 2))
} else if (args.includes('--next')) {
  if (targets.length > 0) {
    const t = targets[0]
    console.log(`${t.id} (quality: ${t.quality}, passes: ${t.passes}, priority: ${t.priority.toFixed(1)})`)
  } else {
    console.log('No targets found')
  }
} else {
  const count = args.includes('--all') ? targets.length : 10
  const shown = targets.slice(0, count)

  console.log(`Top ${shown.length} enrichment targets (of ${targets.length}):`)
  console.log(`${'ID'.padEnd(40)} ${'Quality'.padStart(7)} ${'Passes'.padStart(6)} ${'Priority'.padStart(8)}`)
  console.log(`${'─'.repeat(40)} ${'─'.repeat(7)} ${'─'.repeat(6)} ${'─'.repeat(8)}`)
  for (const t of shown) {
    console.log(`${t.id.padEnd(40)} ${String(t.quality).padStart(7)} ${String(t.passes).padStart(6)} ${t.priority.toFixed(1).padStart(8)}`)
  }
}
