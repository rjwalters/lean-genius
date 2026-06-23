#!/usr/bin/env npx tsx
/**
 * Find proof gallery entries that need peer review
 *
 * Reads all proof directories, joins with review tracker and enrichment tracker,
 * and returns priority-sorted list of proofs needing review.
 *
 * Priority scoring:
 * - Never-reviewed proofs with high enrichment quality (≥80): highest priority
 * - Notable theorems (Wiedijk 100, Hilbert, Millennium) not yet reviewed
 * - Proofs with badge "original" or "verified" (overclaim risk)
 * - Oldest review date (for re-review coverage)
 *
 * Usage:
 *   npx tsx scripts/peer-reviewer/find-targets.ts           # Show top 10 targets
 *   npx tsx scripts/peer-reviewer/find-targets.ts --all     # Show all targets
 *   npx tsx scripts/peer-reviewer/find-targets.ts --json    # Output as JSON
 *   npx tsx scripts/peer-reviewer/find-targets.ts --stats   # Show statistics only
 *   npx tsx scripts/peer-reviewer/find-targets.ts --next    # Show single highest-priority target
 *   npx tsx scripts/peer-reviewer/find-targets.ts --suggest # Show top 10 review candidates (alias for default)
 *   npx tsx scripts/peer-reviewer/find-targets.ts --help    # Show usage
 */

import * as fs from 'fs'
import * as path from 'path'

const GALLERY_DIR = 'src/data/proofs'
const REVIEW_TRACKER_FILE = 'src/data/proofs/review-tracker.json'
const ENRICHMENT_TRACKER_FILE = 'src/data/proofs/enrichment-tracker.json'

function printUsage() {
  console.log(`Usage: npx tsx scripts/peer-reviewer/find-targets.ts [options]

Find proof gallery entries that need peer review.

Options:
  --all      Show all targets instead of the top 10
  --json     Output JSON
  --stats    Show statistics only
  --next     Show the single highest-priority target
  --suggest  Show top 10 review candidates
  --help     Show this help message
  -h         Show this help message`)
}

interface ReviewTrackerEntry {
  reviewCount: number
  lastReviewed: string | null
  overallGrade: string | null
  qualityScore: number | null
  actionItems: number
  resolvedItems: number
}

interface ReviewTracker {
  version: number
  entries: Record<string, ReviewTrackerEntry>
}

interface EnrichmentTrackerEntry {
  passes: number
  lastEnriched: string | null
  quality: number
}

interface EnrichmentTracker {
  version: number
  entries: Record<string, EnrichmentTrackerEntry>
}

interface ReviewTarget {
  id: string
  galleryPath: string
  leanPath: string | null
  reviewCount: number
  lastReviewed: string | null
  enrichmentQuality: number
  enrichmentPasses: number
  priority: number
  meta: {
    title: string
    status: string
    badge: string
    sorries: number
    axiomCount: number
    theoremCount: number
    lineCount: number
    tags: string[]
    hasOriginalContributions: boolean
    mathlibDepCount: number
  }
  flags: string[]
}

function loadReviewTracker(): ReviewTracker {
  if (fs.existsSync(REVIEW_TRACKER_FILE)) {
    try {
      return JSON.parse(fs.readFileSync(REVIEW_TRACKER_FILE, 'utf-8'))
    } catch {
      // Corrupted, start fresh
    }
  }
  return { version: 1, entries: {} }
}

function loadEnrichmentTracker(): EnrichmentTracker {
  if (fs.existsSync(ENRICHMENT_TRACKER_FILE)) {
    try {
      return JSON.parse(fs.readFileSync(ENRICHMENT_TRACKER_FILE, 'utf-8'))
    } catch {
      // Corrupted
    }
  }
  return { version: 1, entries: {} }
}

const NOTABLE_TAGS = new Set([
  'wiedijk-100',
  'hilbert-problems',
  'millennium',
  'clay-problems',
  'fields-medal',
])

function analyzeProof(
  id: string,
  galleryPath: string,
  reviewTracker: ReviewTracker,
  enrichmentTracker: EnrichmentTracker
): ReviewTarget | null {
  const metaPath = path.join(galleryPath, 'meta.json')
  if (!fs.existsSync(metaPath)) return null

  let meta: any
  try {
    meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
  } catch {
    return null
  }

  const proofMeta = meta.meta || {}
  const leanFileRaw = proofMeta.proofRepoPath || ''
  const leanPath = leanFileRaw ? path.join('proofs', leanFileRaw.replace(/^proofs\//, '')) : null

  const tags: string[] = proofMeta.tags || []
  const isNotable = tags.some((t: string) => NOTABLE_TAGS.has(t))
  const hasOriginalContributions = (proofMeta.originalContributions || []).length > 0
  const mathlibDepCount = (proofMeta.mathlibDependencies || []).length

  const leanFile = proofMeta.leanFile || {}
  const theoremCount = (leanFile.theoremCount || 0) + (leanFile.lemmaCount || 0)
  const lineCount = leanFile.lineCount || proofMeta.lineCount || 0

  // Review tracker data
  const reviewEntry = reviewTracker.entries[id]
  const reviewCount = reviewEntry?.reviewCount || 0
  const lastReviewed = reviewEntry?.lastReviewed || null

  // Enrichment tracker data
  const enrichEntry = enrichmentTracker.entries[id]
  const enrichmentQuality = enrichEntry?.quality || 0
  const enrichmentPasses = enrichEntry?.passes || 0

  // Flags for display
  const flags: string[] = []
  if (isNotable) flags.push('notable')
  if (proofMeta.badge === 'original' || proofMeta.badge === 'verified') flags.push('overclaim-risk')
  if (hasOriginalContributions && mathlibDepCount > 0) flags.push('wrapper-check')
  if (enrichmentQuality >= 80) flags.push('enrichment-ready')
  if (proofMeta.status === 'verified' && mathlibDepCount > 2) flags.push('mathlib-heavy')

  const target: ReviewTarget = {
    id,
    galleryPath,
    leanPath,
    reviewCount,
    lastReviewed,
    enrichmentQuality,
    enrichmentPasses,
    priority: 0,
    meta: {
      title: meta.title || id,
      status: proofMeta.status || 'unknown',
      badge: proofMeta.badge || 'unknown',
      sorries: proofMeta.sorries ?? 0,
      axiomCount: proofMeta.axiomCount ?? 0,
      theoremCount,
      lineCount,
      tags,
      hasOriginalContributions,
      mathlibDepCount,
    },
    flags,
  }

  // Priority scoring
  const daysSinceReview = lastReviewed
    ? (Date.now() - new Date(lastReviewed).getTime()) / (1000 * 60 * 60 * 24)
    : 999

  if (reviewCount === 0) {
    // Never reviewed
    let base = 1000

    // Bonus for high enrichment quality (ready for review)
    if (enrichmentQuality >= 80) base += 500

    // Bonus for notable theorems
    if (isNotable) base += 300

    // Bonus for overclaim risk (verified/original badge with Mathlib deps)
    if (flags.includes('overclaim-risk')) base += 200
    if (flags.includes('wrapper-check')) base += 100

    // Bonus for larger proofs (more to review)
    if (lineCount > 100) base += 50

    target.priority = base
  } else {
    // Already reviewed — priority based on staleness
    target.priority = daysSinceReview
  }

  return target
}

function main() {
  const args = process.argv.slice(2)
  if (args.includes('--help') || args.includes('-h')) {
    printUsage()
    return
  }

  const showAll = args.includes('--all')
  const showJson = args.includes('--json')
  const showStats = args.includes('--stats')
  const showNext = args.includes('--next')
  const showSuggest = args.includes('--suggest')

  const reviewTracker = loadReviewTracker()
  const enrichmentTracker = loadEnrichmentTracker()
  const targets: ReviewTarget[] = []

  if (!fs.existsSync(GALLERY_DIR)) {
    console.error(`Gallery directory not found: ${GALLERY_DIR}`)
    process.exit(1)
  }

  for (const entry of fs.readdirSync(GALLERY_DIR)) {
    const galleryPath = path.join(GALLERY_DIR, entry)
    if (!fs.statSync(galleryPath).isDirectory()) continue
    if (entry === 'node_modules') continue

    const target = analyzeProof(entry, galleryPath, reviewTracker, enrichmentTracker)
    if (target) targets.push(target)
  }

  // Sort by priority (highest first)
  targets.sort((a, b) => b.priority - a.priority)

  if (showStats) {
    const total = targets.length
    const reviewed = targets.filter(t => t.reviewCount > 0).length
    const neverReviewed = total - reviewed
    const highQualityUnreviewed = targets.filter(
      t => t.reviewCount === 0 && t.enrichmentQuality >= 80
    ).length
    const notable = targets.filter(t => t.flags.includes('notable')).length
    const overclaim = targets.filter(t => t.flags.includes('overclaim-risk')).length

    if (showJson) {
      console.log(JSON.stringify({
        total, reviewed, neverReviewed, highQualityUnreviewed, notable, overclaim
      }))
    } else {
      console.log('Peer Review Status:')
      console.log(`  Total proofs:              ${total}`)
      console.log(`  Reviewed:                  ${reviewed}`)
      console.log(`  Never reviewed:            ${neverReviewed}`)
      console.log(`  High-quality unreviewed:   ${highQualityUnreviewed}`)
      console.log(`  Notable theorems:          ${notable}`)
      console.log(`  Overclaim risk:            ${overclaim}`)
    }
    return
  }

  if (showNext) {
    if (targets.length === 0) {
      console.log('No targets need review.')
      return
    }
    const t = targets[0]
    if (showJson) {
      console.log(JSON.stringify(t))
    } else {
      console.log(t.id)
    }
    return
  }

  const limit = showAll ? targets.length : 10
  const shown = targets.slice(0, limit)

  if (showJson) {
    console.log(JSON.stringify(shown, null, 2))
    return
  }

  const label = showSuggest ? 'Suggested review candidates' : 'Top review targets'
  console.log(`${label} (${shown.length} of ${targets.length} total):\n`)
  for (const t of shown) {
    const reviewed = t.reviewCount > 0
      ? `(${t.reviewCount}x, last ${t.lastReviewed?.slice(0, 10)})`
      : '(never reviewed)'
    const flagStr = t.flags.length > 0 ? ` [${t.flags.join(', ')}]` : ''
    const quality = t.enrichmentQuality > 0 ? ` q:${t.enrichmentQuality}` : ''
    console.log(`  ${t.id} ${reviewed} ${t.meta.status}/${t.meta.badge}${quality}${flagStr}`)
  }
}

main()
