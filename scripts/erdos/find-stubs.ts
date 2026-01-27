#!/usr/bin/env npx tsx
/**
 * Find gallery stubs that need enhancement
 *
 * A "stub" is a gallery entry that has:
 * - Placeholder Lean proof (contains "True := by" or ":= trivial")
 * - Empty or minimal annotations (<10 lines)
 * - Garbage meta.json description (contains scraping artifacts)
 *
 * Usage:
 *   npx tsx scripts/erdos/find-stubs.ts           # Random stub with source (DEFAULT)
 *   npx tsx scripts/erdos/find-stubs.ts --next    # Highest priority stub (deterministic)
 *   npx tsx scripts/erdos/find-stubs.ts --random  # Random stub (any, including no source)
 *   npx tsx scripts/erdos/find-stubs.ts --list    # List all stubs
 *   npx tsx scripts/erdos/find-stubs.ts --stats   # Show statistics only
 *   npx tsx scripts/erdos/find-stubs.ts --json    # Output as JSON
 */

import * as fs from 'fs'
import * as path from 'path'

const GALLERY_DIR = 'src/data/proofs'
const PROOFS_DIR = 'proofs/Proofs'
const FORMAL_CONJECTURES_DIR = 'external/formal-conjectures/FormalConjectures/ErdosProblems'

interface StubInfo {
  erdosNumber: number
  galleryPath: string
  proofPath: string
  hasPlaceholderProof: boolean
  hasEmptyAnnotations: boolean
  hasGarbageDescription: boolean
  hasFormalConjecturesSource: boolean
  formalConjecturesPath?: string
  problemStatus?: string  // proved, disproved, open, solved
  isRework?: boolean      // true if flagged needs-work in completed.json
  stubScore: number       // Higher = more stub-like (worse quality)
  priorityScore: number   // Higher = should fix first
}

interface StubStats {
  totalGalleryEntries: number
  totalStubs: number
  stubsWithSources: number
  stubsWithoutSources: number
  placeholderProofs: number
  emptyAnnotations: number
  garbageDescriptions: number
  qualityEntries: number
  reworkEntries: number
}

function isPlaceholderProof(proofPath: string): boolean {
  if (!fs.existsSync(proofPath)) return true
  const content = fs.readFileSync(proofPath, 'utf-8')
  return content.includes('True := by') ||
         content.includes(':= trivial') ||
         content.includes('theorem erdos_') && content.includes(':= by\n  trivial')
}

function hasEmptyAnnotations(galleryPath: string): boolean {
  const annotationsPath = path.join(galleryPath, 'annotations.json')
  if (!fs.existsSync(annotationsPath)) return true
  const content = fs.readFileSync(annotationsPath, 'utf-8')
  const lines = content.split('\n').filter(l => l.trim()).length
  return lines < 10
}

function hasGarbageDescription(galleryPath: string): boolean {
  const metaPath = path.join(galleryPath, 'meta.json')
  if (!fs.existsSync(metaPath)) return true
  const content = fs.readFileSync(metaPath, 'utf-8')
  // Check for common scraping artifacts
  return content.includes('Forum\\n') ||
         content.includes('Favourites') ||
         content.includes('Random Solved') ||
         content.includes('Random Open') ||
         content.includes('Dual View') ||
         content.includes('"description": "Forum')
}

function getProblemStatus(galleryPath: string): string | undefined {
  const metaPath = path.join(galleryPath, 'meta.json')
  if (!fs.existsSync(metaPath)) return undefined
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
    return meta.meta?.erdosProblemStatus || meta.erdosProblemStatus
  } catch {
    return undefined
  }
}

function hasFormalConjecturesSource(erdosNumber: number): { has: boolean; path?: string } {
  const leanPath = path.join(FORMAL_CONJECTURES_DIR, `${erdosNumber}.lean`)
  if (fs.existsSync(leanPath)) {
    return { has: true, path: leanPath }
  }
  return { has: false }
}

const COMPLETED_FILE = path.join('research/stub-claims', 'completed.json')

interface CompletedEntry {
  status: string
  enhanced_at?: string
  agent?: string
  issues?: string[]
}

function loadCompleted(): Record<string, CompletedEntry> {
  if (!fs.existsSync(COMPLETED_FILE)) return {}
  try {
    const data = JSON.parse(fs.readFileSync(COMPLETED_FILE, 'utf-8'))
    return data.completed || {}
  } catch {
    return {}
  }
}

function calculateStubScore(info: Partial<StubInfo>): number {
  let score = 0
  if (info.hasPlaceholderProof) score += 3
  if (info.hasEmptyAnnotations) score += 2
  if (info.hasGarbageDescription) score += 1
  return score
}

function calculatePriorityScore(info: Partial<StubInfo>): number {
  let score = 100

  // Higher priority for stubs with formal-conjectures sources (easier to fix)
  if (info.hasFormalConjecturesSource) score += 50

  // Higher priority for proved/solved (cleaner narrative)
  if (info.problemStatus === 'proved') score += 30
  else if (info.problemStatus === 'solved') score += 25
  else if (info.problemStatus === 'disproved') score += 20
  // open = +0

  // Higher priority for lower Erdős numbers (more foundational)
  if (info.erdosNumber) {
    score += Math.max(0, 50 - Math.floor(info.erdosNumber / 20))
  }

  // Higher priority for worse stubs (more improvement potential)
  score += (info.stubScore || 0) * 5

  return score
}

function findAllStubs(): StubInfo[] {
  const stubs: StubInfo[] = []
  const completed = loadCompleted()

  // Find all erdos-* directories
  const entries = fs.readdirSync(GALLERY_DIR)
    .filter(e => e.startsWith('erdos-') && !e.includes('-complete') && !e.includes('-factorial'))
    .filter(e => {
      const match = e.match(/^erdos-(\d+)$/)
      return match !== null
    })

  for (const entry of entries) {
    const match = entry.match(/^erdos-(\d+)$/)
    if (!match) continue

    const erdosNumber = parseInt(match[1])
    const erdosKey = erdosNumber.toString()
    const completionEntry = completed[erdosKey]

    // EXCLUSION RULE: Skip entries marked as quality in completed.json (truly done)
    if (completionEntry?.status === 'quality') {
      continue
    }

    const galleryPath = path.join(GALLERY_DIR, entry)
    const proofPath = path.join(PROOFS_DIR, `Erdos${erdosNumber}Problem.lean`)

    const hasPlaceholder = isPlaceholderProof(proofPath)
    const emptyAnnotations = hasEmptyAnnotations(galleryPath)
    const garbageDesc = hasGarbageDescription(galleryPath)

    // INCLUSION RULES:
    // 1. Has file system issues (current logic), OR
    // 2. Marked needs-work in completed.json (quality audit flagged it)
    const hasFileIssues = hasPlaceholder || emptyAnnotations || garbageDesc
    const markedNeedsWork = completionEntry?.status === 'needs-work'

    if (!hasFileIssues && !markedNeedsWork) continue

    const formalSource = hasFormalConjecturesSource(erdosNumber)
    const status = getProblemStatus(galleryPath)

    const stubInfo: StubInfo = {
      erdosNumber,
      galleryPath,
      proofPath,
      hasPlaceholderProof: hasPlaceholder,
      hasEmptyAnnotations: emptyAnnotations,
      hasGarbageDescription: garbageDesc,
      hasFormalConjecturesSource: formalSource.has,
      formalConjecturesPath: formalSource.path,
      problemStatus: status,
      isRework: markedNeedsWork || undefined,
      stubScore: 0,
      priorityScore: 0,
    }

    stubInfo.stubScore = calculateStubScore(stubInfo)
    stubInfo.priorityScore = calculatePriorityScore(stubInfo)

    stubs.push(stubInfo)
  }

  // Sort by priority (highest first)
  return stubs.sort((a, b) => b.priorityScore - a.priorityScore)
}

function computeStats(stubs: StubInfo[]): StubStats {
  const entries = fs.readdirSync(GALLERY_DIR)
    .filter(e => e.startsWith('erdos-') && fs.statSync(path.join(GALLERY_DIR, e)).isDirectory())
    .length

  const completed = loadCompleted()
  const qualityCount = Object.values(completed).filter(e => e.status === 'quality').length
  const reworkCount = stubs.filter(s => s.isRework).length

  return {
    totalGalleryEntries: entries,
    totalStubs: stubs.length,
    stubsWithSources: stubs.filter(s => s.hasFormalConjecturesSource).length,
    stubsWithoutSources: stubs.filter(s => !s.hasFormalConjecturesSource).length,
    placeholderProofs: stubs.filter(s => s.hasPlaceholderProof).length,
    emptyAnnotations: stubs.filter(s => s.hasEmptyAnnotations).length,
    garbageDescriptions: stubs.filter(s => s.hasGarbageDescription).length,
    qualityEntries: qualityCount,
    reworkEntries: reworkCount,
  }
}

function formatStubList(stubs: StubInfo[], limit?: number): void {
  const withSources = stubs.filter(s => s.hasFormalConjecturesSource)
  const withoutSources = stubs.filter(s => !s.hasFormalConjecturesSource)

  console.log('=== Stubs with formal-conjectures sources (PRIORITY) ===\n')
  if (withSources.length === 0) {
    console.log('  (none)\n')
  } else {
    const toShow = limit ? withSources.slice(0, limit) : withSources
    for (const stub of toShow) {
      const issues: string[] = []
      if (stub.hasPlaceholderProof) issues.push('placeholder-proof')
      if (stub.hasEmptyAnnotations) issues.push('empty-annotations')
      if (stub.hasGarbageDescription) issues.push('garbage-desc')

      const statusIcon = stub.problemStatus === 'proved' ? '✓' :
                         stub.problemStatus === 'disproved' ? '✗' :
                         stub.problemStatus === 'solved' ? '✓' : '?'

      const reworkTag = stub.isRework ? ' [REWORK]' : ''
      console.log(`  #${stub.erdosNumber}${reworkTag} [${statusIcon} ${stub.problemStatus || 'unknown'}] - ${issues.join(', ')}`)
      console.log(`    Source: ${stub.formalConjecturesPath}`)
    }
    if (limit && withSources.length > limit) {
      console.log(`  ... and ${withSources.length - limit} more`)
    }
  }

  console.log('\n=== Stubs without sources (need manual Lean) ===\n')
  if (withoutSources.length === 0) {
    console.log('  (none)\n')
  } else {
    const toShow = limit ? withoutSources.slice(0, Math.min(10, limit)) : withoutSources.slice(0, 20)
    for (const stub of toShow) {
      const issues: string[] = []
      if (stub.hasPlaceholderProof) issues.push('placeholder-proof')
      if (stub.hasEmptyAnnotations) issues.push('empty-annotations')
      if (stub.hasGarbageDescription) issues.push('garbage-desc')

      const statusIcon = stub.problemStatus === 'proved' ? '✓' :
                         stub.problemStatus === 'disproved' ? '✗' :
                         stub.problemStatus === 'solved' ? '✓' : '?'

      const reworkTag = stub.isRework ? ' [REWORK]' : ''
      console.log(`  #${stub.erdosNumber}${reworkTag} [${statusIcon} ${stub.problemStatus || 'unknown'}] - ${issues.join(', ')}`)
    }
    if (withoutSources.length > (limit || 20)) {
      console.log(`  ... and ${withoutSources.length - (limit || 20)} more`)
    }
  }
}

function selectRandomStub(stubs: StubInfo[], sourceOnly: boolean = false): StubInfo | null {
  const pool = sourceOnly ? stubs.filter(s => s.hasFormalConjecturesSource) : stubs
  if (pool.length === 0) return null
  const randomIndex = Math.floor(Math.random() * pool.length)
  return pool[randomIndex]
}

function showNextStub(stubs: StubInfo[], stub?: StubInfo | null, isRandom: boolean = false): void {
  if (stubs.length === 0) {
    console.log('No stubs found! All gallery entries are quality.')
    return
  }

  const next = stub || stubs[0]
  if (!next) {
    console.log('No matching stubs found!')
    return
  }

  const header = isRandom ? '=== Random Stub to Enhance ===' : '=== Next Stub to Enhance ==='
  console.log(`${header}\n`)
  console.log(`Erdős Problem #${next.erdosNumber}${next.isRework ? ' [REWORK]' : ''}`)
  console.log(`Status: ${next.problemStatus || 'unknown'}`)
  console.log(`Priority Score: ${next.priorityScore}`)
  console.log(`Stub Score: ${next.stubScore}/6\n`)

  console.log('Issues:')
  if (next.hasPlaceholderProof) console.log('  ✗ Placeholder Lean proof')
  if (next.hasEmptyAnnotations) console.log('  ✗ Empty annotations.json')
  if (next.hasGarbageDescription) console.log('  ✗ Garbage in meta.json description')

  console.log('\nPaths:')
  console.log(`  Gallery: ${next.galleryPath}`)
  console.log(`  Proof:   ${next.proofPath}`)
  if (next.hasFormalConjecturesSource) {
    console.log(`  Source:  ${next.formalConjecturesPath} ✓`)
  }

  console.log('\n=== Enhancement Steps ===\n')

  if (next.hasFormalConjecturesSource) {
    console.log('1. Read the formal-conjectures source:')
    console.log(`   cat ${next.formalConjecturesPath}\n`)
    console.log('2. Rewrite the Lean proof file:')
    console.log(`   - Add proper imports and documentation`)
    console.log(`   - Replace placeholder with real formalization`)
    console.log(`   - Add axioms if needed (with justification)`)
    console.log(`   Edit: ${next.proofPath}\n`)
  } else {
    console.log('1. Research the problem on erdosproblems.com:')
    console.log(`   https://erdosproblems.com/${next.erdosNumber}\n`)
    console.log('2. Write the Lean proof from scratch:')
    console.log(`   Edit: ${next.proofPath}\n`)
  }

  console.log('3. Build and verify:')
  console.log(`   lake build Proofs.Erdos${next.erdosNumber}Problem\n`)

  console.log('4. Rewrite meta.json:')
  console.log(`   - Fix description (remove scraping artifacts)`)
  console.log(`   - Add historicalContext, proofStrategy, keyInsights`)
  console.log(`   Edit: ${next.galleryPath}/meta.json\n`)

  console.log('5. Create annotations.json:')
  console.log(`   - One annotation per definition/theorem`)
  console.log(`   - Minimum 5 annotations, 100+ lines`)
  console.log(`   Edit: ${next.galleryPath}/annotations.json\n`)

  console.log('6. Full build and verify:')
  console.log('   pnpm build\n')
}

function showStats(stats: StubStats): void {
  console.log('=== Erdős Gallery Quality Statistics ===\n')

  const pct = (n: number, total: number) => ((n / total) * 100).toFixed(1)

  console.log(`Total gallery entries:     ${stats.totalGalleryEntries}`)
  console.log(`Quality entries:           ${stats.qualityEntries} (${pct(stats.qualityEntries, stats.totalGalleryEntries)}%)`)
  console.log(`Stubs needing enhancement: ${stats.totalStubs} (${pct(stats.totalStubs, stats.totalGalleryEntries)}%)`)
  if (stats.reworkEntries > 0) {
    console.log(`  Including rework entries: ${stats.reworkEntries} (flagged by quality audit)`)
  }
  console.log('')

  console.log('Stub breakdown:')
  console.log(`  With formal-conjectures: ${stats.stubsWithSources} (easier to fix)`)
  console.log(`  Without sources:         ${stats.stubsWithoutSources} (need manual Lean)\n`)

  console.log('Quality issues:')
  console.log(`  Placeholder proofs:      ${stats.placeholderProofs}`)
  console.log(`  Empty annotations:       ${stats.emptyAnnotations}`)
  console.log(`  Garbage descriptions:    ${stats.garbageDescriptions}\n`)
}

// Main
const args = process.argv.slice(2)

const stubs = findAllStubs()
const stats = computeStats(stubs)

if (args.includes('--help') || args.includes('-h')) {
  console.log(`
Erdős Gallery Stub Finder

Find gallery entries that need enhancement (stubs).

Usage:
  npx tsx scripts/erdos/find-stubs.ts           Random stub with source (DEFAULT, best for parallel agents)
  npx tsx scripts/erdos/find-stubs.ts --next    Highest priority stub (deterministic, for single agent)
  npx tsx scripts/erdos/find-stubs.ts --random  Random stub from ALL stubs (including those without sources)
  npx tsx scripts/erdos/find-stubs.ts --list    List all stubs (prioritized)
  npx tsx scripts/erdos/find-stubs.ts --stats   Show statistics only
  npx tsx scripts/erdos/find-stubs.ts --json    Output as JSON

A stub has one or more of:
  - Placeholder Lean proof (True := trivial)
  - Empty annotations.json (<10 lines)
  - Garbage meta.json description (scraping artifacts)
  - Marked needs-work in completed.json (quality audit flagged)

Default Behavior:
  Running without flags selects a RANDOM stub that has a formal-conjectures
  source. This is optimal for parallel agents to avoid collisions.

Priority order (for --next):
  1. Has formal-conjectures source (easier to fix)
  2. Status: proved > solved > disproved > open
  3. Lower Erdős number (more foundational)
`)
  process.exit(0)
}

if (args.includes('--json')) {
  console.log(JSON.stringify({ stats, stubs }, null, 2))
} else if (args.includes('--stats')) {
  showStats(stats)
} else if (args.includes('--list')) {
  // Explicit list mode (old default behavior)
  showStats(stats)
  formatStubList(stubs, 30)
  console.log('\nOther commands:')
  console.log('  npx tsx scripts/erdos/find-stubs.ts           # Random stub with source (default)')
  console.log('  npx tsx scripts/erdos/find-stubs.ts --next    # Highest priority stub')
  console.log('  npx tsx scripts/erdos/find-stubs.ts --random  # Random stub (any)')
} else if (args.includes('--next')) {
  showStats(stats)
  showNextStub(stubs)
} else if (args.includes('--random')) {
  showStats(stats)
  const randomStub = selectRandomStub(stubs, false)
  showNextStub(stubs, randomStub, true)
} else {
  // Default: random stub with source (best for parallel agents)
  showStats(stats)
  const randomStub = selectRandomStub(stubs, true)
  showNextStub(stubs, randomStub, true)
}
