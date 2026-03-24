#!/usr/bin/env npx tsx
/**
 * Find proof gallery entries that need integrity auditing
 *
 * Reads all proof directories, joins with audit tracker,
 * checks Lean source files for integrity issues, and returns
 * priority-sorted list of proofs needing audit.
 *
 * Checks performed:
 * - True stubs: theorems proving `True` (`:= trivial`, `: True :=`)
 * - Sorry count: compare meta.json sorries vs actual Lean file
 * - Axiom count: compare meta.json axiomCount vs actual Lean file
 * - Status consistency: "verified" requires 0 sorries + 0 True stubs
 * - Badge consistency: Mathlib wrapper detection
 *
 * Priority: never-audited first, then oldest audit, then highest risk
 *
 * Usage:
 *   npx tsx scripts/auditor/find-targets.ts           # Show top 10 targets
 *   npx tsx scripts/auditor/find-targets.ts --all     # Show all targets
 *   npx tsx scripts/auditor/find-targets.ts --json    # Output as JSON
 *   npx tsx scripts/auditor/find-targets.ts --stats   # Show statistics only
 *   npx tsx scripts/auditor/find-targets.ts --next    # Show single highest-priority target
 *   npx tsx scripts/auditor/find-targets.ts --issues   # Show only proofs with detected issues
 */

import * as fs from 'fs'
import * as path from 'path'
import { execSync } from 'child_process'

const GALLERY_DIR = 'src/data/proofs'
const TRACKER_FILE = 'src/data/proofs/audit-tracker.json'
const PROOFS_DIR = 'proofs/Proofs'

interface TrackerEntry {
  auditCount: number
  lastAudited: string | null
  result: 'clean' | 'issues-found' | 'issues-fixed' | null
  issues: string[]
}

interface Tracker {
  version: number
  entries: Record<string, TrackerEntry>
}

interface AuditTarget {
  id: string
  galleryPath: string
  leanPath: string | null
  auditCount: number
  lastAudited: string | null
  priority: number
  detectedIssues: string[]
  meta: {
    status: string
    badge: string
    claimedSorries: number
    claimedAxioms: number
  }
  actual: {
    sorryCount: number
    axiomCount: number
    trueStubCount: number
    hasMajorMathlibDep: boolean
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

/**
 * Strip Lean comments from source code.
 * Handles line comments (--) and nested block comments (/- ... -/).
 */
function stripLeanComments(content: string): string {
  let result = ''
  let i = 0
  let depth = 0

  while (i < content.length) {
    if (depth === 0) {
      if (content[i] === '-' && i + 1 < content.length && content[i + 1] === '-') {
        // Line comment: skip to end of line, preserve newline
        while (i < content.length && content[i] !== '\n') i++
        continue
      }
      if (content[i] === '/' && i + 1 < content.length && content[i + 1] === '-') {
        depth = 1
        i += 2
        continue
      }
      result += content[i]
    } else {
      if (content[i] === '/' && i + 1 < content.length && content[i + 1] === '-') {
        depth++
        i += 2
        continue
      }
      if (content[i] === '-' && i + 1 < content.length && content[i + 1] === '/') {
        depth--
        i += 2
        continue
      }
    }
    i++
  }

  return result
}

// NOTE: Automated Mathlib wrapper detection was removed because regex-based
// heuristics cannot reliably distinguish "using Mathlib lemmas as building blocks"
// (normal, expected in original proofs) from "directly wrapping a Mathlib theorem
// as the main result." The hasMajorMathlibDep field is retained in AuditTarget
// for manual auditor review but is always false for automated scanning.

function countInFile(filePath: string, pattern: RegExp): number {
  if (!fs.existsSync(filePath)) return 0
  const content = fs.readFileSync(filePath, 'utf-8')
  const matches = content.match(pattern)
  return matches ? matches.length : 0
}

function detectIssues(target: AuditTarget): string[] {
  const issues: string[] = []

  // True stub detection
  if (target.actual.trueStubCount > 0 && target.meta.status === 'verified') {
    issues.push(`CRITICAL: ${target.actual.trueStubCount} True stubs but status is "verified"`)
  }

  // Sorry count mismatch
  if (target.meta.claimedSorries !== target.actual.sorryCount) {
    issues.push(`sorry mismatch: claims ${target.meta.claimedSorries}, actual ${target.actual.sorryCount}`)
  }

  // Axiom count mismatch -- only flag when meta undercounts actual declarations.
  // When claimed > actual, the difference may be structure-encoded assumptions (intentional).
  if (target.meta.claimedAxioms >= 0 && target.actual.axiomCount > target.meta.claimedAxioms) {
    issues.push(`axiom undercount: claims ${target.meta.claimedAxioms}, actual declarations ${target.actual.axiomCount}`)
  }

  // Verified with sorries
  if (target.meta.status === 'verified' && target.actual.sorryCount > 0) {
    issues.push(`status "verified" but has ${target.actual.sorryCount} sorries`)
  }

  // Mathlib wrapper with "original" or "verified" badge
  if (target.actual.hasMajorMathlibDep &&
      (target.meta.badge === 'original' || target.meta.badge === 'verified')) {
    issues.push(`badge "${target.meta.badge}" but directly calls major Mathlib theorem`)
  }

  return issues
}

function analyzeProof(id: string, galleryPath: string, tracker: Tracker): AuditTarget | null {
  const metaPath = path.join(galleryPath, 'meta.json')
  if (!fs.existsSync(metaPath)) return null

  let meta: any
  try {
    meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
  } catch {
    return null
  }

  const proofMeta = meta.meta || {}
  const leanFileRaw = proofMeta.leanFile || proofMeta.proofRepoPath || ''
  const leanFile = typeof leanFileRaw === 'string' ? leanFileRaw : ''
  const leanPath = leanFile ? path.join('proofs', leanFile.replace(/^proofs\//, '')) : null

  // Actual counts from Lean file
  let sorryCount = 0
  let axiomCount = 0
  let trueStubCount = 0
  let hasMajorMathlibDep = false

  if (leanPath && fs.existsSync(leanPath)) {
    const rawContent = fs.readFileSync(leanPath, 'utf-8')
    // Strip comments to avoid counting sorry/True in comments (Issue #6130)
    const content = stripLeanComments(rawContent)

    sorryCount = (content.match(/\bsorry\b/g) || []).length
    axiomCount = (content.match(/^axiom /gm) || []).length

    // True stubs: only count theorem/lemma declarations, not example (Issue #6130)
    for (const line of content.split('\n')) {
      const trimmed = line.trim()
      if (/^(theorem|lemma)\b/.test(trimmed) && /(:= trivial\b|: True\b)/.test(trimmed)) {
        trueStubCount++
      }
    }

    // hasMajorMathlibDep left as false -- automated detection removed (unreliable)
  }

  const trackerEntry = tracker.entries[id]
  const auditCount = trackerEntry?.auditCount || 0
  const lastAudited = trackerEntry?.lastAudited || null

  const target: AuditTarget = {
    id,
    galleryPath,
    leanPath,
    auditCount,
    lastAudited,
    priority: 0,
    detectedIssues: [],
    meta: {
      status: proofMeta.status || 'unknown',
      badge: proofMeta.badge || 'unknown',
      claimedSorries: proofMeta.sorries ?? -1,
      claimedAxioms: proofMeta.axiomCount ?? -1,
    },
    actual: {
      sorryCount,
      axiomCount,
      trueStubCount,
      hasMajorMathlibDep,
    },
  }

  target.detectedIssues = detectIssues(target)

  // Priority: issues first, then never-audited, then oldest audit
  const hasIssues = target.detectedIssues.length > 0
  const hasCritical = target.detectedIssues.some(i => i.startsWith('CRITICAL'))
  const daysSinceAudit = lastAudited
    ? (Date.now() - new Date(lastAudited).getTime()) / (1000 * 60 * 60 * 24)
    : 999

  if (hasCritical) target.priority = 10000
  else if (hasIssues) target.priority = 5000 + daysSinceAudit
  else if (auditCount === 0) target.priority = 1000 + daysSinceAudit
  else target.priority = daysSinceAudit

  return target
}

function main() {
  const args = process.argv.slice(2)
  const showAll = args.includes('--all')
  const showJson = args.includes('--json')
  const showStats = args.includes('--stats')
  const showNext = args.includes('--next')
  const showIssues = args.includes('--issues')

  const tracker = loadTracker()
  const targets: AuditTarget[] = []

  // Scan gallery
  if (!fs.existsSync(GALLERY_DIR)) {
    console.error(`Gallery directory not found: ${GALLERY_DIR}`)
    process.exit(1)
  }

  for (const entry of fs.readdirSync(GALLERY_DIR)) {
    const galleryPath = path.join(GALLERY_DIR, entry)
    if (!fs.statSync(galleryPath).isDirectory()) continue
    if (entry === 'node_modules') continue

    const target = analyzeProof(entry, galleryPath, tracker)
    if (target) targets.push(target)
  }

  // Sort by priority (highest first)
  targets.sort((a, b) => b.priority - a.priority)

  // Filter to issues only if requested
  const display = showIssues
    ? targets.filter(t => t.detectedIssues.length > 0)
    : targets

  if (showStats) {
    const total = targets.length
    const audited = targets.filter(t => t.auditCount > 0).length
    const withIssues = targets.filter(t => t.detectedIssues.length > 0).length
    const critical = targets.filter(t => t.detectedIssues.some(i => i.startsWith('CRITICAL'))).length

    if (showJson) {
      console.log(JSON.stringify({ total, audited, unaudited: total - audited, withIssues, critical }))
    } else {
      console.log(`Gallery Audit Status:`)
      console.log(`  Total proofs:     ${total}`)
      console.log(`  Audited:          ${audited}`)
      console.log(`  Unaudited:        ${total - audited}`)
      console.log(`  With issues:      ${withIssues}`)
      console.log(`  Critical issues:  ${critical}`)
    }
    return
  }

  if (showNext) {
    if (display.length === 0) {
      console.log('No targets need auditing.')
      return
    }
    const t = display[0]
    if (showJson) {
      console.log(JSON.stringify(t))
    } else {
      console.log(t.id)
    }
    return
  }

  const limit = showAll ? display.length : 10
  const shown = display.slice(0, limit)

  if (showJson) {
    console.log(JSON.stringify(shown, null, 2))
    return
  }

  console.log(`Top ${shown.length} audit targets (of ${display.length} total):\n`)
  for (const t of shown) {
    const issues = t.detectedIssues.length > 0
      ? ` ❌ ${t.detectedIssues.join('; ')}`
      : ' ✓'
    const audited = t.auditCount > 0
      ? `(${t.auditCount}x, last ${t.lastAudited?.slice(0, 10)})`
      : '(never audited)'
    console.log(`  ${t.id} ${audited} [${t.meta.status}/${t.meta.badge}]${issues}`)
  }
}

main()
