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
    hasAssumptions: boolean
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

function commonPrefixLength(a: string, b: string): number {
  let i = 0
  while (i < a.length && i < b.length && a[i] === b[i]) i++
  return i
}

/**
 * Build a set of all Lean file paths that are the primary proof file for a
 * gallery entry. Used to distinguish "sibling files from the same proof family"
 * (helpers, Aristotle companions) from "sibling gallery entries" (separate proofs
 * that happen to share a name prefix, e.g. Erdos2Problem ↔ Erdos2OQ01).
 */
function buildGalleryOwnedPaths(galleryDir: string): Set<string> {
  const owned = new Set<string>()
  if (!fs.existsSync(galleryDir)) return owned
  for (const entry of fs.readdirSync(galleryDir)) {
    const galleryPath = path.join(galleryDir, entry)
    if (!fs.statSync(galleryPath).isDirectory()) continue
    const metaPath = path.join(galleryPath, 'meta.json')
    if (!fs.existsSync(metaPath)) continue
    try {
      const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
      const proofMeta = meta.meta || {}
      const leanFileRaw = proofMeta.proofRepoPath || (typeof proofMeta.leanFile === 'string' ? proofMeta.leanFile : '')
      const leanFile = typeof leanFileRaw === 'string' ? leanFileRaw : ''
      if (leanFile) {
        owned.add(path.join('proofs', leanFile.replace(/^proofs\//, '')))
      }
    } catch {
      // skip malformed meta
    }
  }
  return owned
}

/**
 * Resolve all Lean source files for a proof, including:
 * - The main proofRepoPath file
 * - Any files listed in meta.additionalFiles
 * - Any submodule imports (import Proofs.X.Y → proofs/Proofs/X/Y.lean)
 * - Sibling imports (import Proofs.X → proofs/Proofs/X.lean) when X shares
 *   a name prefix with the main file (covers inherited-axiom cases)
 *
 * Returns two sets:
 * - forSorries: main file + additionalFiles + non-gallery sibling imports
 *   (gallery-owned sibling files are excluded to avoid sorry inflation:
 *    parent/sibling gallery entries are audited independently and their
 *    sorries must not be double-counted here)
 * - forAxioms: everything in forSorries + gallery-owned sibling imports
 *   (needed to count axioms that are declared in parent proof files and
 *    inherited/re-exported by the current proof)
 */
function resolveAllLeanFiles(
  mainLeanPath: string,
  proofMeta: any,
  galleryOwnedPaths: Set<string>
): { forSorries: string[]; forAxioms: string[] } {
  const baseFiles: string[] = []
  const galleryFiles: string[] = []     // gallery-owned siblings (axioms only)
  const nonGalleryFiles: string[] = []  // non-gallery siblings (sorries + axioms)

  if (mainLeanPath && fs.existsSync(mainLeanPath)) {
    baseFiles.push(mainLeanPath)
  }

  // Check additionalFiles from meta (always included in both lists)
  const additionalFiles: unknown[] = proofMeta.additionalFiles || []
  for (const af of additionalFiles) {
    if (typeof af !== 'string') continue
    const afPath = path.join('proofs', af.replace(/^proofs\//, ''))
    if (fs.existsSync(afPath) && !baseFiles.includes(afPath)) {
      baseFiles.push(afPath)
    }
  }

  const allSoFar = () => [...baseFiles, ...galleryFiles, ...nonGalleryFiles]

  // Detect submodule and sibling imports from main file
  // Follow imports into subdirectories that are either:
  //   1. A prefix of the main file name (e.g., "YangMills" prefix of "YangMillsProblem")
  //   2. The same directory as the main file (e.g., main at YangMills/Exploration.lean → follow Proofs.YangMills.*)
  // Also follow single-level imports (import Proofs.X) when X shares a name
  //   prefix of >= 4 chars with the main file (e.g., Erdos2Problem ↔ Erdos2OQ01).
  // This avoids counting sorries in unrelated shared libraries (e.g., GraphCore).
  //
  // Gallery-owned siblings are placed in galleryFiles (axiom-only tracking):
  //   - Excluded from forSorries to prevent sorry inflation from parent gallery entries
  //   - Included in forAxioms to capture axioms inherited from parent proof files
  if (mainLeanPath && fs.existsSync(mainLeanPath)) {
    const mainBaseName = path.basename(mainLeanPath, '.lean')
    const mainParentDir = path.basename(path.dirname(mainLeanPath))
    const content = fs.readFileSync(mainLeanPath, 'utf-8')
    const importRegex = /^import (Proofs\.\S+)/gm
    let match
    while ((match = importRegex.exec(content)) !== null) {
      const moduleParts = match[1].split('.')
      const subDirName = moduleParts[1]

      if (moduleParts.length === 2) {
        // Single-level import: import Proofs.X → proofs/Proofs/X.lean
        // Follow only when X shares a meaningful name prefix with the main file
        // (indicating they belong to the same proof family).
        // Threshold: prefix must be >= 40% of the shorter name (min 4 chars).
        // This allows Erdos2OQ01 ↔ Erdos2Problem ("Erdos2", 60% of 10)
        // while blocking Erdos28AdditiveBases ↔ Erdos340GreedySidon ("Erdos", 26% of 19).
        const minLen = Math.min(mainBaseName.length, subDirName.length)
        const threshold = Math.max(4, Math.floor(minLen * 0.4))
        if (commonPrefixLength(mainBaseName, subDirName) < threshold) continue
        const subPath = path.join('proofs', 'Proofs', subDirName + '.lean')
        if (!fs.existsSync(subPath) || allSoFar().includes(subPath)) continue
        if (galleryOwnedPaths.has(subPath)) {
          galleryFiles.push(subPath)
        } else {
          nonGalleryFiles.push(subPath)
        }
        continue
      }

      // Multi-level import: import Proofs.X.Y → proofs/Proofs/X/Y.lean
      if (moduleParts.length < 3) continue
      // Follow if X is a prefix of the main file name, OR if the main file lives in directory X
      if (!mainBaseName.startsWith(subDirName) && mainParentDir !== subDirName) continue

      const modulePath = moduleParts.join('/')
      const subPath = path.join('proofs', modulePath + '.lean')
      if (!fs.existsSync(subPath) || allSoFar().includes(subPath)) continue
      if (galleryOwnedPaths.has(subPath)) {
        galleryFiles.push(subPath)
      } else {
        nonGalleryFiles.push(subPath)
      }
    }
  }

  return {
    forSorries: [...baseFiles, ...nonGalleryFiles],
    forAxioms: [...baseFiles, ...nonGalleryFiles, ...galleryFiles],
  }
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

  // Axiom count mismatch -- check both directions.
  // Note: structure-encoded assumptions (e.g. NSAxioms structure fields) and axioms
  // in companion files (e.g. PiTranscendental.lean) should still be counted in
  // meta.axiomCount per policy, but the tool can only detect `axiom` declarations.
  // When actualAxiomCount == 0 but claimedAxioms > 0, the proof may be using
  // structure-encoded assumptions documented in the `assumptions` field — suppress
  // the false positive only when status is "axiomatized" and assumptions are documented.
  if (target.meta.claimedAxioms >= 0 && target.actual.axiomCount !== target.meta.claimedAxioms) {
    if (target.actual.axiomCount > target.meta.claimedAxioms) {
      issues.push(`axiom undercount: claims ${target.meta.claimedAxioms}, actual declarations ${target.actual.axiomCount}`)
    } else {
      // Overcount: claimed > actual
      // Suppress if actualAxiomCount == 0, proof is axiomatized, and assumptions are documented.
      // These are structure-encoded or companion-file axioms that can't be auto-detected.
      const isStructureEncoded =
        target.actual.axiomCount === 0 &&
        target.meta.status === 'axiomatized' &&
        target.meta.hasAssumptions
      if (!isStructureEncoded) {
        issues.push(`axiom overcount: claims ${target.meta.claimedAxioms}, actual declarations ${target.actual.axiomCount}`)
      }
    }
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

function analyzeProof(
  id: string,
  galleryPath: string,
  tracker: Tracker,
  galleryOwnedPaths: Set<string>
): AuditTarget | null {
  const metaPath = path.join(galleryPath, 'meta.json')
  if (!fs.existsSync(metaPath)) return null

  let meta: any
  try {
    meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
  } catch {
    return null
  }

  const proofMeta = meta.meta || {}
  // proofRepoPath is always a string path; leanFile may be an object (metadata)
  const leanFileRaw = proofMeta.proofRepoPath || (typeof proofMeta.leanFile === 'string' ? proofMeta.leanFile : '')
  const leanFile = typeof leanFileRaw === 'string' ? leanFileRaw : ''
  const leanPath = leanFile ? path.join('proofs', leanFile.replace(/^proofs\//, '')) : null

  // Actual counts from Lean file(s) — includes submodules and additionalFiles
  let sorryCount = 0
  let axiomCount = 0
  let trueStubCount = 0
  let hasMajorMathlibDep = false

  const { forSorries, forAxioms } = leanPath
    ? resolveAllLeanFiles(leanPath, proofMeta, galleryOwnedPaths)
    : { forSorries: [], forAxioms: [] }

  // Count sorries and True stubs from non-gallery-owned files only
  // (gallery-owned siblings are audited as their own entries)
  for (const filePath of forSorries) {
    const rawContent = fs.readFileSync(filePath, 'utf-8')
    // Strip comments to avoid counting sorry/True in comments (Issue #6130)
    const content = stripLeanComments(rawContent)

    sorryCount += (content.match(/\bsorry\b/g) || []).length

    // True stubs: only count theorem/lemma declarations, not example (Issue #6130)
    for (const line of content.split('\n')) {
      const trimmed = line.trim()
      if (/^(theorem|lemma)\b/.test(trimmed) && /(:= trivial\b|: True\b)/.test(trimmed)) {
        trueStubCount++
      }
    }
  }

  // Count axioms from all files including gallery-owned siblings
  // (parent proof files may declare axioms that are inherited by this entry)
  // Fix: include `noncomputable axiom` in addition to plain `axiom` declarations
  for (const filePath of forAxioms) {
    const rawContent = fs.readFileSync(filePath, 'utf-8')
    const content = stripLeanComments(rawContent)
    axiomCount += (content.match(/^(?:noncomputable\s+)?(?:private\s+)?axiom /gm) || []).length
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
      hasAssumptions: typeof proofMeta.assumptions === 'string' && proofMeta.assumptions.trim().length > 0,
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

  // Pre-build gallery-owned paths for sorry/axiom scope isolation
  const galleryOwnedPaths = buildGalleryOwnedPaths(GALLERY_DIR)

  for (const entry of fs.readdirSync(GALLERY_DIR)) {
    const galleryPath = path.join(GALLERY_DIR, entry)
    if (!fs.statSync(galleryPath).isDirectory()) continue
    if (entry === 'node_modules') continue

    const target = analyzeProof(entry, galleryPath, tracker, galleryOwnedPaths)
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
