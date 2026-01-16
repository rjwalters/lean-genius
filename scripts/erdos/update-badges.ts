#!/usr/bin/env npx tsx
/**
 * Update badges in meta.json based on actual Lean file analysis
 *
 * Scans all proof directories and updates badges based on:
 * - sorry count in the Lean file
 * - axiom usage
 *
 * Valid badges:
 * - 'wip' - Has sorries (work in progress)
 * - 'axiom' - Uses axioms, no sorries
 * - 'mathlib' - Complete proof using Mathlib
 * - 'original' - Novel proof with minimal delegation
 * - 'ai-solved' - Problem solved by AI
 * - 'from-axioms' - Proves from first principles
 * - 'pedagogical' - Teaching example
 * - 'fallacy' - Demonstrates a fallacy
 */

import * as fs from 'fs'
import * as path from 'path'

const PROOFS_DIR = 'src/data/proofs'
const LEAN_DIR = 'proofs/Proofs'

type ValidBadge = 'original' | 'mathlib' | 'pedagogical' | 'from-axioms' | 'fallacy' | 'wip' | 'ai-solved' | 'axiom'

interface UpdateResult {
  id: string
  oldBadge: string
  newBadge: ValidBadge
  sorries: number
  hasAxiom: boolean
  reason: string
}

/**
 * Count sorries in a Lean file
 */
function countSorries(content: string): number {
  // Match 'sorry' as a standalone tactic/term, not in comments
  const lines = content.split('\n')
  let count = 0
  let inBlockComment = false

  for (const line of lines) {
    // Track block comments
    if (line.includes('/-')) inBlockComment = true
    if (line.includes('-/')) {
      inBlockComment = false
      continue
    }
    if (inBlockComment) continue

    // Skip line comments
    const withoutLineComment = line.split('--')[0]

    // Count sorry occurrences (word boundary match)
    const matches = withoutLineComment.match(/\bsorry\b/g)
    if (matches) {
      count += matches.length
    }
  }

  return count
}

/**
 * Check if Lean file uses axioms
 */
function hasAxiom(content: string): boolean {
  // Check for axiom declarations
  return /\baxiom\s+\w+/.test(content) || /\bpostulate\s+\w+/.test(content)
}

/**
 * Determine the appropriate badge based on file analysis
 */
function determineBadge(
  content: string,
  currentBadge: string,
  sorryCount: number
): { badge: ValidBadge; reason: string; hasAxiom: boolean } {
  const usesAxiom = hasAxiom(content)

  // Preserve certain manual badges
  if (currentBadge === 'ai-solved') {
    return { badge: 'ai-solved', reason: 'Preserved (AI-solved)', hasAxiom: usesAxiom }
  }
  if (currentBadge === 'pedagogical') {
    return { badge: 'pedagogical', reason: 'Preserved (pedagogical)', hasAxiom: usesAxiom }
  }
  if (currentBadge === 'fallacy') {
    return { badge: 'fallacy', reason: 'Preserved (fallacy example)', hasAxiom: usesAxiom }
  }
  if (currentBadge === 'from-axioms') {
    return { badge: 'from-axioms', reason: 'Preserved (from-axioms)', hasAxiom: usesAxiom }
  }
  if (currentBadge === 'original') {
    return { badge: 'original', reason: 'Preserved (original)', hasAxiom: usesAxiom }
  }

  // Determine badge based on sorry count and axioms
  if (sorryCount > 0) {
    return { badge: 'wip', reason: `Has ${sorryCount} sorry`, hasAxiom: usesAxiom }
  }

  if (usesAxiom) {
    return { badge: 'axiom', reason: 'Uses axioms, no sorries', hasAxiom: usesAxiom }
  }

  // Map invalid badges to valid ones
  if (currentBadge === 'formalized' || currentBadge === 'verified') {
    return { badge: 'mathlib', reason: 'Complete (was formalized/verified)', hasAxiom: usesAxiom }
  }
  if (currentBadge === 'axiomatized') {
    return { badge: 'axiom', reason: 'Complete (was axiomatized)', hasAxiom: usesAxiom }
  }

  return { badge: 'mathlib', reason: 'Complete, uses Mathlib', hasAxiom: usesAxiom }
}

/**
 * Update badges for all proofs
 */
function updateBadges(dryRun = false): UpdateResult[] {
  const results: UpdateResult[] = []
  const proofDirs = fs.readdirSync(PROOFS_DIR).filter(d => {
    const fullPath = path.join(PROOFS_DIR, d)
    return fs.statSync(fullPath).isDirectory() && fs.existsSync(path.join(fullPath, 'meta.json'))
  })

  console.log(`Scanning ${proofDirs.length} proof directories...\n`)

  for (const dir of proofDirs) {
    const metaPath = path.join(PROOFS_DIR, dir, 'meta.json')

    try {
      const metaContent = fs.readFileSync(metaPath, 'utf-8')
      const meta = JSON.parse(metaContent)

      // Get Lean file path from meta
      const leanRelPath = meta.meta?.proofRepoPath
      if (!leanRelPath) continue

      const leanPath = path.join('proofs', leanRelPath)
      if (!fs.existsSync(leanPath)) continue

      const leanContent = fs.readFileSync(leanPath, 'utf-8')
      const sorryCount = countSorries(leanContent)
      const currentBadge = meta.meta?.badge || 'wip'

      const { badge: newBadge, reason, hasAxiom: usesAxiom } = determineBadge(leanContent, currentBadge, sorryCount)

      // Update if badge changed
      if (currentBadge !== newBadge) {
        results.push({
          id: dir,
          oldBadge: currentBadge,
          newBadge,
          sorries: sorryCount,
          hasAxiom: usesAxiom,
          reason
        })

        if (!dryRun) {
          meta.meta.badge = newBadge
          meta.meta.sorries = sorryCount
          fs.writeFileSync(metaPath, JSON.stringify(meta, null, 2))
        }
      }
    } catch (error) {
      console.error(`Error processing ${dir}:`, error)
    }
  }

  return results
}

// Main
const args = process.argv.slice(2)
const dryRun = args.includes('--dry-run')

if (args.includes('--help') || args.includes('-h')) {
  console.log(`
Update Badge Script

Usage:
  npx tsx scripts/erdos/update-badges.ts           Run and update badges
  npx tsx scripts/erdos/update-badges.ts --dry-run Preview changes without updating

This script scans all proof Lean files and updates badges based on:
- sorry count (>0 = wip)
- axiom usage (axiom keyword = axiom badge)
- preserves manual badges (ai-solved, pedagogical, fallacy, etc.)
`)
  process.exit(0)
}

console.log(dryRun ? '=== DRY RUN - No files will be modified ===\n' : '=== Updating badges ===\n')

const results = updateBadges(dryRun)

if (results.length === 0) {
  console.log('No badge updates needed.')
} else {
  console.log(`\nUpdates${dryRun ? ' (preview)' : ''}:`)
  for (const r of results) {
    console.log(`  ${r.id}: ${r.oldBadge} → ${r.newBadge} (${r.reason})`)
  }
  console.log(`\nTotal: ${results.length} badge${results.length === 1 ? '' : 's'} ${dryRun ? 'would be ' : ''}updated`)
}

// Summary by badge type
const summary: Record<string, number> = {}
for (const r of results) {
  summary[`${r.oldBadge} → ${r.newBadge}`] = (summary[`${r.oldBadge} → ${r.newBadge}`] || 0) + 1
}

if (Object.keys(summary).length > 0) {
  console.log('\nSummary:')
  for (const [change, count] of Object.entries(summary).sort((a, b) => b[1] - a[1])) {
    console.log(`  ${change}: ${count}`)
  }
}
