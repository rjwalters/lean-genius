#!/usr/bin/env npx tsx
/**
 * Quality audit for Erdős gallery and research data.
 *
 * Detects all known junk patterns and quality issues:
 * - Gallery entries with placeholder proofs (True := trivial)
 * - Gallery entries with scraping artifacts in descriptions
 * - Gallery entries with empty/missing annotations
 * - Research entries with "Problem statement not found"
 * - Research entries with "Relevance" table header artifact
 * - Missing Lean files for gallery entries
 *
 * Usage:
 *   npx tsx scripts/erdos/quality-audit.ts              # Summary
 *   npx tsx scripts/erdos/quality-audit.ts --verbose     # Detailed report
 *   npx tsx scripts/erdos/quality-audit.ts --json        # JSON output
 *   npx tsx scripts/erdos/quality-audit.ts --fail-on-issues  # CI mode (exit 1 if issues)
 */

import * as fs from 'fs'
import * as path from 'path'

interface QualityIssue {
  type: 'placeholder-proof' | 'garbage-description' | 'empty-annotations' |
        'missing-statement' | 'relevance-artifact' | 'missing-lean-file'
  path: string
  details: string
}

interface AuditResult {
  issues: QualityIssue[]
  summary: {
    galleryEntries: number
    researchEntries: number
    totalIssues: number
    issuesByType: Record<string, number>
  }
}

const GALLERY_DIR = 'src/data/proofs'
const RESEARCH_DIR = 'src/data/research/problems'
const PROOFS_DIR = 'proofs/Proofs'

// Navigation artifacts from erdosproblems.com scraping
const NAV_ARTIFACTS = ['Forum', 'Favourites', 'Random Solved', 'Dual View', 'Random Open']

function auditGalleryEntry(entryPath: string): QualityIssue[] {
  const issues: QualityIssue[] = []
  const dirName = path.basename(entryPath)
  const erdosMatch = dirName.match(/^erdos-(\d+)$/)
  if (!erdosMatch) return issues
  const erdosNum = erdosMatch[1]

  // Check for missing Lean file
  const leanFile = path.join(PROOFS_DIR, `Erdos${erdosNum}Problem.lean`)
  if (!fs.existsSync(leanFile)) {
    issues.push({
      type: 'missing-lean-file',
      path: entryPath,
      details: `Lean file not found: ${leanFile}`
    })
  } else {
    // Check for placeholder proofs
    const leanContent = fs.readFileSync(leanFile, 'utf-8')
    if (leanContent.includes('True := trivial') ||
        leanContent.includes('True := by trivial')) {
      issues.push({
        type: 'placeholder-proof',
        path: entryPath,
        details: 'Contains placeholder proof (True := trivial)'
      })
    }
  }

  // Check for garbage descriptions
  const metaFile = path.join(entryPath, 'meta.json')
  if (fs.existsSync(metaFile)) {
    const metaContent = fs.readFileSync(metaFile, 'utf-8')
    for (const artifact of NAV_ARTIFACTS) {
      if (metaContent.includes(artifact)) {
        issues.push({
          type: 'garbage-description',
          path: entryPath,
          details: `Description contains scraping artifact: "${artifact}"`
        })
        break
      }
    }
  }

  // Check for empty annotations
  const annotationsFile = path.join(entryPath, 'annotations.json')
  if (!fs.existsSync(annotationsFile)) {
    issues.push({
      type: 'empty-annotations',
      path: entryPath,
      details: 'annotations.json missing'
    })
  } else {
    const content = fs.readFileSync(annotationsFile, 'utf-8')
    try {
      const parsed = JSON.parse(content)
      const entries = Array.isArray(parsed) ? parsed.length : Object.keys(parsed).length
      if (entries < 3) {
        issues.push({
          type: 'empty-annotations',
          path: entryPath,
          details: `annotations.json has only ${entries} entries`
        })
      }
    } catch {
      issues.push({
        type: 'empty-annotations',
        path: entryPath,
        details: 'annotations.json is invalid JSON'
      })
    }
  }

  return issues
}

function auditResearchEntry(filePath: string): QualityIssue[] {
  const issues: QualityIssue[] = []
  try {
    const content = fs.readFileSync(filePath, 'utf-8')
    const data = JSON.parse(content)

    // Check for missing problem statement
    if (data.problemStatement?.plain === 'Problem statement not found') {
      issues.push({
        type: 'missing-statement',
        path: filePath,
        details: 'Problem statement not found'
      })
    }

    // Check for "Relevance" artifact in relatedProofs
    if (Array.isArray(data.relatedProofs) && data.relatedProofs.includes('Relevance')) {
      issues.push({
        type: 'relevance-artifact',
        path: filePath,
        details: 'Contains "Relevance" table header artifact in relatedProofs'
      })
    }
  } catch (e) {
    issues.push({
      type: 'missing-statement',
      path: filePath,
      details: `Failed to parse JSON: ${e}`
    })
  }

  return issues
}

function runAudit(): AuditResult {
  const issues: QualityIssue[] = []

  // Audit gallery entries
  const galleryEntries = fs.existsSync(GALLERY_DIR)
    ? fs.readdirSync(GALLERY_DIR)
        .filter(e => e.startsWith('erdos-'))
        .map(e => path.join(GALLERY_DIR, e))
        .filter(p => fs.statSync(p).isDirectory())
    : []

  for (const entry of galleryEntries) {
    issues.push(...auditGalleryEntry(entry))
  }

  // Audit research entries
  const researchFiles = fs.existsSync(RESEARCH_DIR)
    ? fs.readdirSync(RESEARCH_DIR)
        .filter(f => f.endsWith('.json'))
        .map(f => path.join(RESEARCH_DIR, f))
    : []

  for (const file of researchFiles) {
    issues.push(...auditResearchEntry(file))
  }

  // Calculate summary
  const issuesByType: Record<string, number> = {}
  for (const issue of issues) {
    issuesByType[issue.type] = (issuesByType[issue.type] || 0) + 1
  }

  return {
    issues,
    summary: {
      galleryEntries: galleryEntries.length,
      researchEntries: researchFiles.length,
      totalIssues: issues.length,
      issuesByType
    }
  }
}

// Main
const args = process.argv.slice(2)
const result = runAudit()

if (args.includes('--json')) {
  console.log(JSON.stringify(result, null, 2))
} else {
  console.log('=== Erdos Data Quality Audit ===\n')
  console.log(`Gallery entries:  ${result.summary.galleryEntries}`)
  console.log(`Research entries: ${result.summary.researchEntries}`)
  console.log(`Issues found:     ${result.summary.totalIssues}\n`)

  if (Object.keys(result.summary.issuesByType).length > 0) {
    console.log('Issues by type:')
    for (const [type, count] of Object.entries(result.summary.issuesByType)) {
      console.log(`  ${type}: ${count}`)
    }
  } else {
    console.log('No issues found - all data passes quality checks.')
  }

  if (args.includes('--verbose') && result.issues.length > 0) {
    console.log('\nDetailed issues:')
    for (const issue of result.issues) {
      console.log(`\n  [${issue.type}] ${issue.path}`)
      console.log(`    ${issue.details}`)
    }
  }
}

// Exit with error code if issues found and --fail-on-issues flag set
if (args.includes('--fail-on-issues') && result.issues.length > 0) {
  process.exit(1)
}
