/**
 * Deduplication module for Erdős problems
 *
 * Checks for existing gallery and research entries to avoid overwriting
 */

import * as fs from 'fs'
import * as path from 'path'
import type { DedupeResult, TransformedProblem } from './types'

const GALLERY_DIR = 'src/data/proofs'
const RESEARCH_DIR = 'research/problems'

interface ExistingEntry {
  type: 'gallery' | 'research'
  slug: string
  erdosNumber?: number
  path: string
}

/**
 * Scan gallery directory for existing Erdős entries
 */
function scanGalleryEntries(): ExistingEntry[] {
  const entries: ExistingEntry[] = []
  const galleryPath = path.resolve(process.cwd(), GALLERY_DIR)

  if (!fs.existsSync(galleryPath)) {
    return entries
  }

  const dirs = fs.readdirSync(galleryPath, { withFileTypes: true })
    .filter(d => d.isDirectory())

  for (const dir of dirs) {
    const metaPath = path.join(galleryPath, dir.name, 'meta.json')

    if (!fs.existsSync(metaPath)) continue

    try {
      const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
      const erdosNumber = meta.meta?.erdosNumber

      // Only include if it's an Erdős-related entry
      if (
        dir.name.toLowerCase().includes('erdos') ||
        erdosNumber ||
        meta.meta?.tags?.includes('erdos')
      ) {
        entries.push({
          type: 'gallery',
          slug: dir.name,
          erdosNumber,
          path: path.join(GALLERY_DIR, dir.name),
        })
      }
    } catch {
      // Skip invalid meta.json files
    }
  }

  return entries
}

/**
 * Scan research directory for existing Erdős entries
 */
function scanResearchEntries(): ExistingEntry[] {
  const entries: ExistingEntry[] = []
  const researchPath = path.resolve(process.cwd(), RESEARCH_DIR)

  if (!fs.existsSync(researchPath)) {
    return entries
  }

  const items = fs.readdirSync(researchPath, { withFileTypes: true })

  for (const item of items) {
    // Check directories
    if (item.isDirectory() && item.name.toLowerCase().includes('erdos')) {
      // Try to extract erdos number from directory name
      const match = item.name.match(/erdos-?(\d+)/i)
      const erdosNumber = match ? parseInt(match[1]) : undefined

      entries.push({
        type: 'research',
        slug: item.name,
        erdosNumber,
        path: path.join(RESEARCH_DIR, item.name),
      })
    }

    // Check individual markdown files (like erdos-124.md)
    if (item.isFile() && item.name.toLowerCase().includes('erdos') && item.name.endsWith('.md')) {
      const slug = item.name.replace('.md', '')
      const match = slug.match(/erdos-?(\d+)/i)
      const erdosNumber = match ? parseInt(match[1]) : undefined

      entries.push({
        type: 'research',
        slug,
        erdosNumber,
        path: path.join(RESEARCH_DIR, item.name),
      })
    }
  }

  return entries
}

/**
 * Get all existing Erdős entries
 */
export function getExistingEntries(): ExistingEntry[] {
  const gallery = scanGalleryEntries()
  const research = scanResearchEntries()
  return [...gallery, ...research]
}

/**
 * Check if a problem number is a duplicate
 */
export function checkDuplicate(
  problemNumber: number,
  existingEntries?: ExistingEntry[]
): DedupeResult {
  const entries = existingEntries || getExistingEntries()

  // First check by exact erdos number match
  const byNumber = entries.filter(e => e.erdosNumber === problemNumber)
  if (byNumber.length > 0) {
    const hasGallery = byNumber.some(e => e.type === 'gallery')
    const hasResearch = byNumber.some(e => e.type === 'research')

    return {
      number: problemNumber,
      isDuplicate: true,
      existingType: hasGallery && hasResearch ? 'both' : hasGallery ? 'gallery' : 'research',
      existingSlug: byNumber[0].slug,
      matchReason: `matched by erdosNumber ${problemNumber}`,
    }
  }

  // Also check by slug pattern (erdos-{number} or erdos-{number}-*)
  const slugPattern = new RegExp(`erdos-?${problemNumber}(?:-|$)`, 'i')
  const bySlug = entries.filter(e => slugPattern.test(e.slug))
  if (bySlug.length > 0) {
    const hasGallery = bySlug.some(e => e.type === 'gallery')
    const hasResearch = bySlug.some(e => e.type === 'research')

    return {
      number: problemNumber,
      isDuplicate: true,
      existingType: hasGallery && hasResearch ? 'both' : hasGallery ? 'gallery' : 'research',
      existingSlug: bySlug[0].slug,
      matchReason: `matched by slug pattern for #${problemNumber}`,
    }
  }

  return {
    number: problemNumber,
    isDuplicate: false,
  }
}

/**
 * Filter problems to remove duplicates
 */
export function filterDuplicates(problems: TransformedProblem[]): {
  unique: TransformedProblem[]
  duplicates: Array<{ problem: TransformedProblem; result: DedupeResult }>
} {
  const existingEntries = getExistingEntries()
  const unique: TransformedProblem[] = []
  const duplicates: Array<{ problem: TransformedProblem; result: DedupeResult }> = []

  for (const problem of problems) {
    const result = checkDuplicate(problem.number, existingEntries)

    if (result.isDuplicate) {
      duplicates.push({ problem, result })
    } else {
      unique.push(problem)
    }
  }

  return { unique, duplicates }
}

/**
 * Get deduplication statistics
 */
export function getDedupeStats(): {
  galleryCount: number
  researchCount: number
  uniqueErdosNumbers: number[]
  entries: ExistingEntry[]
} {
  const entries = getExistingEntries()
  const erdosNumbers = new Set<number>()

  for (const entry of entries) {
    if (entry.erdosNumber) {
      erdosNumbers.add(entry.erdosNumber)
    }
  }

  return {
    galleryCount: entries.filter(e => e.type === 'gallery').length,
    researchCount: entries.filter(e => e.type === 'research').length,
    uniqueErdosNumbers: Array.from(erdosNumbers).sort((a, b) => a - b),
    entries,
  }
}

/**
 * Print deduplication report
 */
export function printDedupeReport(): void {
  const stats = getDedupeStats()

  console.log('\n=== Existing Erdős Entries ===')
  console.log(`Gallery entries: ${stats.galleryCount}`)
  console.log(`Research entries: ${stats.researchCount}`)
  console.log(`Unique Erdős numbers: ${stats.uniqueErdosNumbers.length}`)

  if (stats.uniqueErdosNumbers.length > 0) {
    console.log(`Numbers: ${stats.uniqueErdosNumbers.join(', ')}`)
  }

  console.log('\nEntries:')
  for (const entry of stats.entries) {
    const numStr = entry.erdosNumber ? `#${entry.erdosNumber}` : '(no number)'
    console.log(`  [${entry.type}] ${entry.slug} ${numStr}`)
  }
}
