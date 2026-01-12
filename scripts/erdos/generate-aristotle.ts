/**
 * Generate Aristotle job candidates from Erdős problems
 *
 * Key insight from lessons learned:
 * - Aristotle = proof search (known results only!)
 * - Claude = creative work (OPEN problems)
 *
 * So we prioritize SOLVED problems for Aristotle (formalization targets)
 * and DON'T send OPEN conjectures.
 */

import * as fs from 'fs'
import * as path from 'path'
import type { TransformedProblem, AristotleCandidate } from './types'

const ARISTOTLE_JOBS_FILE = 'research/aristotle-jobs.json'

interface AristotleJobsFile {
  version: string
  description: string
  jobs: any[]
  completed: any[]
  failed: any[]
  lessons_learned: string[]
  pending_candidates?: AristotleCandidate[]
}

/**
 * Load the Aristotle jobs file
 */
function loadAristotleJobs(): AristotleJobsFile {
  const jobsPath = path.resolve(process.cwd(), ARISTOTLE_JOBS_FILE)

  if (fs.existsSync(jobsPath)) {
    try {
      return JSON.parse(fs.readFileSync(jobsPath, 'utf-8'))
    } catch {
      // Corrupted file
    }
  }

  return {
    version: '1.0',
    description: 'Track Aristotle proof search jobs across research sessions',
    jobs: [],
    completed: [],
    failed: [],
    lessons_learned: [
      'Aristotle = proof search (known results), Claude = creative work (OPEN problems)',
      "Don't send OPEN conjectures to Aristotle - no proof exists to find",
    ],
  }
}

/**
 * Save the Aristotle jobs file
 */
function saveAristotleJobs(jobs: AristotleJobsFile): void {
  const jobsPath = path.resolve(process.cwd(), ARISTOTLE_JOBS_FILE)
  fs.writeFileSync(jobsPath, JSON.stringify(jobs, null, 2))
}

/**
 * Convert slug to Lean file name
 */
function toLeanFileName(slug: string): string {
  const pascalSlug = slug
    .replace(/^erdos-(\d+)-?/, 'Erdos$1')
    .split('-')
    .map(part => part.charAt(0).toUpperCase() + part.slice(1))
    .join('')
  return `proofs/Proofs/${pascalSlug}.lean`
}

/**
 * Select Aristotle candidates from problems
 *
 * Priority:
 * 1. SOLVED problems with high tractability (formalization targets)
 * 2. PARTIALLY_SOLVED problems with high tractability
 * 3. OPEN problems are NOT suitable for Aristotle!
 */
export function selectAristotleCandidates(problems: TransformedProblem[]): AristotleCandidate[] {
  const candidates: AristotleCandidate[] = []

  for (const problem of problems) {
    // Skip OPEN problems - Aristotle can't prove unknown results
    if (problem.status === 'OPEN') {
      continue
    }

    // Skip if not suitable
    if (!problem.aristotleSuitable) {
      continue
    }

    // Determine suitability reason and notes
    let reason = ''
    let notes = ''

    if (problem.status === 'SOLVED') {
      reason = `Solved problem - known proof exists for Aristotle to formalize`
      notes = `Tractability: ${problem.tractability}/10. ${problem.tractabilityReason}`
    } else if (problem.status === 'PARTIALLY_SOLVED') {
      reason = `Partially solved - partial results can be formalized`
      notes = `Tractability: ${problem.tractability}/10. Focus on proven partial results only.`
    }

    candidates.push({
      problemId: problem.slug,
      erdosNumber: problem.number,
      source: 'erdosproblems.com scrape',
      tractabilityScore: problem.tractability,
      reason,
      suggestedFile: toLeanFileName(problem.slug),
      notes,
    })
  }

  // Sort by tractability score (highest first)
  candidates.sort((a, b) => b.tractabilityScore - a.tractabilityScore)

  return candidates
}

/**
 * Generate Aristotle candidates and optionally save to jobs file
 */
export function generateAristotleCandidates(
  problems: TransformedProblem[],
  dryRun = false,
  updateJobsFile = true
): AristotleCandidate[] {
  console.log('Selecting Aristotle candidates...')

  const candidates = selectAristotleCandidates(problems)

  console.log(`Found ${candidates.length} suitable candidates for Aristotle`)

  // Group by tractability tier
  const tier9_10 = candidates.filter(c => c.tractabilityScore >= 9)
  const tier7_8 = candidates.filter(c => c.tractabilityScore >= 7 && c.tractabilityScore < 9)
  const tier5_6 = candidates.filter(c => c.tractabilityScore >= 5 && c.tractabilityScore < 7)

  console.log(`  High priority (9-10): ${tier9_10.length}`)
  console.log(`  Medium priority (7-8): ${tier7_8.length}`)
  console.log(`  Lower priority (5-6): ${tier5_6.length}`)

  if (updateJobsFile && !dryRun && candidates.length > 0) {
    const jobs = loadAristotleJobs()

    // Merge candidates with existing list (avoid duplicates by erdosNumber)
    const existing = jobs.pending_candidates || []
    const existingNumbers = new Set(existing.map(c => c.erdosNumber))
    const newCandidates = candidates.filter(c => !existingNumbers.has(c.erdosNumber))

    jobs.pending_candidates = [...existing, ...newCandidates]
      .sort((a, b) => b.tractabilityScore - a.tractabilityScore)

    saveAristotleJobs(jobs)
    console.log(`  Added ${newCandidates.length} new candidates (${jobs.pending_candidates.length} total) to ${ARISTOTLE_JOBS_FILE}`)
  }

  return candidates
}

/**
 * Get statistics about Aristotle candidates
 */
export function getAristotleStats(candidates: AristotleCandidate[]): {
  total: number
  byTractability: Record<string, number>
  topCandidates: AristotleCandidate[]
} {
  const byTractability: Record<string, number> = {}

  for (const c of candidates) {
    const bucket = `${c.tractabilityScore}`
    byTractability[bucket] = (byTractability[bucket] || 0) + 1
  }

  return {
    total: candidates.length,
    byTractability,
    topCandidates: candidates.slice(0, 10),
  }
}

/**
 * Print Aristotle candidate report
 */
export function printAristotleReport(candidates: AristotleCandidate[]): void {
  const stats = getAristotleStats(candidates)

  console.log('\n=== Aristotle Candidates ===')
  console.log(`Total suitable candidates: ${stats.total}`)
  console.log('\nDistribution by tractability score:')

  for (let i = 10; i >= 1; i--) {
    const count = stats.byTractability[`${i}`] || 0
    if (count > 0) {
      console.log(`  Score ${i}: ${count}`)
    }
  }

  if (stats.topCandidates.length > 0) {
    console.log('\nTop 10 candidates:')
    for (const c of stats.topCandidates) {
      console.log(`  #${c.erdosNumber} (${c.tractabilityScore}/10): ${c.reason}`)
    }
  }

  console.log('\nNote: Only SOLVED/PARTIALLY_SOLVED problems are candidates.')
  console.log('OPEN problems should be tackled by Claude, not Aristotle.')
}
