/**
 * Update Aristotle candidates from existing gallery entries
 *
 * Reads meta.json from gallery entries and generates Aristotle candidates
 * for solved problems that aren't already in the pending_candidates list.
 */

import * as fs from 'fs'
import * as path from 'path'

const GALLERY_DIR = 'src/data/proofs'
const ARISTOTLE_JOBS_FILE = 'research/aristotle-jobs.json'

interface AristotleCandidate {
  problemId: string
  erdosNumber: number
  source: string
  tractabilityScore: number
  reason: string
  suggestedFile: string
  notes: string
}

interface AristotleJobsFile {
  version: string
  description: string
  jobs: any[]
  completed: any[]
  failed: any[]
  lessons_learned: string[]
  pending_candidates: AristotleCandidate[]
  notes?: string[]
}

/**
 * Estimate tractability based on problem characteristics
 */
function estimateTractability(meta: any): number {
  let score = 7 // Base score for solved problems

  // Higher score for shorter statements (simpler problems)
  const statement = meta.overview?.problemStatement || ''
  if (statement.length < 500) score++
  if (statement.length < 200) score++

  // Check for prize (indicates notable problem)
  if (meta.meta?.erdosPrizeValue) {
    const prizeMatch = meta.meta.erdosPrizeValue.match(/\$(\d+)/)
    if (prizeMatch) {
      const prize = parseInt(prizeMatch[1])
      // High prizes often mean hard problems - lower tractability
      if (prize >= 500) score--
      if (prize >= 1000) score--
    }
  }

  // Adjust for keywords indicating complexity
  const complexKeywords = ['infinite', 'countab', 'asymptotic', 'density', 'limit']
  const simpleKeywords = ['integer', 'sum', 'divisib', 'prime', 'square']

  for (const kw of complexKeywords) {
    if (statement.toLowerCase().includes(kw)) score--
  }
  for (const kw of simpleKeywords) {
    if (statement.toLowerCase().includes(kw)) score++
  }

  return Math.max(1, Math.min(10, score))
}

/**
 * Generate reason based on problem status
 */
function generateReason(meta: any): string {
  const status = meta.meta?.erdosProblemStatus || 'solved'
  if (status === 'solved') {
    return 'Solved problem - known proof exists for Aristotle to formalize'
  } else if (status === 'partially-solved') {
    return 'Partially solved - partial results can be formalized'
  }
  return 'Formalization target'
}

/**
 * Load Aristotle jobs file
 */
function loadAristotleJobs(): AristotleJobsFile {
  const jobsPath = path.resolve(process.cwd(), ARISTOTLE_JOBS_FILE)

  if (fs.existsSync(jobsPath)) {
    return JSON.parse(fs.readFileSync(jobsPath, 'utf-8'))
  }

  return {
    version: '1.0',
    description: 'Track Aristotle proof search jobs across research sessions',
    jobs: [],
    completed: [],
    failed: [],
    lessons_learned: [],
    pending_candidates: [],
  }
}

/**
 * Save Aristotle jobs file
 */
function saveAristotleJobs(jobs: AristotleJobsFile): void {
  const jobsPath = path.resolve(process.cwd(), ARISTOTLE_JOBS_FILE)
  fs.writeFileSync(jobsPath, JSON.stringify(jobs, null, 2))
}

/**
 * Main function
 */
function main() {
  console.log('Updating Aristotle candidates from gallery entries...\n')

  const galleryPath = path.resolve(process.cwd(), GALLERY_DIR)
  const erdosDirs = fs.readdirSync(galleryPath).filter(d => d.startsWith('erdos-'))

  console.log(`Found ${erdosDirs.length} Erdős gallery entries`)

  // Load existing candidates
  const jobs = loadAristotleJobs()
  const existingNumbers = new Set((jobs.pending_candidates || []).map(c => c.erdosNumber))

  console.log(`Existing candidates: ${existingNumbers.size}`)

  const newCandidates: AristotleCandidate[] = []

  for (const dir of erdosDirs) {
    const metaPath = path.join(galleryPath, dir, 'meta.json')

    if (!fs.existsSync(metaPath)) continue

    try {
      const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
      const erdosNumber = meta.meta?.erdosNumber

      if (!erdosNumber) continue

      // Skip if already in candidates
      if (existingNumbers.has(erdosNumber)) continue

      // Skip open problems
      const status = meta.meta?.erdosProblemStatus
      if (status === 'open') continue

      const tractability = estimateTractability(meta)

      // Only include high tractability candidates (7+)
      if (tractability < 7) continue

      const leanPath = meta.meta?.proofRepoPath || `Proofs/Erdos${erdosNumber}Problem.lean`

      newCandidates.push({
        problemId: meta.id,
        erdosNumber,
        source: 'gallery entries scan',
        tractabilityScore: tractability,
        reason: generateReason(meta),
        suggestedFile: `proofs/${leanPath}`,
        notes: `Tractability: ${tractability}/10. ${status} (formalization target)`,
      })
    } catch (err) {
      console.log(`  Error reading ${dir}: ${err}`)
    }
  }

  console.log(`Found ${newCandidates.length} new high-tractability candidates`)

  if (newCandidates.length > 0) {
    // Sort by tractability
    newCandidates.sort((a, b) => b.tractabilityScore - a.tractabilityScore)

    // Merge with existing
    jobs.pending_candidates = [
      ...(jobs.pending_candidates || []),
      ...newCandidates,
    ].sort((a, b) => b.tractabilityScore - a.tractabilityScore)

    saveAristotleJobs(jobs)
    console.log(`\nTotal candidates: ${jobs.pending_candidates.length}`)
  }

  // Print summary
  console.log('\n=== Top 15 Candidates ===')
  const top15 = (jobs.pending_candidates || []).slice(0, 15)
  for (const c of top15) {
    console.log(`  #${c.erdosNumber} (${c.tractabilityScore}/10): ${c.problemId}`)
  }

  console.log('\nDistribution:')
  const tier9_10 = (jobs.pending_candidates || []).filter(c => c.tractabilityScore >= 9).length
  const tier7_8 = (jobs.pending_candidates || []).filter(c => c.tractabilityScore >= 7 && c.tractabilityScore < 9).length
  console.log(`  High (9-10): ${tier9_10}`)
  console.log(`  Medium (7-8): ${tier7_8}`)
}

main()
