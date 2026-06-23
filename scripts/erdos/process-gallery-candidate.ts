#!/usr/bin/env npx tsx
/**
 * Process a single Erdős problem into the proof gallery
 *
 * Usage:
 *   npx tsx scripts/erdos/process-gallery-candidate.ts <problem-number>
 *   npx tsx scripts/erdos/process-gallery-candidate.ts --list
 *   npx tsx scripts/erdos/process-gallery-candidate.ts --next
 *
 * This script:
 * 1. Checks if the problem exists in formal-conjectures
 * 2. Copies the Lean file to proofs/Proofs/
 * 3. Creates gallery metadata stub
 * 4. Reports what manual work is needed (annotations, removing sorry)
 */

import * as fs from 'fs'
import * as path from 'path'

const FORMAL_CONJECTURES_DIR = 'external/formal-conjectures/FormalConjectures/ErdosProblems'
const PROOFS_DIR = 'proofs/Proofs'
const GALLERY_DIR = 'src/data/proofs'
const CANDIDATES_FILE = 'scripts/erdos/data/gallery-candidates.json'

interface GalleryCandidate {
  number: number
  status: string
  leanFile: string
  title?: string
  tags?: string[]
}

function loadCandidates(): GalleryCandidate[] {
  if (!fs.existsSync(CANDIDATES_FILE)) {
    console.error(`Candidates file not found: ${CANDIDATES_FILE}`)
    console.error('Run: npx tsx scripts/erdos/cross-reference.ts')
    process.exit(1)
  }
  return JSON.parse(fs.readFileSync(CANDIDATES_FILE, 'utf-8'))
}

function getProcessedNumbers(): Set<number> {
  const processed = new Set<number>()

  // Check existing proof files
  if (fs.existsSync(PROOFS_DIR)) {
    const files = fs.readdirSync(PROOFS_DIR)
    for (const file of files) {
      const match = file.match(/^Erdos(\d+)(?:Problem)?\.lean$/)
      if (match) {
        processed.add(parseInt(match[1]))
      }
    }
  }

  return processed
}

function listCandidates(): void {
  const candidates = loadCandidates()
  const processed = getProcessedNumbers()

  console.log('=== Gallery Candidates ===\n')
  console.log(`Total candidates: ${candidates.length}`)
  console.log(`Already processed: ${processed.size}`)
  console.log(`Remaining: ${candidates.length - [...candidates].filter(c => processed.has(c.number)).length}\n`)

  console.log('Unprocessed candidates:')
  for (const c of candidates) {
    if (!processed.has(c.number)) {
      console.log(`  #${c.number} [${c.status}] - ${c.leanFile}`)
    }
  }
}

function getNextCandidate(): GalleryCandidate | null {
  const candidates = loadCandidates()
  const processed = getProcessedNumbers()

  // Prioritize: proved > disproved > solved
  const priority = ['proved', 'disproved', 'solved']

  for (const status of priority) {
    for (const c of candidates) {
      if (c.status === status && !processed.has(c.number)) {
        return c
      }
    }
  }

  return null
}

function processCandidate(problemNumber: number): void {
  const candidates = loadCandidates()
  const candidate = candidates.find(c => c.number === problemNumber)

  if (!candidate) {
    console.error(`Problem #${problemNumber} is not in gallery candidates`)
    console.error('Check: scripts/erdos/data/gallery-candidates.json')
    process.exit(1)
  }

  console.log(`=== Processing Erdős #${problemNumber} ===\n`)
  console.log(`Status: ${candidate.status}`)
  console.log(`Lean file: ${candidate.leanFile}\n`)

  // Check if formal-conjectures has the file
  const formalLeanPath = path.join(FORMAL_CONJECTURES_DIR, `${problemNumber}.lean`)
  const hasLeanSource = fs.existsSync(formalLeanPath)

  if (hasLeanSource) {
    console.log(`✓ Found Lean source: ${formalLeanPath}`)
  } else {
    console.log(`✗ No Lean source in formal-conjectures`)
    console.log(`  You'll need to write the proof from scratch\n`)
  }

  // Target paths
  const proofFileName = `Erdos${problemNumber}Problem.lean`
  const proofPath = path.join(PROOFS_DIR, proofFileName)
  const gallerySlug = `erdos-${problemNumber}`
  const galleryPath = path.join(GALLERY_DIR, gallerySlug)

  // Check if already exists
  if (fs.existsSync(proofPath)) {
    console.log(`\n⚠ Proof file already exists: ${proofPath}`)
  } else if (hasLeanSource) {
    // Copy Lean file
    console.log(`\nCopying Lean file...`)
    const leanContent = fs.readFileSync(formalLeanPath, 'utf-8')

    // Add our header and imports
    const modifiedContent = `/-
Erdős Problem #${problemNumber}
Status: ${candidate.status}

Source: formal-conjectures repository
Adapted for lean-genius proof gallery

TODO:
- [ ] Remove sorry placeholders
- [ ] Add educational annotations
- [ ] Verify builds: lake build Proofs.Erdos${problemNumber}Problem
-/

${leanContent}
`

    fs.writeFileSync(proofPath, modifiedContent)
    console.log(`✓ Created: ${proofPath}`)
  }

  // Create gallery directory
  if (fs.existsSync(galleryPath)) {
    console.log(`⚠ Gallery entry already exists: ${galleryPath}`)
  } else {
    fs.mkdirSync(galleryPath, { recursive: true })

    // Create gallery metadata stub using the app's expected file names.
    const title = `Erdős Problem #${problemNumber}`
    const description = `Erdős problem #${problemNumber} (${candidate.status})`
    const sourceUrl = `https://erdosproblems.com/${problemNumber}`
    const erdosProblemStatus = candidate.status === 'proved' ? 'solved' :
                               candidate.status === 'disproved' ? 'disproved' : 'partial'
    const meta = {
      id: gallerySlug,
      title,
      slug: gallerySlug,
      description,
      meta: {
        author: 'Erdős',
        sourceUrl,
        status: 'stub',
        proofRepoPath: `Proofs/${proofFileName}`,
        tags: candidate.tags || ['erdos', 'number-theory'],
        badge: 'stub',
        sorries: 1,
        erdosNumber: problemNumber,
        erdosUrl: sourceUrl,
        erdosProblemStatus,
      },
      overview: {
        historicalContext: `This is a stub entry for Erdős Problem #${problemNumber}. Full historical context pending enhancement.`,
        problemStatement: 'Problem statement pending.',
        proofStrategy: 'Pending enhancement.',
        keyInsights: ['Pending enhancement'],
      },
      sections: [],
      conclusion: {
        summary: 'Stub entry - enhancement needed.',
        implications: 'Pending.',
        openQuestions: [],
      },
    }
    const annotations = [
      {
        id: `${gallerySlug}-stub`,
        proofId: gallerySlug,
        type: 'context',
        range: { startLine: 1, endLine: 10 },
        title: 'Stub Entry',
        content: `This is a stub entry for Erdős Problem #${problemNumber}. Enhancement needed to add proper formalization and annotations.`,
        significance: 'supporting',
      },
    ]
    const indexTs = `import meta from './meta.json'
import annotations from './annotations.json'

export { meta, annotations }
`

    fs.writeFileSync(
      path.join(galleryPath, 'meta.json'),
      JSON.stringify(meta, null, 2) + '\n'
    )
    fs.writeFileSync(
      path.join(galleryPath, 'annotations.json'),
      JSON.stringify(annotations, null, 2) + '\n'
    )
    fs.writeFileSync(path.join(galleryPath, 'index.ts'), indexTs)
    console.log(`✓ Created: ${galleryPath}/meta.json`)
    console.log(`✓ Created: ${galleryPath}/annotations.json`)
    console.log(`✓ Created: ${galleryPath}/index.ts`)
  }

  // Print next steps
  console.log('\n=== Next Steps ===\n')
  console.log('1. Edit the Lean file to remove sorry:')
  console.log(`   code ${proofPath}\n`)
  console.log('2. Build and verify:')
  console.log(`   cd proofs && lake build Proofs.Erdos${problemNumber}Problem\n`)
  console.log('3. Improve annotations:')
  console.log(`   Edit ${galleryPath}/annotations.json\n`)
  console.log('4. Update meta.json with proper description and context\n')
  console.log('5. Full build:')
  console.log('   pnpm build\n')
}

// Main
const args = process.argv.slice(2)

if (args.length === 0 || args[0] === '--help' || args[0] === '-h') {
  console.log(`
Erdős Gallery Candidate Processor

Usage:
  npx tsx scripts/erdos/process-gallery-candidate.ts <number>  Process specific problem
  npx tsx scripts/erdos/process-gallery-candidate.ts --list    List all candidates
  npx tsx scripts/erdos/process-gallery-candidate.ts --next    Process next unprocessed

Examples:
  npx tsx scripts/erdos/process-gallery-candidate.ts 494
  npx tsx scripts/erdos/process-gallery-candidate.ts --next
`)
  process.exit(0)
}

if (args[0] === '--list') {
  listCandidates()
} else if (args[0] === '--next') {
  const next = getNextCandidate()
  if (next) {
    console.log(`Next candidate: #${next.number}\n`)
    processCandidate(next.number)
  } else {
    console.log('All candidates have been processed!')
  }
} else {
  const num = parseInt(args[0])
  if (isNaN(num)) {
    console.error(`Invalid problem number: ${args[0]}`)
    process.exit(1)
  }
  processCandidate(num)
}
