/**
 * Generate gallery stub templates for solved Erdős problems
 *
 * Creates:
 * - src/data/proofs/erdos-{n}-{slug}/meta.json
 * - src/data/proofs/erdos-{n}-{slug}/annotations.json
 * - src/data/proofs/erdos-{n}-{slug}/index.ts
 * - proofs/Proofs/Erdos{N}{PascalSlug}.lean (placeholder)
 */

import * as fs from 'fs'
import * as path from 'path'
import type { TransformedProblem, GalleryGenerationResult } from './types'

const GALLERY_DIR = 'src/data/proofs'
const PROOFS_DIR = 'proofs/Proofs'

/**
 * Convert slug to PascalCase for Lean file names
 */
function toPascalCase(slug: string): string {
  return slug
    .split('-')
    .map(part => part.charAt(0).toUpperCase() + part.slice(1))
    .join('')
}

/**
 * Generate a short description from the statement
 */
function generateDescription(problem: TransformedProblem): string {
  let desc = problem.statement.latex || problem.statement.html

  // Remove LaTeX commands
  desc = desc.replace(/\\[a-zA-Z]+\{[^}]*\}/g, '')
  desc = desc.replace(/\$[^$]+\$/g, '...')
  desc = desc.replace(/<[^>]+>/g, '')

  // Trim and limit length
  desc = desc.trim().slice(0, 200)

  if (desc.length >= 200) {
    desc = desc.slice(0, 197) + '...'
  }

  return desc || `Erdős Problem #${problem.number}`
}

/**
 * Generate meta.json content
 */
function generateMetaJson(problem: TransformedProblem): object {
  const pascalSlug = toPascalCase(problem.slug.replace(/^erdos-\d+-?/, ''))
  const leanFileName = `Erdos${problem.number}${pascalSlug || 'Problem'}`

  return {
    id: problem.slug,
    title: `Erdős Problem #${problem.number}`,
    slug: problem.slug,
    description: generateDescription(problem),
    meta: {
      author: 'Unknown',
      sourceUrl: problem.sourceUrl,
      date: '',
      status: 'pending',
      proofRepoPath: `Proofs/${leanFileName}.lean`,
      tags: problem.mappedTags,
      badge: 'wip',
      sorries: 1,
      erdosNumber: problem.number,
      erdosUrl: problem.sourceUrl,
      erdosProblemStatus: problem.status === 'SOLVED' ? 'solved' : problem.status === 'PARTIALLY_SOLVED' ? 'partially-solved' : 'open',
      ...(problem.prize && { erdosPrizeValue: problem.prize }),
    },
    overview: {
      historicalContext: `Erdős Problem #${problem.number} from erdosproblems.com.${problem.prize ? ` Originally offered with a prize of ${problem.prize}.` : ''}`,
      problemStatement: problem.statement.latex || problem.statement.html.slice(0, 1000),
      proofStrategy: 'TODO: Document proof strategy',
      keyInsights: [],
    },
    sections: [],
    conclusion: {
      summary: 'TODO: Add proof summary',
      implications: '',
      openQuestions: [],
    },
  }
}

/**
 * Generate annotations.json content (empty array)
 */
function generateAnnotationsJson(): object {
  return []
}

/**
 * Generate index.ts content
 */
function generateIndexTs(problem: TransformedProblem): string {
  const pascalSlug = toPascalCase(problem.slug.replace(/^erdos-\d+-?/, ''))
  const leanFileName = `Erdos${problem.number}${pascalSlug || 'Problem'}`

  return `import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

// Type assertion for JSON import
const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

// Import the Lean source file
const leanSource = () => import('../../../../proofs/Proofs/${leanFileName}.lean?raw')

export const proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '', // Loaded dynamically
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const annotations: Annotation[] = annotationsJson as Annotation[]

export const proofData: ProofData = {
  proof,
  annotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default proofData
`
}

/**
 * Generate Lean placeholder file
 */
function generateLeanPlaceholder(problem: TransformedProblem): string {
  const pascalSlug = toPascalCase(problem.slug.replace(/^erdos-\d+-?/, ''))
  const theoremName = `erdos_${problem.number}${pascalSlug ? `_${pascalSlug.toLowerCase()}` : ''}`

  // Clean up the statement for comments
  let statement = problem.statement.latex || problem.statement.html
  statement = statement.replace(/\n/g, '\n  ')
  if (statement.length > 500) {
    statement = statement.slice(0, 497) + '...'
  }

  return `/-
  Erdős Problem #${problem.number}

  Source: ${problem.sourceUrl}
  Status: ${problem.status}
  ${problem.prize ? `Prize: ${problem.prize}` : ''}

  Statement:
  ${statement}

  Tags: ${problem.tags.join(', ')}

  TODO: Implement proof
-/

import Mathlib

-- Placeholder theorem
-- Replace with actual statement and proof
theorem ${theoremName} : True := by
  trivial

-- sorry marker for tracking
#check ${theoremName}
`
}

/**
 * Generate gallery entry for a single problem
 */
export function generateGalleryEntry(
  problem: TransformedProblem,
  dryRun = false
): GalleryGenerationResult {
  const galleryPath = path.resolve(process.cwd(), GALLERY_DIR, problem.slug)
  const proofsPath = path.resolve(process.cwd(), PROOFS_DIR)

  const pascalSlug = toPascalCase(problem.slug.replace(/^erdos-\d+-?/, ''))
  const leanFileName = `Erdos${problem.number}${pascalSlug || 'Problem'}.lean`
  const leanPath = path.join(proofsPath, leanFileName)

  const files: string[] = []

  // Check if gallery directory already exists
  if (fs.existsSync(galleryPath)) {
    return {
      number: problem.number,
      slug: problem.slug,
      files: [],
      skipped: true,
      skipReason: 'Gallery directory already exists',
    }
  }

  // Check if Lean file already exists
  if (fs.existsSync(leanPath)) {
    return {
      number: problem.number,
      slug: problem.slug,
      files: [],
      skipped: true,
      skipReason: 'Lean file already exists',
    }
  }

  if (dryRun) {
    return {
      number: problem.number,
      slug: problem.slug,
      files: [
        path.join(GALLERY_DIR, problem.slug, 'meta.json'),
        path.join(GALLERY_DIR, problem.slug, 'annotations.json'),
        path.join(GALLERY_DIR, problem.slug, 'index.ts'),
        path.join(PROOFS_DIR, leanFileName),
      ],
      skipped: false,
    }
  }

  // Create gallery directory
  fs.mkdirSync(galleryPath, { recursive: true })

  // Write meta.json
  const metaPath = path.join(galleryPath, 'meta.json')
  fs.writeFileSync(metaPath, JSON.stringify(generateMetaJson(problem), null, 2))
  files.push(path.join(GALLERY_DIR, problem.slug, 'meta.json'))

  // Write annotations.json
  const annotationsPath = path.join(galleryPath, 'annotations.json')
  fs.writeFileSync(annotationsPath, JSON.stringify(generateAnnotationsJson(), null, 2))
  files.push(path.join(GALLERY_DIR, problem.slug, 'annotations.json'))

  // Write index.ts
  const indexPath = path.join(galleryPath, 'index.ts')
  fs.writeFileSync(indexPath, generateIndexTs(problem))
  files.push(path.join(GALLERY_DIR, problem.slug, 'index.ts'))

  // Ensure proofs directory exists
  if (!fs.existsSync(proofsPath)) {
    fs.mkdirSync(proofsPath, { recursive: true })
  }

  // Write Lean placeholder
  fs.writeFileSync(leanPath, generateLeanPlaceholder(problem))
  files.push(path.join(PROOFS_DIR, leanFileName))

  return {
    number: problem.number,
    slug: problem.slug,
    files,
    skipped: false,
  }
}

/**
 * Generate gallery entries for multiple problems
 */
export function generateGalleryEntries(
  problems: TransformedProblem[],
  dryRun = false
): GalleryGenerationResult[] {
  // Filter to only solved problems
  const solvedProblems = problems.filter(
    p => p.status === 'SOLVED' || p.status === 'PARTIALLY_SOLVED'
  )

  console.log(`Generating gallery entries for ${solvedProblems.length} solved problems...`)

  const results: GalleryGenerationResult[] = []

  for (const problem of solvedProblems) {
    const result = generateGalleryEntry(problem, dryRun)
    results.push(result)

    if (!result.skipped) {
      console.log(`  Created: ${problem.slug}`)
    }
  }

  const created = results.filter(r => !r.skipped).length
  const skipped = results.filter(r => r.skipped).length

  console.log(`Gallery generation complete: ${created} created, ${skipped} skipped`)

  return results
}

/**
 * Get gallery generation statistics
 */
export function getGalleryStats(results: GalleryGenerationResult[]): {
  created: number
  skipped: number
  skipReasons: Record<string, number>
  filesCreated: number
} {
  const skipReasons: Record<string, number> = {}

  for (const result of results) {
    if (result.skipped && result.skipReason) {
      skipReasons[result.skipReason] = (skipReasons[result.skipReason] || 0) + 1
    }
  }

  return {
    created: results.filter(r => !r.skipped).length,
    skipped: results.filter(r => r.skipped).length,
    skipReasons,
    filesCreated: results.reduce((sum, r) => sum + r.files.length, 0),
  }
}
