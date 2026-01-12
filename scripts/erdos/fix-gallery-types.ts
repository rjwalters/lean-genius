/**
 * Fix TypeScript type errors in generated gallery index.ts files
 *
 * Updates index.ts to use proper type assertions for JSON imports
 */

import * as fs from 'fs'
import * as path from 'path'

const GALLERY_DIR = path.resolve(process.cwd(), 'src/data/proofs')

/**
 * Generate proper index.ts content with type assertions
 */
function generateFixedIndexTs(leanFileName: string): string {
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
 * Extract lean file name from existing index.ts
 */
function extractLeanFileName(content: string): string | null {
  const match = content.match(/import.*'\.\.\/\.\.\/\.\.\/\.\.\/proofs\/Proofs\/([^']+)\.lean/)
  return match ? match[1] : null
}

/**
 * Fix all erdos gallery index.ts files
 */
function fixGalleryTypes() {
  const dirs = fs.readdirSync(GALLERY_DIR).filter(d => d.startsWith('erdos-'))

  let fixed = 0
  let skipped = 0
  let errors = 0

  for (const dir of dirs) {
    const indexPath = path.join(GALLERY_DIR, dir, 'index.ts')

    if (!fs.existsSync(indexPath)) {
      console.log(`  Skip: ${dir} - no index.ts`)
      skipped++
      continue
    }

    try {
      const content = fs.readFileSync(indexPath, 'utf-8')

      // Check if already fixed (has ProofMeta import)
      if (content.includes('ProofMeta, ProofSection')) {
        console.log(`  Skip: ${dir} - already fixed`)
        skipped++
        continue
      }

      // Extract lean file name
      const leanFileName = extractLeanFileName(content)
      if (!leanFileName) {
        console.log(`  Error: ${dir} - couldn't extract lean file name`)
        errors++
        continue
      }

      // Write fixed content
      const fixedContent = generateFixedIndexTs(leanFileName)
      fs.writeFileSync(indexPath, fixedContent)
      console.log(`  Fixed: ${dir}`)
      fixed++
    } catch (err) {
      console.log(`  Error: ${dir} - ${err}`)
      errors++
    }
  }

  console.log(`\nResults: ${fixed} fixed, ${skipped} skipped, ${errors} errors`)
}

// Run
console.log('Fixing gallery type errors...\n')
fixGalleryTypes()
