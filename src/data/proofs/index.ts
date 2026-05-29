/**
 * Proof Data Index
 *
 * Exports:
 * - listings: Lightweight metadata for HomePage gallery (small bundle)
 * - getProofAsync: Dynamic import for full proof data (lazy loaded)
 * - getProof/getAllProofs: Synchronous access (pulls in full bundle - use sparingly)
 */

import listingsData from './listings.json'
import type { Annotation, ProofData, ProofListing } from '@/types/proof'

// Lightweight listings for HomePage - does not pull in proof data
export const listings: ProofListing[] = listingsData as ProofListing[]

// Auto-discover all proof modules using Vite's glob import
// This automatically finds all index.ts files in subdirectories
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const proofModuleGlobs = import.meta.glob<any>('./**/index.ts')

// Build the proofModules map from glob results
// Convert paths like './erdos-105/index.ts' to slugs like 'erdos-105'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const proofModules: Record<string, () => Promise<any>> = {}

for (const path in proofModuleGlobs) {
  // Extract slug from path: './some-proof/index.ts' -> 'some-proof'
  const match = path.match(/^\.\/([^/]+)\/index\.ts$/)
  if (match) {
    const slug = match[1]
    proofModules[slug] = proofModuleGlobs[path]
  }
}

/**
 * Convert kebab-case slug to camelCase export name
 * e.g., "navier-stokes" -> "navierStokesData"
 */
function slugToExportName(slug: string): string {
  const camel = slug.replace(/-([a-z0-9])/g, (_, c) => c.toUpperCase())
  return camel + 'Data'
}

/**
 * Asynchronously load proof data for a given slug.
 * This enables per-proof code splitting - only loads the requested proof.
 */
export async function getProofAsync(slug: string): Promise<ProofData | undefined> {
  const loader = proofModules[slug]
  if (!loader) return undefined

  try {
    const module = await loader()
    // Try default export first, then named export, then fallback to first *Data export
    // (fallback handles casing mismatches like OQ vs Oq in export names)
    const exportName = slugToExportName(slug)
    let proofData: ProofData | undefined = module.default || module[exportName] ||
      Object.keys(module).filter(k => k.endsWith('Data')).map(k => module[k]).find(v => v?.proof)

    // Fallback: construct ProofData from legacy { meta, annotations } exports
    if (!proofData && module.meta) {
      const m = module.meta.default || module.meta
      proofData = {
        proof: {
          id: m.id,
          title: m.title,
          slug: m.slug,
          description: m.description,
          meta: m.meta,
          sections: m.sections || [],
          overview: m.overview,
          conclusion: m.conclusion,
          crossReferences: m.crossReferences,
          references: m.references,
          source: '',
        },
        annotations: (module.annotations?.default || module.annotations || []) as Annotation[],
      }
    }

    // Inject crossReferences from raw meta.json if the proof object doesn't have them
    if (proofData?.proof && !proofData.proof.crossReferences) {
      const rawMeta = module.meta?.default || module.meta || module.default?.proof
      const crossRefs = rawMeta?.crossReferences
      if (crossRefs && Array.isArray(crossRefs)) {
        proofData.proof.crossReferences = crossRefs
      }
    }

    // Inject references from raw meta.json if the proof object doesn't have them
    if (proofData?.proof && !proofData.proof.references) {
      const rawMeta = module.meta?.default || module.meta || module.default?.proof
      const refs = rawMeta?.references
      if (refs && Array.isArray(refs)) {
        proofData.proof.references = refs
      }
    }

    // Normalize annotations: convert legacy {lineNumber} format to {range}
    if (proofData?.annotations) {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      proofData.annotations = proofData.annotations.filter((ann: any) => {
        if (ann.range) return true
        const line = ann.lineNumber ?? ann.line
        if (line != null) {
          ann.range = { startLine: line, endLine: line }
          return true
        }
        return false // drop annotations with no range, lineNumber, or line
      })
    }

    // Load the Lean source from the build-generated static asset tree instead
    // of importing it through the module graph. The emit step in
    // scripts/annotations/build.ts copies each proof's Lean file to
    // public/data/proofs/<slug>/source.lean, which Vite/Cloudflare serve at the
    // site root. This keeps the ~1339 large `?raw` modules out of the Rollup
    // build graph (build-perf phase 1, issue #20992). On any fetch failure the
    // source is left empty rather than failing the whole proof load.
    if (proofData?.proof) {
      try {
        const res = await fetch(`/data/proofs/${slug}/source.lean`)
        if (res.ok) proofData.proof.source = await res.text()
      } catch {
        /* leave source empty on failure */
      }
    }

    return proofData
  } catch (e) {
    console.error(`Failed to load proof: ${slug}`, e)
    return undefined
  }
}

// Cache for synchronous access (populated on first use)
let proofsCache: Record<string, ProofData> | null = null

/**
 * Synchronously get a proof by slug.
 * WARNING: This pulls in ALL proof data into the bundle.
 * Prefer getProofAsync for better code splitting.
 */
export function getProof(slug: string): ProofData | undefined {
  if (!proofsCache) {
    proofsCache = {}
    // This will be tree-shaken if only getProofAsync is used
  }
  return proofsCache[slug]
}

/**
 * Get all proofs synchronously.
 * WARNING: This pulls in ALL proof data into the bundle.
 * Prefer using `listings` for HomePage gallery.
 */
export function getAllProofs(): ProofData[] {
  if (!proofsCache) {
    return []
  }
  return Object.values(proofsCache)
}
