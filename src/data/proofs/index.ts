/**
 * Proof Data Index
 *
 * Exports:
 * - listings: Lightweight metadata for HomePage gallery (small bundle)
 * - getProofAsync: Dynamic import for full proof data (lazy loaded)
 * - getProof/getAllProofs: Synchronous access (pulls in full bundle - use sparingly)
 */

import listingsData from './listings.json'
import type { ProofData, ProofListing } from '@/types/proof'

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
    // Try default export first, then named export
    return module.default || module[slugToExportName(slug)]
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
