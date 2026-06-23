/**
 * Proof Data Index
 *
 * Exports:
 * - listings: Lightweight metadata for HomePage gallery (small bundle, in-graph)
 * - getProofAsync: Fetch full proof data by slug from the static asset tree
 *
 * Phase 2 of the build-perf durable fix (issue #20993, follow-up to phase 1
 * issue #20992). Previously this module used `import.meta.glob` to discover
 * ~2435 per-proof shim modules, each of which statically imported
 * a meta.json + annotations.json — for ~7300 data modules in the vite/Rollup
 * graph. That O(N) blowup pushed the build past the 20-minute deploy cap and
 * stalled at the transform stage near the 8 GB Node heap. Phase 2 collapses
 * all of that to:
 *   - this file (a thin fetch-by-slug loader)
 *   - listings.json (single ~1.8MB module, eagerly needed by HomePage —
 *     architect classified it as not part of the O(N) blowup)
 *   - data-manifest.json (single small module mapping slug -> sha8 hashes for
 *     cache-busting; the manifest IS bundled with content hashing so any
 *     proof change busts the importing chunk)
 * All per-proof meta/annotations/source now live under public/data/proofs/<slug>/
 * (gitignored, build-generated) and are fetched at runtime.
 */

import listingsData from './listings.json'
import dataManifest from './data-manifest.json'
import type {
  Annotation,
  CrossReference,
  ProofData,
  ProofListing,
  ProofMeta,
  ProofOverview,
  ProofConclusion,
  ProofReference,
  ProofSection,
} from '@/types/proof'

// Lightweight listings for HomePage — does not pull in proof data
export const listings: ProofListing[] = listingsData as ProofListing[]

interface ManifestEntry {
  meta: string
  ann: string
  src: string
}

const DATA_MANIFEST: Record<string, ManifestEntry> = dataManifest as Record<
  string,
  ManifestEntry
>

/**
 * Shape of meta.json as written by the gallery. Fields are duplicated from
 * the per-proof `meta` plus a few top-level fields the shim files used to
 * project onto a `Proof` object.
 */
interface RawMeta {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections?: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
  references?: ProofReference[]
}

/**
 * Normalize annotations: convert legacy {lineNumber} format to {range}, drop
 * annotations with no positional info. Ported from the previous getProofAsync
 * implementation (lines ~99-111 of the pre-phase-2 file).
 */
function normalizeAnnotations(annotations: Annotation[]): Annotation[] {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  return (annotations as any[]).filter((ann: any) => {
    if (ann.range) return true
    const line = ann.lineNumber ?? ann.line
    if (line != null) {
      ann.range = { startLine: line, endLine: line }
      return true
    }
    return false
  }) as Annotation[]
}

/**
 * Asynchronously load proof data for a given slug.
 *
 * Public signature preserved from phase 1: `(slug) => Promise<ProofData | undefined>`.
 * The only real consumer is `src/pages/ProofPage.tsx`; no change needed there.
 *
 * The loader uses the in-graph data-manifest to know (a) which slugs exist and
 * (b) the sha8 cache-buster hashes for each file. Fetches are issued in
 * parallel and any failure (network, 404) returns undefined rather than
 * throwing, matching the previous contract.
 */
export async function getProofAsync(slug: string): Promise<ProofData | undefined> {
  const v = DATA_MANIFEST[slug]
  if (!v) return undefined

  try {
    const [metaResp, annResp] = await Promise.all([
      fetch(`/data/proofs/${slug}/meta.json?v=${v.meta}`),
      fetch(`/data/proofs/${slug}/annotations.json?v=${v.ann}`),
    ])
    if (!metaResp.ok) return undefined

    const meta = (await metaResp.json()) as RawMeta
    // annotations.json is optional — some proofs have none; treat a missing or
    // failed fetch as an empty list rather than failing the whole load.
    let rawAnnotations: Annotation[] = []
    if (annResp.ok) {
      try {
        rawAnnotations = (await annResp.json()) as Annotation[]
      } catch {
        rawAnnotations = []
      }
    }

    const proofData: ProofData = {
      proof: {
        id: meta.id,
        title: meta.title,
        slug: meta.slug,
        description: meta.description,
        meta: meta.meta,
        sections: meta.sections ?? [],
        overview: meta.overview,
        conclusion: meta.conclusion,
        crossReferences: meta.crossReferences,
        references: meta.references,
        source: '',
      },
      annotations: normalizeAnnotations(rawAnnotations),
    }

    // Fetch the Lean source. The previous (phase-1) implementation pre-fetched
    // this inside getProofAsync so ProofPage didn't need to change — we
    // preserve that contract here. Failures leave `source` empty rather than
    // failing the whole proof load.
    try {
      const srcResp = await fetch(`/data/proofs/${slug}/source.lean?v=${v.src}`)
      if (srcResp.ok) proofData.proof.source = await srcResp.text()
    } catch {
      /* leave source empty on failure */
    }

    return proofData
  } catch (e) {
    console.error(`Failed to load proof: ${slug}`, e)
    return undefined
  }
}
