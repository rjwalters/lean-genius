import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, ProofVersionInfo, VersionHistoryEntry } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/NavierStokes.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  currentVersion?: string
  versionHistory?: VersionHistoryEntry[]
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const navierStokesProof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const navierStokesAnnotations: Annotation[] = annotationsJson as Annotation[]

// Build version info if available
const versionInfo: ProofVersionInfo | undefined = meta.currentVersion && meta.versionHistory
  ? {
      currentVersion: meta.currentVersion,
      versionHistory: meta.versionHistory,
    }
  : undefined

export const navierStokesData: ProofData = {
  proof: navierStokesProof,
  annotations: navierStokesAnnotations,
  versionInfo,
}
