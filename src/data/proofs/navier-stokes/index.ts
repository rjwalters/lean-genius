import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, ProofVersionInfo, VersionHistoryEntry, VersionContent } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/NavierStokes.lean?raw'
import v1Json from './versions/v1.json'
import v2Json from './versions/v2.json'

// Version content mapping
// Note: v1 doesn't have objection field, v2 does
const v1 = v1Json as { description: string; overview: ProofOverview; conclusion: ProofConclusion }
const v2 = v2Json as { description: string; overview: ProofOverview; conclusion: ProofConclusion; objection?: { verdict: string; summary: string; coreIssue?: string } }

const versionContent: Record<string, VersionContent> = {
  v1: {
    description: v1.description,
    overview: v1.overview,
    conclusion: v1.conclusion,
  },
  v2: {
    description: v2.description,
    overview: v2.overview,
    conclusion: v2.conclusion,
    objection: v2.objection ? {
      verdict: v2.objection.verdict,
      summary: v2.objection.summary,
      coreIssue: v2.objection.coreIssue,
    } : undefined,
  },
}

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

// Build version info if available, attaching content to each version
const versionInfo: ProofVersionInfo | undefined = meta.currentVersion && meta.versionHistory
  ? {
      currentVersion: meta.currentVersion,
      versionHistory: meta.versionHistory.map(entry => ({
        ...entry,
        content: versionContent[entry.version],
      })),
    }
  : undefined

export const navierStokesData: ProofData = {
  proof: navierStokesProof,
  annotations: navierStokesAnnotations,
  versionInfo,
}
