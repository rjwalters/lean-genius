import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/PicksTheoremOQ03CrossPoly.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
}

export const picksTheoremOQ03CrossPolyProof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const picksTheoremOQ03CrossPolyAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const picksTheoremOQ03CrossPolyData: ProofData = {
  proof: picksTheoremOQ03CrossPolyProof,
  annotations: picksTheoremOQ03CrossPolyAnnotations,
}

export default picksTheoremOQ03CrossPolyData
