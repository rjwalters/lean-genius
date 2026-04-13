import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/CantorDiagonalizationOQ03OQ01Incomplete01.lean?raw'

const meta = metaJson as {
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

export const cantorDiagonalizationOq03Oq01Incomplete01Proof: Proof = {
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

export const cantorDiagonalizationOq03Oq01Incomplete01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const cantorDiagonalizationOq03Oq01Incomplete01Data: ProofData = {
  proof: cantorDiagonalizationOq03Oq01Incomplete01Proof,
  annotations: cantorDiagonalizationOq03Oq01Incomplete01Annotations,
}

export default cantorDiagonalizationOq03Oq01Incomplete01Data
