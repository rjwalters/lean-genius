import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LawsOfLargeNumbersOQ01OQ03.lean?raw'

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

export const lawsOfLargeNumbersOQ01OQ03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const lawsOfLargeNumbersOQ01OQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const lawsOfLargeNumbersOQ01OQ03Data: ProofData = {
  proof: lawsOfLargeNumbersOQ01OQ03Proof,
  annotations: lawsOfLargeNumbersOQ01OQ03Annotations,
}

export default lawsOfLargeNumbersOQ01OQ03Data
