import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LawsOfLargeNumbersOQ04OQ03.lean?raw'

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

export const lawsOfLargeNumbersOQ04OQ03Proof: Proof = {
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

export const lawsOfLargeNumbersOQ04OQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const lawsOfLargeNumbersOQ04OQ03Data: ProofData = {
  proof: lawsOfLargeNumbersOQ04OQ03Proof,
  annotations: lawsOfLargeNumbersOQ04OQ03Annotations,
}

export default lawsOfLargeNumbersOQ04OQ03Data
