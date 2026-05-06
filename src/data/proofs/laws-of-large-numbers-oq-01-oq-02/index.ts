import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/LawsOfLargeNumbersOQ01OQ02.lean?raw'

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

export const lawsOfLargeNumbersOQ01OQ02Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  overview: meta.overview,
  source: sourceRaw,
}

const annotations = annotationsJson as unknown as { annotations: Annotation[] }

export const lawsOfLargeNumbersOQ01OQ02Data: ProofData = {
  proof: lawsOfLargeNumbersOQ01OQ02Proof,
  annotations: annotations.annotations,
}

export default lawsOfLargeNumbersOQ01OQ02Data
