import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

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

export const divisibilityTruncationGeneralOQ01Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const divisibilityTruncationGeneralOQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const divisibilityTruncationGeneralOQ01TacticStates: TacticState[] = []

export const divisibilityTruncationGeneralOQ01Data: ProofData = {
  proof: divisibilityTruncationGeneralOQ01Proof,
  annotations: divisibilityTruncationGeneralOQ01Annotations,
  tacticStates: divisibilityTruncationGeneralOQ01TacticStates,
}
