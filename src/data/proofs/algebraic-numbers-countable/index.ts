import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, ProofReference } from '@/types/proof'
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
  references?: ProofReference[]
}

export const algebraicNumbersCountableProof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
  references: meta.references,
}

export const algebraicNumbersCountableAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const algebraicNumbersCountableData: ProofData = {
  proof: algebraicNumbersCountableProof,
  annotations: algebraicNumbersCountableAnnotations,
  tacticStates: [],
}
