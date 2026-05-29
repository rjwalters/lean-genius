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

export const harmonicDivergenceOQ04Proof: Proof = {
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

export const harmonicDivergenceOQ04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const harmonicDivergenceOQ04TacticStates: TacticState[] = []

export const harmonicDivergenceOQ04Data: ProofData = {
  proof: harmonicDivergenceOQ04Proof,
  annotations: harmonicDivergenceOQ04Annotations,
  tacticStates: harmonicDivergenceOQ04TacticStates,
}
