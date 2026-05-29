import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'

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

export const abelRuffiniOq04Proof: Proof = {
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

export const abelRuffiniOq04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const abelRuffiniOq04TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const abelRuffiniOq04Data: ProofData = {
  proof: abelRuffiniOq04Proof,
  annotations: abelRuffiniOq04Annotations,
  tacticStates: abelRuffiniOq04TacticStates,
}
