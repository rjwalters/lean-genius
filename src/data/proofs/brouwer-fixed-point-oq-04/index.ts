import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/BrouwerFixedPointOQ04.lean?raw'

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

export const brouwerFixedPointOQ04Proof: Proof = {
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

export const brouwerFixedPointOQ04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const brouwerFixedPointOQ04TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const brouwerFixedPointOQ04Data: ProofData = {
  proof: brouwerFixedPointOQ04Proof,
  annotations: brouwerFixedPointOQ04Annotations,
  tacticStates: brouwerFixedPointOQ04TacticStates,
}
