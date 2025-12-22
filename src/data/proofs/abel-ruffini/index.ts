import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from './source.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const abelRuffiniProof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const abelRuffiniAnnotations: Annotation[] = annotationsJson as Annotation[]
export const abelRuffiniTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const abelRuffiniData: ProofData = {
  proof: abelRuffiniProof,
  annotations: abelRuffiniAnnotations,
  tacticStates: abelRuffiniTacticStates,
}
