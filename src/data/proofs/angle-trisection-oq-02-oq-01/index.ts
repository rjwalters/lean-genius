import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/AngleTrisectionOQ02OQ01.lean?raw'

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

export const angleTrisectionOQ02OQ01Proof: Proof = {
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

export const angleTrisectionOQ02OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const angleTrisectionOQ02OQ01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const angleTrisectionOQ02OQ01Data: ProofData = {
  proof: angleTrisectionOQ02OQ01Proof,
  annotations: angleTrisectionOQ02OQ01Annotations,
  tacticStates: angleTrisectionOQ02OQ01TacticStates,
}
