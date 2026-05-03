import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/AbelRuffiniOQ09.lean?raw'

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

export const abelRuffiniOq09Proof: Proof = {
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

export const abelRuffiniOq09Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const abelRuffiniOq09TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const abelRuffiniOq09Data: ProofData = {
  proof: abelRuffiniOq09Proof,
  annotations: abelRuffiniOq09Annotations,
  tacticStates: abelRuffiniOq09TacticStates,
}
