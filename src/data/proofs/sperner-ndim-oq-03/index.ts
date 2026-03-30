import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/SpernerNDimOQ03.lean?raw'

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

export const spernerNdimOq03Proof: Proof = {
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

export const spernerNdimOq03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const spernerNdimOq03TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const spernerNdimOq03Data: ProofData = {
  proof: spernerNdimOq03Proof,
  annotations: spernerNdimOq03Annotations,
  tacticStates: spernerNdimOq03TacticStates,
}
