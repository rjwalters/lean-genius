import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/Sqrt2IrrationalFromAxioms.lean?raw'

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

export const sqrt2FromAxiomsProof: Proof = {
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

export const sqrt2FromAxiomsAnnotations: Annotation[] = annotationsJson as Annotation[]
export const sqrt2FromAxiomsTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const sqrt2FromAxiomsData: ProofData = {
  proof: sqrt2FromAxiomsProof,
  annotations: sqrt2FromAxiomsAnnotations,
  tacticStates: sqrt2FromAxiomsTacticStates,
}
