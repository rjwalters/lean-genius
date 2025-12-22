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

export const russell1Plus1Proof: Proof = {
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

export const russell1Plus1Annotations: Annotation[] = annotationsJson as Annotation[]
export const russell1Plus1TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const russell1Plus1Data: ProofData = {
  proof: russell1Plus1Proof,
  annotations: russell1Plus1Annotations,
  tacticStates: russell1Plus1TacticStates,
}
