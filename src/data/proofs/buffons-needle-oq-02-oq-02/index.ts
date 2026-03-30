import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BuffonsNeedleOQ02OQ02.lean?raw'

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

export const buffonsNeedleOQ02OQ02Proof: Proof = {
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

export const buffonsNeedleOQ02OQ02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const buffonsNeedleOQ02OQ02TacticStates: TacticState[] = [] as TacticState[]

export const buffonsNeedleOQ02OQ02Data: ProofData = {
  proof: buffonsNeedleOQ02OQ02Proof,
  annotations: buffonsNeedleOQ02OQ02Annotations,
  tacticStates: buffonsNeedleOQ02OQ02TacticStates,
}
