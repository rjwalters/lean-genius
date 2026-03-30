import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/Hilbert15SchubertCalculusOQ01.lean?raw'

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

export const hilbert15OQ01Proof: Proof = {
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

export const hilbert15OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const hilbert15OQ01TacticStates: TacticState[] = [] as TacticState[]

export const hilbert15OQ01Data: ProofData = {
  proof: hilbert15OQ01Proof,
  annotations: hilbert15OQ01Annotations,
  tacticStates: hilbert15OQ01TacticStates,
}
