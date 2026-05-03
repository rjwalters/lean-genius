import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/CantorDiagonalizationOQ01OQ02.lean?raw'

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

export const cantorDiagonalizationOQ01OQ02Proof: Proof = {
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

export const cantorDiagonalizationOQ01OQ02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const cantorDiagonalizationOQ01OQ02TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const cantorDiagonalizationOQ01OQ02Data: ProofData = {
  proof: cantorDiagonalizationOQ01OQ02Proof,
  annotations: cantorDiagonalizationOQ01OQ02Annotations,
  tacticStates: cantorDiagonalizationOQ01OQ02TacticStates,
}
