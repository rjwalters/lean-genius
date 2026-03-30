import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/ContinuumHypothesisOQ01OQ01.lean?raw'

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

export const continuumHypothesisOQ01OQ01Proof: Proof = {
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

export const continuumHypothesisOQ01OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const continuumHypothesisOQ01OQ01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const continuumHypothesisOQ01OQ01Data: ProofData = {
  proof: continuumHypothesisOQ01OQ01Proof,
  annotations: continuumHypothesisOQ01OQ01Annotations,
  tacticStates: continuumHypothesisOQ01OQ01TacticStates,
}
