import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/GeometricSeriesOQ02OQ05.lean?raw'

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

export const geometricSeriesOq02Oq05Proof: Proof = {
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

export const geometricSeriesOq02Oq05Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const geometricSeriesOq02Oq05TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const geometricSeriesOq02Oq05Data: ProofData = {
  proof: geometricSeriesOq02Oq05Proof,
  annotations: geometricSeriesOq02Oq05Annotations,
  tacticStates: geometricSeriesOq02Oq05TacticStates,
}
