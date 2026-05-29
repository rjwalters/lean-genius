import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'

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

export const ballotProblemOq02Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const ballotProblemOq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const ballotProblemOq02TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const ballotProblemOq02Data: ProofData = {
  proof: ballotProblemOq02Proof,
  annotations: ballotProblemOq02Annotations,
  tacticStates: ballotProblemOq02TacticStates,
}
