import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/BallotProblemOQ03OQ02.lean?raw'

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

export const ballotProblemOq03Oq02Proof: Proof = {
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

export const ballotProblemOq03Oq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const ballotProblemOq03Oq02TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const ballotProblemOq03Oq02Data: ProofData = {
  proof: ballotProblemOq03Oq02Proof,
  annotations: ballotProblemOq03Oq02Annotations,
  tacticStates: ballotProblemOq03Oq02TacticStates,
}
