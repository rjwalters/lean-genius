import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/BallotProblem.lean?raw'

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

export const ballotProblemProof: Proof = {
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

export const ballotProblemAnnotations: Annotation[] = annotationsJson as Annotation[]
export const ballotProblemTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const ballotProblemData: ProofData = {
  proof: ballotProblemProof,
  annotations: ballotProblemAnnotations,
  tacticStates: ballotProblemTacticStates,
}
