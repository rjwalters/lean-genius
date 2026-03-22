import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BallotProblemOQ03OQ02.lean?raw'

const meta = metaJson as unknown as {
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

export const ballotProblemOq03Oq02Data: ProofData = {
  proof: ballotProblemOq03Oq02Proof,
  annotations: ballotProblemOq03Oq02Annotations,
}

export default ballotProblemOq03Oq02Data
