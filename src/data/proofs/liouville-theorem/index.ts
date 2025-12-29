import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/LiouvilleTheorem.lean?raw'

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

export const liouvilleTheoremProof: Proof = {
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

export const liouvilleTheoremAnnotations: Annotation[] = annotationsJson as Annotation[]
export const liouvilleTheoremTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const liouvilleTheoremData: ProofData = {
  proof: liouvilleTheoremProof,
  annotations: liouvilleTheoremAnnotations,
  tacticStates: liouvilleTheoremTacticStates,
}
