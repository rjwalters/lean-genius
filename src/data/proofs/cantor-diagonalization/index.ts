import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/CantorDiagonalization.lean?raw'

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

export const cantorDiagonalizationProof: Proof = {
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

export const cantorDiagonalizationAnnotations: Annotation[] = annotationsJson as Annotation[]
export const cantorDiagonalizationTacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const cantorDiagonalizationData: ProofData = {
  proof: cantorDiagonalizationProof,
  annotations: cantorDiagonalizationAnnotations,
  tacticStates: cantorDiagonalizationTacticStates,
}
