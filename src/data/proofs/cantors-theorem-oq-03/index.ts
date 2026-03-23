import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/CantorsTheoremOQ03.lean?raw'

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

export const cantorsTheoremOq03Proof: Proof = {
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

export const cantorsTheoremOq03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const cantorsTheoremOq03TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const cantorsTheoremOq03Data: ProofData = {
  proof: cantorsTheoremOq03Proof,
  annotations: cantorsTheoremOq03Annotations,
  tacticStates: cantorsTheoremOq03TacticStates,
}
