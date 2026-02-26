import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/CantorsTheoremOQ02.lean?raw'

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

export const cantorsTheoremOQ02Proof: Proof = {
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

export const cantorsTheoremOQ02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const cantorsTheoremOQ02TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const cantorsTheoremOQ02Data: ProofData = {
  proof: cantorsTheoremOQ02Proof,
  annotations: cantorsTheoremOQ02Annotations,
  tacticStates: cantorsTheoremOQ02TacticStates,
}
