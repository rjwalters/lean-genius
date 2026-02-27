import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/BinomialTheoremOQ03.lean?raw'

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

export const binomialTheoremOQ03Proof: Proof = {
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

export const binomialTheoremOQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const binomialTheoremOQ03TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const binomialTheoremOQ03Data: ProofData = {
  proof: binomialTheoremOQ03Proof,
  annotations: binomialTheoremOQ03Annotations,
  tacticStates: binomialTheoremOQ03TacticStates,
}
