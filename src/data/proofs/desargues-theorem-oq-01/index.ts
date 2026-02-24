import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, TacticState } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import tacticStatesJson from './tacticStates.json'
import sourceRaw from '../../../../proofs/Proofs/DesarguesTheoremOQ01.lean?raw'

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

export const desarguesTheoremOQ01Proof: Proof = {
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

export const desarguesTheoremOQ01Annotations: Annotation[] = annotationsJson as Annotation[]
export const desarguesTheoremOQ01TacticStates: TacticState[] = tacticStatesJson as TacticState[]

export const desarguesTheoremOQ01Data: ProofData = {
  proof: desarguesTheoremOQ01Proof,
  annotations: desarguesTheoremOQ01Annotations,
  tacticStates: desarguesTheoremOQ01TacticStates,
}
