import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/Erdos1010OQ02Problem.lean?raw'

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

export const erdos1010Oq02Proof: Proof = {
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

export const erdos1010Oq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const erdos1010Oq02TacticStates: never[] = []

export const erdos1010Oq02Data: ProofData = {
  proof: erdos1010Oq02Proof,
  annotations: erdos1010Oq02Annotations,
  tacticStates: erdos1010Oq02TacticStates,
}
