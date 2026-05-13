import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
}

const leanSource = () => import('../../../../proofs/Proofs/Erdos114OQ04Problem.lean?raw')

export const erdos114Oq04Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const erdos114Oq04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const erdos114Oq04Data: ProofData = {
  proof: erdos114Oq04Proof,
  annotations: erdos114Oq04Annotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default erdos114Oq04Data
