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

const leanSource = () => import('../../../../proofs/Proofs/CantorDiagonalizationOQ04OQ01.lean?raw')

export const cantorDiagonalizationOq04Oq01Proof: Proof = {
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

export const cantorDiagonalizationOq04Oq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const cantorDiagonalizationOq04Oq01Data: ProofData = {
  proof: cantorDiagonalizationOq04Oq01Proof,
  annotations: cantorDiagonalizationOq04Oq01Annotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default cantorDiagonalizationOq04Oq01Data
