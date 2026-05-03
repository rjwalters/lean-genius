import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsData from './annotations.json'

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

const annotations: Annotation[] = annotationsData as unknown as Annotation[]

export const infinitudePrimes4k3OQ03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections ?? [],
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const infinitudePrimes4k3OQ03Annotations = annotations

export const infinitudePrimes4k3OQ03Data: ProofData = {
  proof: infinitudePrimes4k3OQ03Proof,
  annotations,
}

export async function getProofSource(): Promise<string> {
  const src = await import('/proofs/Proofs/InfinitudePrimes4k3OQ03.lean?raw')
  return src.default
}

export default infinitudePrimes4k3OQ03Data
