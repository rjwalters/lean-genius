import meta from './meta.json'
import annotationsData from './annotations.json'
import type { Annotation, ProofData } from '@/types/proof'

const annotations: Annotation[] = annotationsData as Annotation[]

export const infinitudePrimes4k3OQ03Data: ProofData = {
  proof: {
    id: meta.id,
    title: meta.title,
    slug: meta.slug,
    description: meta.description,
    meta: meta.meta,
    sections: meta.sections,
    overview: meta.overview,
    conclusion: meta.conclusion,
    crossReferences: meta.crossReferences,
    source: '',
  },
  annotations,
}

export const infinitudePrimes4k3OQ03Proof = infinitudePrimes4k3OQ03Data.proof
export const infinitudePrimes4k3OQ03Annotations = annotations

export async function getProofSource(): Promise<string> {
  const src = await import(
    '/proofs/Proofs/InfinitudePrimes4k3OQ03.lean?raw'
  )
  return src.default
}

export default infinitudePrimes4k3OQ03Data
