import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/InfinitudePrimes4k3OQ03.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const infinitudePrimes4k3Oq03Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const infinitudePrimes4k3Oq03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const infinitudePrimes4k3Oq03Data: ProofData = { proof: infinitudePrimes4k3Oq03Proof, annotations: infinitudePrimes4k3Oq03Annotations, tacticStates: [] }
