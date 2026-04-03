import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/RamseyR4kExtensions.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const ramseyR4kExtensionsProof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const ramseyR4kExtensionsAnnotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const ramseyR4kExtensionsData: ProofData = { proof: ramseyR4kExtensionsProof, annotations: ramseyR4kExtensionsAnnotations, tacticStates: [] }
