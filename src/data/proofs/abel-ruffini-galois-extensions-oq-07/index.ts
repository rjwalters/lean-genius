import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const abelRuffiniGaloisExtensionsOQ07Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const abelRuffiniGaloisExtensionsOQ07Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const abelRuffiniGaloisExtensionsOQ07Data: ProofData = { proof: abelRuffiniGaloisExtensionsOQ07Proof, annotations: abelRuffiniGaloisExtensionsOQ07Annotations, tacticStates: [] }
