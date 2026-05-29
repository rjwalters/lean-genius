import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const dissectionOfCubesOQ04Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: '', overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const dissectionOfCubesOQ04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const dissectionOfCubesOQ04Data: ProofData = { proof: dissectionOfCubesOQ04Proof, annotations: dissectionOfCubesOQ04Annotations, tacticStates: [] }
