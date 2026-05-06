import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/GreensTheoremOQ02OQ04.lean?raw'
const meta = metaJson as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const greensTheoremOQ02OQ04Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections, source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const greensTheoremOQ02OQ04Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const greensTheoremOQ02OQ04Data: ProofData = { proof: greensTheoremOQ02OQ04Proof, annotations: greensTheoremOQ02OQ04Annotations }
