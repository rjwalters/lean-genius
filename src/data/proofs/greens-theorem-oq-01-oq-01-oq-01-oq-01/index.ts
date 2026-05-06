import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const greensTheoremOQ01OQ01OQ01OQ01Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const greensTheoremOQ01OQ01OQ01OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const greensTheoremOQ01OQ01OQ01OQ01Data: ProofData = { proof: greensTheoremOQ01OQ01OQ01OQ01Proof, annotations: greensTheoremOQ01OQ01OQ01OQ01Annotations, tacticStates: [] }
export default greensTheoremOQ01OQ01OQ01OQ01Data
