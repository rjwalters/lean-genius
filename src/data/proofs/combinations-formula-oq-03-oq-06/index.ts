import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/CombinationsFormulaOQ03OQ06.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const combinationsFormulaOQ03OQ06Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const combinationsFormulaOQ03OQ06Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const combinationsFormulaOQ03OQ06Data: ProofData = { proof: combinationsFormulaOQ03OQ06Proof, annotations: combinationsFormulaOQ03OQ06Annotations, tacticStates: [] }
