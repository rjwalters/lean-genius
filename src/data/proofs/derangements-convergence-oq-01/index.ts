import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/DerangementsConvergenceOQ01.lean?raw'
const meta = metaJson as unknown as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion; crossReferences?: CrossReference[] }
export const derangementsConvergenceOq01Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections ?? [], source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion, crossReferences: meta.crossReferences }
export const derangementsConvergenceOq01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const derangementsConvergenceOq01Data: ProofData = { proof: derangementsConvergenceOq01Proof, annotations: derangementsConvergenceOq01Annotations, tacticStates: [] }
