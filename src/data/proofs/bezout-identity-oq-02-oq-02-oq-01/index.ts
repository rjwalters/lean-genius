import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/BezoutIdentityOQ02OQ02OQ01.lean?raw'
const meta = metaJson as { id: string; title: string; slug: string; description: string; meta: ProofMeta; sections: ProofSection[]; overview?: ProofOverview; conclusion?: ProofConclusion, CrossReference }
export const bezoutIdentityOQ02OQ02OQ01Proof: Proof = { id: meta.id, title: meta.title, slug: meta.slug, description: meta.description, meta: meta.meta, sections: meta.sections, source: sourceRaw, overview: meta.overview, conclusion: meta.conclusion }
export const bezoutIdentityOQ02OQ02OQ01Annotations: Annotation[] = annotationsJson as unknown as Annotation[]
export const bezoutIdentityOQ02OQ02OQ01Data: ProofData = { proof: bezoutIdentityOQ02OQ02OQ01Proof, annotations: bezoutIdentityOQ02OQ02OQ01Annotations }
