import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/GeometricSeriesOQ02OQ03OQ01OQ03.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
  crossReferences?: CrossReference[]
}

export const geometricSeriesOq02Oq03Oq01Oq03Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const geometricSeriesOq02Oq03Oq01Oq03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const geometricSeriesOq02Oq03Oq01Oq03Data: ProofData = {
  proof: geometricSeriesOq02Oq03Oq01Oq03Proof,
  annotations: geometricSeriesOq02Oq03Oq01Oq03Annotations,
}
