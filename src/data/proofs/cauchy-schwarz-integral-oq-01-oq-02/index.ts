import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/CauchySchwarzIntegralOQ01OQ02.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const cauchySchwarzIntegralOQ01OQ02Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
  overview: meta.overview,
  conclusion: meta.conclusion,
}

export const cauchySchwarzIntegralOQ01OQ02Annotations: Annotation[] = annotationsJson as Annotation[]

export const cauchySchwarzIntegralOQ01OQ02Data: ProofData = {
  proof: cauchySchwarzIntegralOQ01OQ02Proof,
  annotations: cauchySchwarzIntegralOQ01OQ02Annotations,
}
