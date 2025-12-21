import type { Proof, Annotation, ProofData, ProofMeta, ProofSection } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from './source.lean?raw'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
}

export const navierStokesProof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: sourceRaw,
}

export const navierStokesAnnotations: Annotation[] = annotationsJson as Annotation[]

export const navierStokesData: ProofData = {
  proof: navierStokesProof,
  annotations: navierStokesAnnotations,
}
