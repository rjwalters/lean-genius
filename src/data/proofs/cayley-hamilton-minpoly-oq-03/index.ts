import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/CayleyHamiltonMinpolyOQ03.lean?raw'

const meta = metaJson as unknown as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  sections: ProofSection[]
  overview?: ProofOverview
  conclusion?: ProofConclusion
}

export const cayleyHamiltonMinpolyOQ03Proof: Proof = {
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

export const cayleyHamiltonMinpolyOQ03Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const cayleyHamiltonMinpolyOQ03Data: ProofData = {
  proof: cayleyHamiltonMinpolyOQ03Proof,
  annotations: cayleyHamiltonMinpolyOQ03Annotations,
}

export default cayleyHamiltonMinpolyOQ03Data
