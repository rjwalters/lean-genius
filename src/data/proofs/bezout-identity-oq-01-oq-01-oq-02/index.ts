import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

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

const leanSource = () => import('../../../../proofs/Proofs/BezoutIdentityOQ01OQ01OQ02.lean?raw')

export const bezoutIdentityOq01Oq01Oq02Proof: Proof = {
  id: meta.id,
  title: meta.title,
  slug: meta.slug,
  description: meta.description,
  meta: meta.meta,
  sections: meta.sections,
  source: '',
  overview: meta.overview,
  conclusion: meta.conclusion,
  crossReferences: meta.crossReferences,
}

export const bezoutIdentityOq01Oq01Oq02Annotations: Annotation[] = annotationsJson as unknown as Annotation[]

export const bezoutIdentityOq01Oq01Oq02Data: ProofData = {
  proof: bezoutIdentityOq01Oq01Oq02Proof,
  annotations: bezoutIdentityOq01Oq01Oq02Annotations,
}

export async function getProofSource(): Promise<string> {
  const module = await leanSource()
  return module.default
}

export default bezoutIdentityOq01Oq01Oq02Data
