import type { Proof, Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'

const meta = metaJson as {
  id: string
  title: string
  slug: string
  description: string
  meta: ProofMeta
  overview: ProofOverview
  conclusion: ProofConclusion
  sections: ProofSection[]
  crossReferences: CrossReference[]
  sorries: number
  leanFile: Record<string, unknown>
}

const annotations = annotationsJson as Annotation[]

export const proof: ProofData = {
  meta: {
    id: meta.id,
    title: meta.title,
    slug: meta.slug,
    description: meta.description,
    meta: meta.meta,
    overview: meta.overview,
    conclusion: meta.conclusion,
    sections: meta.sections,
    crossReferences: meta.crossReferences,
    sorries: meta.sorries,
    leanFile: meta.leanFile,
  },
  annotations,
}

export default proof
