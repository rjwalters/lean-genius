import type { Annotation, ProofData, ProofMeta, ProofSection, ProofOverview, ProofConclusion, CrossReference } from '@/types/proof'
import metaJson from './meta.json'
import annotationsJson from './annotations.json'
import sourceRaw from '../../../../proofs/Proofs/GreensTheoremOQ01OQ02.lean?raw'

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

const annotations = annotationsJson as unknown as Annotation[]

export const proof: ProofData = {
  proof: {
    id: meta.id,
    title: meta.title,
    slug: meta.slug,
    description: meta.description,
    meta: meta.meta,
    sections: meta.sections ?? [],
    source: sourceRaw,
    overview: meta.overview,
    conclusion: meta.conclusion,
    crossReferences: meta.crossReferences,
  },
  annotations,
}

export default proof
