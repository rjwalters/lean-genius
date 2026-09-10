# Forced F-neighbour edge when C and F share no singleton

In this branch each fi has exactly one heavy neighbour F={2,4}; BC=J therefore forces one singleton neighbour of each colour0,1,3. For each fixed colour, the five fi must use distinct target singleton vertices: a repeated target and F would have two common neighbours, contradicting C4-freeness.

There are exactly five colour1 singletons and five colour3 singletons. Both target classes are saturated. Since f1 and f3 belong to those classes, each must be adjacent to some other fj. The induced graph on N(F) has maximum degree1: a two-edge path fj-fi-fk, together with F, would be C4. An internal edge can only join vertices of colours0,1,3, because colours2and4 are already covered by F and cannot occur in any fi singleton neighbourhood. The only matching on {f0,f1,f3} covering both f1 and f3 is the edge f1-f3. No other internal edge exists.

Consequently f0 is not a target of any colour0 request. There are six colour0 singletons, and the five requests use all five other targets. This is a necessary branch constraint, not a contradiction or exclusion. The two branches sharing C/F at f1or f2 remain separate. The tiny eight-subset audit checks the final matching implication; the saturation argument is mathematical, not graph enumeration. Independent review pending.
