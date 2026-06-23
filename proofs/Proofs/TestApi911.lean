-- Test API availability for Erdos 911

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

-- Check SimpleGraph basics
#check SimpleGraph
#check SimpleGraph.edgeFinset
#check SimpleGraph.Subgraph
#check SimpleGraph.Embedding

-- Check Fintype
#check Fintype.card

-- Check filter concepts for limits
#check Filter.Tendsto
#check Filter.atTop
