import CoverageAssemblyStructure
import CoverageShard0
import CoverageShard1
import CoverageShard2
import CoverageShard3
import CoverageShard4
import CoverageShard5
import CoverageShard6
import CoverageShard7
import CoverageShard8
import CoverageShard9
import CoverageShard10
import CoverageShard11
import CoverageShard12
import CoverageShard13
import CoverageShard14
import CoverageShard15
import LeafPilot
import CoverageShard17
import CoverageShard18
import CoverageShard19
import CoverageShard20
import CoverageShard21
import CoverageShard22
import CoverageShard23
import CoverageShard24
import CoverageShard25
import CoverageShard26
import CoverageShard27
import CoverageShard28
import CoverageShard29
import CoverageShard30
import LiteralDataPilot
import CoverageShard32
import CoverageShard33
import CoverageShard34
import CoverageShard35
namespace ColumnCoverageAssembly
open Erdos85 ColumnCoverageLiterals
def pairs : List (Fin 8 × Fin 8) := [(2,3),(4,5),(6,7)]
def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 140) := .branch [.branch [CoverageShard0.cert,CoverageShard1.cert,CoverageShard2.cert,CoverageShard3.cert,CoverageShard4.cert,CoverageShard5.cert,CoverageShard6.cert,CoverageShard7.cert,CoverageShard8.cert,CoverageShard9.cert,CoverageShard10.cert,CoverageShard11.cert,CoverageShard12.cert,CoverageShard13.cert,CoverageShard14.cert,CoverageShard15.cert,ColumnCoverageLeafPilot.cert,CoverageShard17.cert,CoverageShard18.cert,CoverageShard19.cert,CoverageShard20.cert,CoverageShard21.cert,CoverageShard22.cert,CoverageShard23.cert,CoverageShard24.cert,CoverageShard25.cert,CoverageShard26.cert,CoverageShard27.cert,CoverageShard28.cert,CoverageShard29.cert,CoverageShard30.cert,ColumnCoverageLiteralPilot.cert,CoverageShard32.cert,CoverageShard33.cert,CoverageShard34.cert,CoverageShard35.cert]]
theorem checked : threeHighColumnCoverCheck U R pairs threeHighColumnScore domains table cert = true := by
  exact ColumnCoverageStructure.assemble
    CoverageShard0.cert CoverageShard1.cert CoverageShard2.cert CoverageShard3.cert CoverageShard4.cert CoverageShard5.cert CoverageShard6.cert CoverageShard7.cert CoverageShard8.cert CoverageShard9.cert CoverageShard10.cert CoverageShard11.cert CoverageShard12.cert CoverageShard13.cert CoverageShard14.cert CoverageShard15.cert ColumnCoverageLeafPilot.cert CoverageShard17.cert CoverageShard18.cert CoverageShard19.cert CoverageShard20.cert CoverageShard21.cert CoverageShard22.cert CoverageShard23.cert CoverageShard24.cert CoverageShard25.cert CoverageShard26.cert CoverageShard27.cert CoverageShard28.cert CoverageShard29.cert CoverageShard30.cert ColumnCoverageLiteralPilot.cert CoverageShard32.cert CoverageShard33.cert CoverageShard34.cert CoverageShard35.cert
    CoverageShard0.checked CoverageShard1.checked CoverageShard2.checked CoverageShard3.checked CoverageShard4.checked CoverageShard5.checked CoverageShard6.checked CoverageShard7.checked CoverageShard8.checked CoverageShard9.checked CoverageShard10.checked CoverageShard11.checked CoverageShard12.checked CoverageShard13.checked CoverageShard14.checked CoverageShard15.checked ColumnCoverageLeafPilot.checked CoverageShard17.checked CoverageShard18.checked CoverageShard19.checked CoverageShard20.checked CoverageShard21.checked CoverageShard22.checked CoverageShard23.checked CoverageShard24.checked CoverageShard25.checked CoverageShard26.checked CoverageShard27.checked CoverageShard28.checked CoverageShard29.checked CoverageShard30.checked ColumnCoverageLiteralPilot.checked CoverageShard32.checked CoverageShard33.checked CoverageShard34.checked CoverageShard35.checked
end ColumnCoverageAssembly
#print axioms ColumnCoverageAssembly.checked
