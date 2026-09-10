import Zero32Structure
import Zero32Shard0
import Zero32Shard1
import Zero32Shard2
import Zero32Shard3
import Zero32Shard4
import Zero32Shard5
import Zero32Shard6
import Zero32Shard7
import Zero32Shard8
import Zero32Shard9
import Zero32Shard10
import Zero32Shard11
import Zero32Shard12
import Zero32Shard13
import Zero32Shard14
import Zero32Shard15
import Zero32Shard16
import Zero32Shard17
import Zero32Shard18
import Zero32Shard19
import Zero32Shard20
import Zero32Shard21
import Zero32Shard22
import Zero32Shard23
import Zero32Shard24
import Zero32Shard25
import Zero32Shard26
import Zero32Shard27
import Zero32Shard28
import Zero32Shard29
import Zero32Shard30
import Zero32Shard31
import Zero32Shard32
import Zero32Shard33
import Zero32Shard34
import Zero32Shard35
namespace Zero32Assembly
open Erdos85 Zero32
def pairs : List (Fin 8 × Fin 8) := [(2,3),(4,5),(6,7)]
def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 0) := .branch [.branch [Zero32Shard0.cert,Zero32Shard1.cert,Zero32Shard2.cert,Zero32Shard3.cert,Zero32Shard4.cert,Zero32Shard5.cert,Zero32Shard6.cert,Zero32Shard7.cert,Zero32Shard8.cert,Zero32Shard9.cert,Zero32Shard10.cert,Zero32Shard11.cert,Zero32Shard12.cert,Zero32Shard13.cert,Zero32Shard14.cert,Zero32Shard15.cert,Zero32Shard16.cert,Zero32Shard17.cert,Zero32Shard18.cert,Zero32Shard19.cert,Zero32Shard20.cert,Zero32Shard21.cert,Zero32Shard22.cert,Zero32Shard23.cert,Zero32Shard24.cert,Zero32Shard25.cert,Zero32Shard26.cert,Zero32Shard27.cert,Zero32Shard28.cert,Zero32Shard29.cert,Zero32Shard30.cert,Zero32Shard31.cert,Zero32Shard32.cert,Zero32Shard33.cert,Zero32Shard34.cert,Zero32Shard35.cert]]
theorem checked : threeHighColumnCoverCheck U R pairs threeHighColumnScore domains table cert = true := by
  exact Zero32Structure.assemble
    Zero32Shard0.cert Zero32Shard1.cert Zero32Shard2.cert Zero32Shard3.cert Zero32Shard4.cert Zero32Shard5.cert Zero32Shard6.cert Zero32Shard7.cert Zero32Shard8.cert Zero32Shard9.cert Zero32Shard10.cert Zero32Shard11.cert Zero32Shard12.cert Zero32Shard13.cert Zero32Shard14.cert Zero32Shard15.cert Zero32Shard16.cert Zero32Shard17.cert Zero32Shard18.cert Zero32Shard19.cert Zero32Shard20.cert Zero32Shard21.cert Zero32Shard22.cert Zero32Shard23.cert Zero32Shard24.cert Zero32Shard25.cert Zero32Shard26.cert Zero32Shard27.cert Zero32Shard28.cert Zero32Shard29.cert Zero32Shard30.cert Zero32Shard31.cert Zero32Shard32.cert Zero32Shard33.cert Zero32Shard34.cert Zero32Shard35.cert
    Zero32Shard0.checked Zero32Shard1.checked Zero32Shard2.checked Zero32Shard3.checked Zero32Shard4.checked Zero32Shard5.checked Zero32Shard6.checked Zero32Shard7.checked Zero32Shard8.checked Zero32Shard9.checked Zero32Shard10.checked Zero32Shard11.checked Zero32Shard12.checked Zero32Shard13.checked Zero32Shard14.checked Zero32Shard15.checked Zero32Shard16.checked Zero32Shard17.checked Zero32Shard18.checked Zero32Shard19.checked Zero32Shard20.checked Zero32Shard21.checked Zero32Shard22.checked Zero32Shard23.checked Zero32Shard24.checked Zero32Shard25.checked Zero32Shard26.checked Zero32Shard27.checked Zero32Shard28.checked Zero32Shard29.checked Zero32Shard30.checked Zero32Shard31.checked Zero32Shard32.checked Zero32Shard33.checked Zero32Shard34.checked Zero32Shard35.checked
end Zero32Assembly
#print axioms Zero32Assembly.checked
