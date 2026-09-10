import Zero26Structure
import Zero26Shard0
import Zero26Shard1
import Zero26Shard2
import Zero26Shard3
import Zero26Shard4
import Zero26Shard5
import Zero26Shard6
import Zero26Shard7
import Zero26Shard8
import Zero26Shard9
import Zero26Shard10
import Zero26Shard11
import Zero26Shard12
import Zero26Shard13
import Zero26Shard14
import Zero26Shard15
import Zero26Shard16
import Zero26Shard17
import Zero26Shard18
import Zero26Shard19
import Zero26Shard20
import Zero26Shard21
import Zero26Shard22
import Zero26Shard23
import Zero26Shard24
import Zero26Shard25
import Zero26Shard26
import Zero26Shard27
import Zero26Shard28
import Zero26Shard29
import Zero26Shard30
import Zero26Shard31
import Zero26Shard32
import Zero26Shard33
import Zero26Shard34
import Zero26Shard35
namespace Zero26Assembly
open Erdos85 Zero26
def pairs : List (Fin 8 × Fin 8) := [(2,3),(4,5),(6,7)]
def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 0) := .branch [.branch [Zero26Shard0.cert,Zero26Shard1.cert,Zero26Shard2.cert,Zero26Shard3.cert,Zero26Shard4.cert,Zero26Shard5.cert,Zero26Shard6.cert,Zero26Shard7.cert,Zero26Shard8.cert,Zero26Shard9.cert,Zero26Shard10.cert,Zero26Shard11.cert,Zero26Shard12.cert,Zero26Shard13.cert,Zero26Shard14.cert,Zero26Shard15.cert,Zero26Shard16.cert,Zero26Shard17.cert,Zero26Shard18.cert,Zero26Shard19.cert,Zero26Shard20.cert,Zero26Shard21.cert,Zero26Shard22.cert,Zero26Shard23.cert,Zero26Shard24.cert,Zero26Shard25.cert,Zero26Shard26.cert,Zero26Shard27.cert,Zero26Shard28.cert,Zero26Shard29.cert,Zero26Shard30.cert,Zero26Shard31.cert,Zero26Shard32.cert,Zero26Shard33.cert,Zero26Shard34.cert,Zero26Shard35.cert]]
theorem checked : threeHighColumnCoverCheck U R pairs threeHighColumnScore domains table cert = true := by
  exact Zero26Structure.assemble
    Zero26Shard0.cert Zero26Shard1.cert Zero26Shard2.cert Zero26Shard3.cert Zero26Shard4.cert Zero26Shard5.cert Zero26Shard6.cert Zero26Shard7.cert Zero26Shard8.cert Zero26Shard9.cert Zero26Shard10.cert Zero26Shard11.cert Zero26Shard12.cert Zero26Shard13.cert Zero26Shard14.cert Zero26Shard15.cert Zero26Shard16.cert Zero26Shard17.cert Zero26Shard18.cert Zero26Shard19.cert Zero26Shard20.cert Zero26Shard21.cert Zero26Shard22.cert Zero26Shard23.cert Zero26Shard24.cert Zero26Shard25.cert Zero26Shard26.cert Zero26Shard27.cert Zero26Shard28.cert Zero26Shard29.cert Zero26Shard30.cert Zero26Shard31.cert Zero26Shard32.cert Zero26Shard33.cert Zero26Shard34.cert Zero26Shard35.cert
    Zero26Shard0.checked Zero26Shard1.checked Zero26Shard2.checked Zero26Shard3.checked Zero26Shard4.checked Zero26Shard5.checked Zero26Shard6.checked Zero26Shard7.checked Zero26Shard8.checked Zero26Shard9.checked Zero26Shard10.checked Zero26Shard11.checked Zero26Shard12.checked Zero26Shard13.checked Zero26Shard14.checked Zero26Shard15.checked Zero26Shard16.checked Zero26Shard17.checked Zero26Shard18.checked Zero26Shard19.checked Zero26Shard20.checked Zero26Shard21.checked Zero26Shard22.checked Zero26Shard23.checked Zero26Shard24.checked Zero26Shard25.checked Zero26Shard26.checked Zero26Shard27.checked Zero26Shard28.checked Zero26Shard29.checked Zero26Shard30.checked Zero26Shard31.checked Zero26Shard32.checked Zero26Shard33.checked Zero26Shard34.checked Zero26Shard35.checked
end Zero26Assembly
#print axioms Zero26Assembly.checked
