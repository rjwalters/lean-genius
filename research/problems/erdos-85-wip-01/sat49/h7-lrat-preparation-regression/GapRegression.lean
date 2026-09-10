import Proofs.Erdos85LratRuntime
import Proofs.Erdos85OrderFortyNineLratCertificateBase
open Std Sat Std.Tactic.BVDecide
open Erdos85
def cnf : CNF Nat := { clauses := #[[(0, true)], [(0, false), (1, true)], [(1, false)]] }
def raw := parseOrderFortyNineLratProof "10 2 0 1 2 0\n11 0 10 3 0\n"
def prepared := (prepareLratProof cnf raw).toOption.getD #[]
def invalid := parseOrderFortyNineLratProof "10 2 0 99 2 0\n11 0 10 3 0\n"
def rejected := (prepareLratProof cnf invalid).toOption.getD #[]
example : LRAT.check raw cnf = false := by native_decide
example : LRAT.check prepared cnf = true := by native_decide
example : LRAT.check rejected cnf = false := by native_decide
#eval (LRAT.check raw cnf, LRAT.check prepared cnf, LRAT.check rejected cnf)
