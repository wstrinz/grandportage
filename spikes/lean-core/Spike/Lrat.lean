import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
open Std.Sat Std.Tactic.BVDecide
namespace Spike.Lrat
def cnf : CNF Nat := ⟨#[[(0,true)], [(0,false)]]⟩
def satCnf : CNF Nat := ⟨#[[(0,true)]]⟩
def certificate : Array LRAT.IntAction := #[.addEmpty 3 #[1,2]]
-- Native route retains the generated axiom; it is not pure kernel replay.
theorem nativeCheck : LRAT.check certificate cnf = true := by native_decide
theorem nativeUnsat : cnf.Unsat := LRAT.check_sound certificate cnf nativeCheck
#print axioms LRAT.check_sound
#print axioms nativeCheck
#print axioms nativeUnsat
def parseAndCheck (proof : String) (f : CNF Nat) : Except String Bool := do
  let acts ← LRAT.parseLRATProof proof.toUTF8
  return LRAT.check acts f
end Spike.Lrat
