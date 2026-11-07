/- Minimal computational vector notation; Subhanjan Das, MIT, AI-assisted with OpenAI Codex.
The implementation matches Mathlib's Fin.cons / Matrix.vecCons definitionally. -/
import Init.Data.Rat
import Lean.Elab.Tactic.Decide
namespace Das.QRH.CoreVector

def empty : Fin 0 → Rat := Fin.elim0
def cons {n : Nat} (h : Rat) (t : Fin n → Rat) : Fin (n+1) → Rat :=
 Fin.cases h t
macro "q![" xs:term,* "]" : term => do
 let mut out ← `(Das.QRH.CoreVector.empty)
 for x in xs.getElems.reverse do
  out ← `(Das.QRH.CoreVector.cons $x $out)
 return out
end Das.QRH.CoreVector
