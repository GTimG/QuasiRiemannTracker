/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest
import Candidate.Research.RecursiveAffine.ActualReturnTraceShift
import Candidate.Research.RecursiveAffine.RootForestReceipt

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}

/-- The actual second-projector shell loss shifts the SAME terminal
records. Raw edge weights, original source histories and native path
receipts are unchanged; the shifted native loss is paid explicitly. -/
def NativeNodeForestReceipt.shiftShell {N : ReachableNode C j}
    (receipt : NativeNodeForestReceipt hH N Bsrc boxes)(shift : ℝ)
    (hloss : ∀d p,(receipt.family.part d p).loss+shift ≤ terminalLossCap j) :
    NativeNodeForestReceipt hH N Bsrc boxes where
  family:=shiftedReturnedForest receipt.family shift
  chronology:=OrientedFamilyHistory.toNode N _
    ((OrientedFamilyHistory.ofNode N receipt.family receipt.chronology).shift receipt.family shift)
  path:=fun d p=>(receipt.path d p).shiftTerminal shift
  terminalLoss:=hloss
  terminalSource:=receipt.terminalSource
  classCap:=receipt.classCap

private theorem shifted_part_heq
    {Base : Type}{base : Character→Base→Character}{q Z B T : ℝ}{eta : Character}{v v' : O}
    (a : ReturnedPartAt M H hH q base eta Z B T v)
    (a' : ReturnedPartAt M H hH q base eta Z B T v')
    (hv : v=v')(he : HEq a a')(shift : ℝ) :
    HEq (shiftedReturnedPart a shift) (shiftedReturnedPart a' shift) := by
  cases hv
  have h:=eq_of_heq he
  cases h
  exact HEq.rfl

/-- Apply the genuine root shell fee to both sides of the literal
terminal binding. In particular the child trace is shifted along with
the root family, so no terminal identity or source weight is lost. -/
def shiftRootNativePathShell
    {F : RootLowFamily (hH:=hH) C}{d : SuffixDepth 4}{p : F.Prefix d}
    (path : RootNativePath F d p)(shift : ℝ) :
    RootNativePath (shiftedReturnedForest F shift) d p where
  child:=path.child
  childFamily:=shiftedReturnedForest path.childFamily shift
  childPrefix:=path.childPrefix
  trace:=path.trace.shiftTerminal shift
  edge:=path.edge
  multiplier:=path.multiplier
  part:=shifted_part_heq _ _ path.multiplier path.part shift
  weight:=path.weight
  missing:=path.missing

/-- A root residual shell retains one actual whole forest with its
original physical chronology, literal raw coefficient, and native root
edge. Only terminal exponents/losses receive the charged source power. -/
def NativeRootForestReceipt.shiftShell
    (receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes)(shift : ℝ)
    (hloss : ∀d p,(receipt.family.part d p).loss+shift ≤ 6/1000000000000) :
    NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes where
  family:=shiftedReturnedForest receipt.family shift
  chronology:=receipt.chronology.shift receipt.family shift
  path:=fun d p=>shiftRootNativePathShell (receipt.path d p) shift
  terminalLoss:=hloss
  terminalSource:=receipt.terminalSource
  classCap:=receipt.classCap

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.NativeNodeForestReceipt.shiftShell
#print axioms OAI.SevenEighths.Cycle153RegionalLow.NativeRootForestReceipt.shiftShell
