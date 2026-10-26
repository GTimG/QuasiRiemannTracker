/- Copyright (c) 2026 Hailey Collet; actual source binding (c) 2026
Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedPaidSource

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153LowPhysical

variable {alpha Current Label : Type} [Fintype alpha] [DecidableEq alpha]
  [Fintype Current] [DecidableEq Current] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=alpha) M H} {j : Fin 4}

/-- The actual node keeps the literal native source coordinates after
converting only their physical unit. -/
theorem actual_selected_paid_node_coordinates (N : ReachableNode C j)
    (reflected second : Bool) (s : Input Current) (R seed : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
      (geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key hz1 hz2 firstIndex) :
    let node:=actualSelectedPaidNode N reflected second s R seed Mrow amp xi reserve eps b firstHeight budget
      key hz1 hz2 firstIndex massLoss sideError hside r
    ∀i : Fin 4,node.coordinate i=N.unit*actualHighCoordinates reflected (!reflected) second
      node.first node.C node.D node.inactive N.localBase Mrow (Real.logb N.localBase (volume s))
      amp xi reserve eps i := by
  intro node i
  dsimp only [NativePaidPathNode.coordinate]
  change N.unit*actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
    (C.globalBase^N.unit) Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps i=_
  rw [←N.localBase_eq]

theorem actual_selected_paid_node_missing (N : ReachableNode C j)
    (reflected second : Bool) (s : Input Current) (R seed : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
      (geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key hz1 hz2 firstIndex) :
    let node:=actualSelectedPaidNode N reflected second s R seed Mrow amp xi reserve eps b firstHeight budget
      key hz1 hz2 firstIndex massLoss sideError hside r
    node.coordinate 1=N.unit*Real.logb N.localBase
      ((firstSourceMissing (!reflected) node.first).absNorm:ℝ) := by
  intro node
  rw [actual_selected_paid_node_coordinates N reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex massLoss sideError hside r 1]
  rfl

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_paid_node_coordinates
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_paid_node_missing
