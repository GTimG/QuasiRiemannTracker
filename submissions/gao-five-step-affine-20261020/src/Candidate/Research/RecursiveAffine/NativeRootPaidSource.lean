/- Copyright (c) 2026 Hailey Collet; actual source binding (c) 2026
Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeForestAttach
import Candidate.Research.RecursiveAffine.LowPhysical.ActualFirstMass
import Candidate.Research.RecursiveAffine.NativePaidPathNode
import Candidate.Research.RecursiveAffine.ReachableNode

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153LowPhysical

variable {alpha Current Label : Type} [Fintype alpha] [DecidableEq alpha]
  [Fintype Current] [DecidableEq Current] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=alpha) M H} {j : Fin 4}

/-- Literal outer-root source node. Its base is the original global base
and its physical unit is exactly one; no inner reachable node is assumed. -/
def actualRootSelectedPaidNode (Z : ℝ) (hZ : 1<Z)
    (reflected second : Bool) (s : Input Current) (R seed : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow)
      Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected Z (Real.logb Z (volume s))
      (geometryFirstLabel s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex) : NativePaidPathNode Z := by
  let f:=geometryFirstSource s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val.1
  let first:=geometryFirstLabel s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val
  let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b firstHeight
    budget hZ key (firstIndex r.val.1) hz1 hz2 r.val.2
  exact {
    unit:=1
    unit_pos:=one_pos
    local_base:=by simpa only [Real.rpow_one] using hZ
    reflected:=reflected
    second:=second
    first:=first
    firstC:=f.hC
    firstD:=f.hD
    firstSupport:=f.sameSupport
    C:=datum.C
    D:=datum.D
    hC:=datum.hC
    hD:=datum.hD
    secondSupport:=datum.sameSupport
    inactive:=datum.inactive
    rowWidth:=Mrow
    length:=Real.logb Z (volume s)
    amp:=amp
    xi:=xi
    reserve:=reserve
    eps:=eps
    massLoss:=massLoss
    sideError:=sideError
    side:=by simpa only [Real.rpow_one] using hside r.val.1 }

/-- Genuine outer-root same-bin first-mass and side receipt. -/
theorem actual_root_selected_paid_source (Z : ℝ) (hZ : 1<Z)
    (reflected : Bool)(budget : ℕ)(lo ap : ℝ)(hlo : 0<lo)(hap : 0<ap)
    (s : Input Current)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
    (Mrow xi Bmass epsMass : ℝ)
    (hcard : Fintype.card Current ≤ budget)(hlower : lo ≤ s.lower)
    (hseed : Squarefree seed)(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^Bmass)(heps : 0 ≤ epsMass)
    (hs1 : ∀x,s.W₁ x≠0→ap ≤ x)(hs2 : ∀x,s.W₂ x≠0→ap ≤ x)
    (key : ℤ×(Fin 5→ℤ)) :
    ∃exponent sideLower : ℝ,
      ((key.2 2:ℝ)+1)*Real.logb Z 2+exponent-sideLower=6*Real.logb Z 2 ∧
      ∀l : FirstColumnIndex (geometryFirstSource s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
        let first:=geometryFirstLabel s R seed (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key l
        lowAllowedExponent reflected Z (Real.logb Z (volume s)) first ≤ exponent ∧
        geometryFirstHighMass reflected s R seed W Mrow Z xi epsMass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key l ≤
          geometryHighFactor reflected (geometrySupportConstant budget lo ap ap) key*
            Z^(Bmass*epsMass-sideLower) ∧
        (Bmass*epsMass-sideLower)+lowLabelSide reflected Z
          (Real.logb Z (volume s)) first ≤ Bmass*epsMass+6*Real.logb Z 2 :=
  actual_first_mass_and_old_side reflected budget lo ap hlo hap s R seed W Mrow Z xi
    Bmass epsMass hZ hcard hlower hseed hz1 hz2 hsource heps hs1 hs2 key

/-- Exact outer-root raw edge before the separately compensated length-majorant lift. -/
theorem actual_root_selected_raw_edge
    (Z : ℝ)(hZ : 1<Z)
    (reflected second : Bool)(s : Input Current)(R seed : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow)
      Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected Z (Real.logb Z (volume s))
      (geometryFirstLabel s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight
      budget hZ key hz1 hz2 firstIndex)
    (q actualDeleted modelDeleted remainingFees : ℝ) :
    let node:=actualRootSelectedPaidNode Z hZ reflected second s R seed Mrow amp xi reserve eps b firstHeight budget
      key hz1 hz2 firstIndex massLoss sideError hside r
    Z^(Mrow+
      actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
        Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 0+
      q*actualDeleted+massLoss+remainingFees)=
    Z^(node.scale+node.shiftedOutside+q*modelDeleted+(remainingFees+q*(actualDeleted-modelDeleted))) := by
  intro node
  let X0:=actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
    Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 0
  have hscale : node.scale=Mrow := by change 1*Mrow=Mrow;ring
  have hshift : node.shiftedOutside=X0+massLoss := by
    change (1:ℝ)*actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
      (Z^1) Mrow (Real.logb Z (volume s)) amp xi reserve eps 0+1*massLoss=_
    rw [Real.rpow_one]
    dsimp only [X0]
    ring
  change Z^(Mrow+X0+q*actualDeleted+massLoss+remainingFees)=_
  congr 1
  rw [hscale,hshift]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_selected_paid_source
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_selected_raw_edge
