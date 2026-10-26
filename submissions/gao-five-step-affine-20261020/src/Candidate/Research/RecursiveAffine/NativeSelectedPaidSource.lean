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
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153LowPhysical

variable {alpha Current Label : Type} [Fintype alpha] [DecidableEq alpha]
  [Fintype Current] [DecidableEq Current] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=alpha) M H} {j : Fin 4}

/-- The actual first/second labels and the genuine same-bin mass payment
produce the native paid source node. A first-mass loss is retained
literally; its small side is proved by the native bin theorem below. -/
def actualSelectedPaidNode (N : ReachableNode C j)
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
      budget N.localBase_gt_one key hz1 hz2 firstIndex) : NativePaidPathNode C.globalBase := by
  let f:=geometryFirstSource s R seed (N.localBase^Mrow) N.localBase xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex r.val.1).1.val.1
  let first:=geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex r.val.1).1.val
  let datum:=geometryLowSecondDatum reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
    budget N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
  exact {
    unit:=N.unit
    unit_pos:=N.unit_pos
    local_base:=Real.one_lt_rpow C.globalBase_gt_one N.unit_pos
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
    length:=Real.logb N.localBase (volume s)
    amp:=amp
    xi:=xi
    reserve:=reserve
    eps:=eps
    massLoss:=massLoss
    sideError:=sideError
    side:=by rw [←N.localBase_eq];exact hside r.val.1 }

/-- Definitional physical field bindings of the SAME actual selected
source node, for the native capacity/relative-scale trace constructor. -/
theorem actual_selected_paid_node_fields (N : ReachableNode C j)
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
    node.unit=N.unit ∧ node.scale=N.unit*Mrow ∧
      node.volumeLength=N.unit*Real.logb N.localBase (volume s) ∧
      node.amplification=N.unit*amp ∧
      node.commonLog=N.unit*(Real.logb N.localBase ((if reflected then node.first.1.2 else node.first.1.1).absNorm:ℝ)+
        Real.logb N.localBase ((if second then node.D else node.C).absNorm:ℝ)) := by
  intro node
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  change N.unit*(Real.logb (C.globalBase^N.unit) ((if reflected then node.first.1.2 else node.first.1.1).absNorm:ℝ)+
    Real.logb (C.globalBase^N.unit) ((if second then node.D else node.C).absNorm:ℝ))=_
  rw [←N.localBase_eq]

/-- The selected native chain retains precisely the own first and second
ideals used by the SAME paid node; selecting its second common allocation
does not change this source cost. -/
theorem actual_selected_paid_node_chain_fields (N : ReachableNode C j)
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
    let datum:=geometryLowSecondDatum reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
    let src:=geometryLowFirstChild reflected s R seed (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key firstHeight (firstIndex r.val.1)
    ∀allocation : actualAllocations src.pools (if second then datum.D else datum.C),
    let ch:=geometryLowActualChain reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2 second allocation
    node.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+
      Real.logb N.localBase (ch.E₂.absNorm:ℝ)) := by
  intro node datum src allocation ch
  have hfields:=actual_selected_paid_node_fields N reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex massLoss sideError hside r
  rw [hfields.2.2.2.2]
  have hfirst : (if reflected then node.first.1.2 else node.first.1.1)=ch.C₁ := by
    cases reflected <;> rfl
  have hsecond : (if second then node.D else node.C)=ch.E₂ := by
    cases second <;> rfl
  rw [hfirst,hsecond]

/-- Both the first-column mass bound and the source side cancellation are
obtained from the SAME actual geometry bin. There is no premise that the
mass-dyad exponent itself is small, nor any source-energy/count premise. -/
theorem actual_selected_paid_source (N : ReachableNode C j)
    (reflected : Bool)(budget : ℕ)(lo ap : ℝ)(hlo : 0<lo)(hap : 0<ap)
    (s : Input Current)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))
    (Mrow xi Bmass epsMass : ℝ)
    (hcard : Fintype.card Current ≤ budget)(hlower : lo ≤ s.lower)
    (hseed : Squarefree seed)(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ N.localBase^Bmass)(heps : 0 ≤ epsMass)
    (hs1 : ∀x,s.W₁ x≠0→ap ≤ x)(hs2 : ∀x,s.W₂ x≠0→ap ≤ x)
    (key : ℤ×(Fin 5→ℤ)) :
    ∃exponent sideLower : ℝ,
      ((key.2 2:ℝ)+1)*Real.logb N.localBase 2+exponent-sideLower=6*Real.logb N.localBase 2 ∧
      ∀l : FirstColumnIndex (geometryFirstSource s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
        let first:=geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l
        lowAllowedExponent reflected N.localBase (Real.logb N.localBase (volume s)) first ≤ exponent ∧
        geometryFirstHighMass reflected s R seed W Mrow N.localBase xi epsMass
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l ≤
          geometryHighFactor reflected (geometrySupportConstant budget lo ap ap) key*
            N.localBase^(Bmass*epsMass-sideLower) ∧
        (Bmass*epsMass-sideLower)+lowLabelSide reflected N.localBase
          (Real.logb N.localBase (volume s)) first ≤ Bmass*epsMass+6*Real.logb N.localBase 2 :=
  actual_first_mass_and_old_side reflected budget lo ap hlo hap s R seed W Mrow N.localBase xi
    Bmass epsMass N.localBase_gt_one hcard hlower hseed hz1 hz2 hsource heps hs1 hs2 key

/-- The literal selected-row raw edge becomes the native global path
edge. The first-mass loss is in shiftedOutside exactly once. Actual
deleted weight, model deletion and all remaining fees are distinct; their
difference is charged explicitly. No intermediate row factor is dropped. -/
theorem actual_selected_raw_edge_global
    (N : ReachableNode C j)
    (reflected second : Bool)(s : Input Current)(R seed : Ideal O)
    (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
      (geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight
      budget N.localBase_gt_one key hz1 hz2 firstIndex)
    (q actualDeleted modelDeleted remainingFees : ℝ) :
    let node:=actualSelectedPaidNode N reflected second s R seed Mrow amp xi reserve eps b firstHeight budget
      key hz1 hz2 firstIndex massLoss sideError hside r
    N.localBase^(Mrow+
      actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
        N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 0+
      q*actualDeleted+massLoss+remainingFees)=
    C.globalBase^(node.scale+node.shiftedOutside+q*(N.unit*modelDeleted)+
      N.unit*(remainingFees+q*(actualDeleted-modelDeleted))) := by
  intro node
  let X0:=actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
    N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 0
  have hscale : node.scale=N.unit*Mrow := rfl
  have hcoord : node.coordinate 0=N.unit*X0 := by
    dsimp only [NativePaidPathNode.coordinate]
    change N.unit*actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
      (C.globalBase^N.unit) Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 0=N.unit*X0
    rw [←N.localBase_eq]
  have hshift : node.shiftedOutside=N.unit*X0+N.unit*massLoss := by
    change node.coordinate 0+N.unit*massLoss=_
    rw [hcoord]
  let E:=Mrow+X0+q*actualDeleted+massLoss+remainingFees
  change N.localBase^E=_
  calc
    _=(C.globalBase^N.unit)^E := congrArg (fun z : ℝ=>z^E) N.localBase_eq
    _=C.globalBase^(N.unit*E) := (Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le _ _).symm
    _=_ := by
      congr 1
      rw [hscale,hshift]
      dsimp only [E]
      ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_paid_source
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_raw_edge_global
