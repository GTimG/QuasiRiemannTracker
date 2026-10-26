/- Literal initial source presentation and norm after the root LOW step. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualNativePrefix
import Candidate.Research.RecursiveAffine.NativePrefixPresentation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondInputCapacitySource Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn Cycle153HighProvider Cycle153JointCount

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Construct the actual first inner dictionary directly from the
original parent's native presentation. Its original multiplier is one;
there is no invented inner ReachableNode at the root. -/
theorem actual_root_native_prefix
    (etaSeed : Character) (F0 : NaturalRow etaSeed 1) (R0 : Ideal O)
    (s : Input α) (hparent : ParentPresentation s.η F0 R0)
    (Z : ℝ) (hZ : 1<Z) (Q : Ideal O)
    (reflected second : Bool) (Mrow amp xi reserve b t eps : ℝ) (budget : ℕ)
    (hMrow : Mrow ≤ 2) (hamp : 0 ≤ amp) (hloss : 0 ≤ frequencyLoss Z 32 xi+reserve)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1) (hb : 0<b)
    (hsmall : Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2 ≤ 1)
    (hsource : sourceRadius s ≤ Z^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q) :
    let datum:=geometryLowSecondDatum reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s 1 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) 1 s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st:=retainedState Z Bmask hZ (g.datum.τ chi) (internalQ Q etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s 1 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    let units:=fun l=>(firstDictionaryUnit (!reflected) etaSeed 1 F0 R0 l:O)
    ∃Next : PrefixHighPresentation (secondFixedDictionary etaSeed) st.character st.puncture,
      Next.mult=Cycle63Moment.childMultiplier (!reflected) 1 units ⟨first,label⟩ ∧
      ((Ideal.span {Next.mult}).absNorm:ℝ) ≤ Z^prefixCap 0 ∧
      st.rowWidth+Real.logb Z ((Ideal.span {Next.mult}).absNorm:ℝ) ≤
        actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 2+
        (Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2) := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label units
  have hlocal:=depth_two_presented_low_child 1 reflected second etaSeed 1 F0 R0 one_ne_zero
    s hparent 1 1 Z Mrow amp xi reserve b t budget hZ bin q hz1 hz2 n allocation r hf1 hf2
    chi Bmask Q hP hPN st.width (le_refl _)
  obtain ⟨P,hvP⟩:=DepthTwoPresented.presentation hlocal
  let Next : PrefixHighPresentation (secondFixedDictionary etaSeed) st.character st.puncture:=
    nativePrefixPresentation P hP
  have hmult : Next.mult=Cycle63Moment.childMultiplier (!reflected) 1 units ⟨first,label⟩:=hvP.symm
  let fs:=geometryFirstSource s 1 1 (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1
  have hfirstnorm : (first.1.1.absNorm:ℝ) ≤ Z^(130:ℝ) := by
    have hg:=actual_main_low_first_source_gates reflected s 1 1 (Z^Mrow) Z xi 3
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) squarefree_one hz1 hz2 hsource bin (fun _:Unit=>q) ()
    exact hg.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hscale:=live_main_row_scale_le g hZ hb reflected (!reflected) second first reserve eps
    fs.hC fs.hD fs.sameSupport rfl datum.C datum.D datum.inactive rfl rfl HEq.rfl 1
    units (fun l=>Units.isUnit _) (by simpa [normValue] using heps0)
    (hmult ▸ Next.hv) (g.datum.τ chi) (internalQ Q etaSeed) (chain.R₂*chain.E₂) hP hPN
  have hscaleNext : st.rowWidth+Real.logb Z ((Ideal.span {Next.mult}).absNorm:ℝ) ≤
      actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
        Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 2+
      (Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2) := by
    rw [hmult]
    exact hscale
  let physical : NativePaidPathNode Z:={
    unit:=1
    unit_pos:=by norm_num
    local_base:=by simpa only [Real.rpow_one] using hZ
    reflected:=reflected
    second:=second
    first:=first
    firstC:=fs.hC
    firstD:=fs.hD
    firstSupport:=fs.sameSupport
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
    massLoss:=0
    sideError:=lowLabelSide reflected (Z^1) (Real.logb Z (volume s)) first
    side:=le_of_eq (zero_add _) }
  have hcoord : physical.coordinate 2=actualHighCoordinates reflected (!reflected) second first
      datum.C datum.D datum.inactive Z Mrow (Real.logb Z (volume s)) amp xi reserve eps 2 := by
    simp only [NativePaidPathNode.coordinate,physical,Real.rpow_one,one_mul]
  have hi:=native_prefix_increment physical
    (by simpa only [physical,Real.rpow_one] using hfirstnorm) hMrow hamp
    (by simpa only [physical,Real.rpow_one] using hloss) heps le_rfl
    st.rowWidth (Real.logb Z ((Ideal.span {Next.mult}).absNorm:ℝ)) 0
    (Real.logb Z 4+2*(budget:ℝ)*Real.logb Z b+xi/2) st.row_nonneg hsmall
    (by rw [hcoord];simpa only [sub_zero] using hscaleNext)
  have hpos : (0:ℝ) < ((Ideal.span {Next.mult}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr Next.hv))
  refine ⟨Next,hmult,?_,hscaleNext⟩
  apply (Real.logb_le_iff_le_rpow hZ hpos).mp
  simpa only [prefixCap,Nat.cast_zero,zero_add,mul_one,sub_zero] using hi

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_prefix
