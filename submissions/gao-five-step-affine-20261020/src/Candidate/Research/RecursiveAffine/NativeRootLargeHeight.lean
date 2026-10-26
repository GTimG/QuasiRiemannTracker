/- The genuine large-height LOW branch, with a literal empty arithmetic return.
Copyright (c)2026 Zhongpai Gao. Native coarse estimate by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowCoarseInvoke
import Candidate.Research.RecursiveAffine.NativeLowLargeHeight
import Candidate.Research.RecursiveAffine.NativeRootSourceReceipt

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentSecondCanonical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
open Cycle153SourceSchedule Cycle153Reachable Cycle153SourceReturn
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional LocalMoment
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable [Cycle63.AffineLedger]

/-- The large-height branch calls the actual native coarse source on the
SAME selected rows, then absorbs its polynomial scale by the genuine
height cutoff. Its return is the literal empty fully licensed receipt.
No small-height, node-energy, column-energy or returned-count estimate is
assumed. The raw outer scale and the moving native OLD target stay exact. -/
theorem actual_native_root_large_height_empty_return
    (original : ℕ)(hcard : Fintype.card alpha≤original)
    (tau : ℝ)(htau : 0<tau)(Cs K : ℝ)(hK : 0 ≤ K)
    (coarse : MainLowCompleteCoarseSpec (α:=alpha) (Fintype.card alpha) 4 Cs (9/4) (9/4)
      (2*Real.log (9/4)) 4 1 (1/4) (nativeDriverRate original) (nativeMu/64) 3
      (nativeLowCoarseExponent (Fintype.card alpha) original) K C.globalBase)
    (s : Input alpha)(p : Profiles (1/4) (9/4))(height : ℝ)(hheight : 0≤height)
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (Sp : Finset (ℕ×ℕ))(hzero : (0,0)∈Sp)
    (reflected second : Bool)(R seed : Ideal O)(hseed : Squarefree seed)
    (Mrow amp reserve firstHeight outer target : ℝ)
    (hM0 : 0 ≤ Mrow)(hM1 : Mrow ≤ 1)(hamp0 : 0 ≤ amp)(hamp : |amp| ≤ 4)
    (homega : |frequencyLoss C.globalBase 32 (nativeMu/64)+reserve| ≤ 4)
    (hreserve : 0 ≤ reserve)(htarget : -1 ≤ target)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (C.globalBase^Mrow)
      C.globalBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin)
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val (geometryColumnIdeal reflected s R seed
      (C.globalBase^Mrow) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (C.globalBase^Mrow)
      C.globalBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _)
      bin (firstIndex l).1.val,(firstIndex l).1.val.2.1.val))) :
    let rows:=mainLowSelectedNonzeroRows reflected s R seed C.globalBase Mrow amp (nativeMu/64)
      reserve (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one bin caps.zero₁ caps.zero₂ firstIndex
    let datum:=fun r : rows=>geometryLowSecondDatum reflected s R seed C.globalBase Mrow amp (nativeMu/64)
      reserve (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(W : 𝓢(ℝ,ℂ))(chi : rows→RayFourExpansion.RayCharacter)(Q : rows→Ideal O)(m : rows→O)
      (t0 u e : ℝ)
      (select : (r : rows)→(x y : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun _=>True)→BufferIndex e),
      ¬2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|)) ≤ C.globalBase^tau →
      ∀(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)),
      ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
        receipt.family=emptyReturnedForest ∧
        C.globalBase^outer*mainLowPhysicalCompleteCost (Fintype.card alpha) 1 (1/4) second
          (fun r : rows=>ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun r=>geometryFirstHighMass reflected s R seed W Mrow C.globalBase (nativeMu/64)
            (nativeDriverRate original)
            (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin (firstIndex r.val.1).1.val/
            volume (geometryLowFirstChild reflected s R seed (C.globalBase^Mrow) C.globalBase (nativeMu/64)
              (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) bin firstHeight (firstIndex r.val.1)))
          t0 u select ≤
        ((2+4*Real.pi)^(nativeLowLargeHeightDegree original tau htau)*K)*
          ((p.control Sp)^2*geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) bin*
            (1+|firstHeight|+height)^(nativeLowLargeHeightDegree original tau htau)*
            (1+|t0|)^(nativeLowLargeHeightDegree original tau htau)*
            (1+|u|)^(nativeLowLargeHeightDegree original tau htau))*C.globalBase^(outer+target) :=by
  intro rows datum W chi Q m t0 u e select hlarge Bsrc boxes
  have hc:=actual_affine_low_coarse_cost_from_source original Cs K C.globalBase
    C.globalBase_gt_one coarse s p caps Sp hzero reflected second R seed hseed
    Mrow amp reserve firstHeight hM0 hM1 hamp0 hamp homega hreserve bin firstIndex hf hinj
    W chi Q m t0 u e select
  have hexponent : nativeLowCoarseExponent (Fintype.card alpha) original ≤
      nativeLowCoarseExponent original original :=by
    have hh : (Fintype.card alpha:ℝ) ≤ (original:ℝ):=by exact_mod_cast hcard
    unfold nativeLowCoarseExponent
    nlinarith only [hh]
  have hcontrol : 0 ≤ (p.control Sp)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) bin :=by
    exact mul_nonneg (sq_nonneg _) (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hcmax:=hc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le hexponent)
    (by simpa only [mul_assoc] using mul_nonneg hK hcontrol))
  have hs:=Classical.choose_spec (geometry_uniform_shifted_height_splice
    (nativeLowCoarseExponent original original) (-1) tau htau 0)
  have hb:=hs C.globalBase target firstHeight height t0 u _ 0 K
    ((p.control Sp)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) bin)
    C.globalBase_gt_one.le htarget hheight (by norm_num) hK hcontrol
    (fun h=>False.elim (hlarge h)) (by simpa only [mul_assoc] using hcmax)
  refine ⟨native_empty_root_forest_receipt Bsrc boxes,rfl,?_⟩
  have hraw:=mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (zero_lt_one.trans C.globalBase_gt_one).le outer)
  apply hraw.trans_eq
  rw [Real.rpow_add (zero_lt_one.trans C.globalBase_gt_one)]
  simp only [zero_add,nativeLowLargeHeightDegree]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_root_large_height_empty_return
