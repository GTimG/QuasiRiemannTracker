/- Actual coarse LOW cost at the same selected native source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowCoarseSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Candidate.Research.RecursiveAffine.NativeSelectedForest

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonical CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
open Cycle153SourceSchedule CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional LocalMoment
variable {Current Label : Type}[Fintype Current][DecidableEq Current][Fintype Label]
variable [Cycle63.AffineLedger]

/-- Populate the genuine native coarse source with the SAME actual
selected row carrier and affine source caps. Every source/plain/profile
norm gate is derived here. This is the large-height fallback used by the
returned LOW splice; no energy/count estimate on those rows is assumed. -/
theorem actual_affine_low_coarse_cost_from_source
    (original : ℕ)(Cs K Z : ℝ)(hZ : 1<Z)
    (coarse : MainLowCompleteCoarseSpec (α:=Current) (Fintype.card Current) 4 Cs (9/4) (9/4)
      (2*Real.log (9/4)) 4 1 (1/4) (nativeDriverRate original) (nativeMu/64) 3
      (nativeLowCoarseExponent (Fintype.card Current) original) K Z)
    (s : Input Current)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)(Sp : Finset (ℕ×ℕ))(hzero : (0,0)∈Sp)
    (reflected second : Bool)(R seed : Ideal O)(hseed : Squarefree seed)
    (Mrow amp reserve firstHeight : ℝ)(hM0 : 0 ≤ Mrow)(hM1 : Mrow ≤ 1)
    (hamp0 : 0 ≤ amp)(hamp : |amp| ≤ 4)
    (homega : |frequencyLoss Z 32 (nativeMu/64)+reserve| ≤ 4)(hreserve : 0 ≤ reserve)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val (geometryColumnIdeal reflected s R seed
      (Z^Mrow) Z (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val))) :
    let rows:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (nativeMu/64) reserve (9/4)
      firstHeight (Fintype.card Current) hZ bin caps.zero₁ caps.zero₂ firstIndex
    let datum:=fun r : rows=>geometryLowSecondDatum reflected s R seed Z Mrow amp (nativeMu/64) reserve
      (9/4) firstHeight (Fintype.card Current) hZ bin (firstIndex r.val.1) caps.zero₁ caps.zero₂ r.val.2
    ∀(W : 𝓢(ℝ,ℂ))(chi : rows→RayFourExpansion.RayCharacter)(Q : rows→Ideal O)(m : rows→O)
      (t0 u e : ℝ)
      (select : (r : rows)→(x y : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun _=>True)→BufferIndex e),
      mainLowPhysicalCompleteCost (Fintype.card Current) 1 (1/4) second
        (fun r : rows=>ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
        (fun r=>geometryFirstHighMass reflected s R seed W Mrow Z (nativeMu/64) (nativeDriverRate original)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex r.val.1).1.val/
          volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z (nativeMu/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin firstHeight (firstIndex r.val.1)))
        t0 u select ≤ K*(p.control Sp)^2*
          geometryHighFactor reflected (geometrySupportConstant (Fintype.card Current) 1 (1/4) (1/4)) bin*
          Z^(nativeLowCoarseExponent (Fintype.card Current) original) :=by
  intro rows datum W chi Q m t0 u e select
  have hz14 : Z^(1:ℝ) ≤ Z^(4:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hz34 : Z^(3:ℝ) ≤ Z^(4:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hlog : Real.log 2 ≤ 2*Real.log (9/4:ℝ) :=by
    have hh:=Real.log_le_log (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ) ≤ (9/4)*(9/4))
    rw [Real.log_mul (by norm_num : (9/4:ℝ)≠0) (by norm_num : (9/4:ℝ)≠0)] at hh
    linarith only [hh]
  have hp:=affine_low_profile_norm_receipt p Sp hzero
  have hnorm1 : ∀x,‖s.W₁ x‖ ≤ sourceControl Sp (p.profile 0) :=by simpa only [caps.profile₁] using hp.2.2.1
  have hnorm2 : ∀x,‖s.W₂ x‖ ≤ sourceControl Sp (p.profile 1) :=by simpa only [caps.profile₂] using hp.2.2.2.1
  have hc:=coarse
  unfold MainLowCompleteCoarseSpec at hc
  have hfirst:=hc hZ reflected s R seed Mrow amp reserve firstHeight
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hseed caps.endpoints
    (by rw [caps.lower]) (caps.sourceCap.trans hz34) (caps.volumeLog.trans (by norm_num))
    (by rw [abs_of_nonneg hM0];linarith only [hM1]) hamp homega caps.controls
    (fun i=>(caps.windows i).trans hlog)
    (fun side i=>(caps.plainScales side i).trans hz14) (fun i=>(caps.primeScales i).trans hz14)
    caps.poolCap caps.support₁ caps.support₂ caps.zero₁ caps.zero₂ hamp0 hreserve bin firstIndex hinj hf
  exact hfirst rows second W chi Q m t0 u e ((p.control Sp)^2)
    (sourceControl Sp (p.profile 0)) (sourceControl Sp (p.profile 1))
    (sq_nonneg _) hp.1 hp.2.1 hnorm1 hnorm2 hp.2.2.2.2 select
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_affine_low_coarse_cost_from_source
