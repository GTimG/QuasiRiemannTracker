/- The actual selected OLD source at its final native target. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedOldThreshold

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional Cycle153.RegionalSchedule
open Cycle63FinalCapacity CenteredMomentSectorLocalization Cycle153RegionalLow
open CenteredMomentSourceLiveColumn CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonAllocationSum CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentFirstExceptionalPrefactor Cycle153LowPhysical Cycle153SourceSchedule
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable [Cycle63.AffineLedger]

/-- Invoke the genuine OLD source at the SAME physical rows. Child
source radii, all actual dyads, their post-rate count, and the final OLD
exponent are proved here from the native sources, not supplied as energy
or favorable-count assumptions. The only threshold depends on fixed
norm/cardinality data, before the moving source and ledger. -/
def actualSelectedOldTargetAt
    (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ)(hNrow : Nrow≤budget)(Z : ℝ)(hZ : 1<Z)
    (hlarge : actualSelectedOldThreshold Bnorm hB budget Nrow≤Z)
    (g : GeometryAffineLowSchedule)(hmu : g.μ=nativeMu)
    (hprice : Cycle63.AffineLedger.price≤Cycle63.Optimization.slotPrice)
    (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
    (caps : GeometryAffineLowSourceGates s p Cs Z)(hcard : Fintype.card alpha≤Nrow)
    (reflected second : Bool)(R : Ideal O)(Mrow amp firstHeight oldError mesh sourcePad : ℝ)
    (hMrow0 : 0≤Mrow)(hMrow1 : Mrow≤1)(hamp0 : 0≤amp)(hamp4 : |amp|≤4)
    (homega4 : |frequencyLoss Z 32 (nativeMu/64)+nativeMu/8|≤4)
    (hpad : sourcePad≤nativeMu/8)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R 1 (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R 1 (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)))
    (Psi : 𝓢(ℝ,ℂ))(Cg fixed : ℝ)(hCg : 0≤Cg)(hfixed : 0≤fixed) :=
  let after:=actualSelectedOldAfter Bnorm hB budget Nrow Z hlarge
  let omega:=frequencyLoss Z 32 (nativeMu/64)+nativeMu/8
  let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
    2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
      (omega+nativeMu/8)+Cycle63.AffineLedger.q*mesh
  let hchild:=fun l : Label=>
    (after.2.2 s 2 hcard caps.endpoints caps.volume
      (geometryColumnIdeal reflected s R 1 (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R (firstIndex l).2
      (geometryColumnCharacter reflected s R 1 (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      firstHeight (hf1 l)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by norm_num [nativeMu,primitiveError] : (2:ℝ)+nativeMu/8≤130))
  let hsource4:=caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : (3:ℝ)≤4))
  let hvolume4:=caps.volumeLog.trans (by norm_num : (3:ℝ)≤4)
  let hMrow4 : |Mrow|≤4:=by rw [abs_of_nonneg hMrow0];linarith only [hMrow1]
  let hbox:=fun r : NativeLowRows reflected s R 1 Z Mrow amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight Nrow hZ key hz1 hz2 firstIndex=>
    after.1.2.2.2 reflected s R 1 Mrow amp (nativeMu/8) firstHeight
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hcard caps.endpoints (by simp) hz1 hz2
      hsource4 hvolume4 hMrow4 hamp4 homega4 hamp0
      (div_nonneg nativeMu_pos.le (by norm_num)) key (firstIndex r.val.1).1.val
      (firstIndex r.val.1).1.property (firstIndex r.val.1).2 (hf1 r.val.1) r.val.2
  let hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)≤Cycle63.AffineLedger.lowRate:=by
    dsimp only [Cycle63.AffineLedger.lowRate]
    exact div_le_div_of_nonneg_left Cycle63.AffineLedger.q_pos.le
      (mul_pos (by norm_num : (0:ℝ)<6) Cycle63.AffineLedger.price_pos)
      (mul_le_mul_of_nonneg_left hprice (by norm_num : (0:ℝ)≤6))
  let hradial0 : 0≤omega+nativeMu/8:=by
    have hf:=frequencyLoss_nonneg Z 32 (nativeMu/64) hZ (by norm_num)
      (div_nonneg nativeMu_pos.le (by norm_num))
    dsimp only [omega]
    linarith only [hf,nativeMu_pos]
  let hcommon : common≤actualSourceCommon64 g (Fintype.card alpha) omega mesh:=by
    dsimp only [actualSourceCommon64]
    rw [hmu]
    dsimp only [common]
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hrate hradial0)) le_rfl
  let hpadg : sourcePad≤g.μ/8:=by rw [hmu];exact hpad
  after.1.1.2 (inferInstance : Cycle63.AffineLedger) g hmu reflected second s R Mrow amp
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight common sourcePad oldError omega mesh
    (actualSelectedOldBoxConstant Bnorm hB budget Nrow) Cg fixed Nrow hZ key hz1 hz2 firstIndex Psi
    (hcard.trans hNrow) (by rw [caps.lower]) caps.poolCap caps.sourceCap hCg hfixed caps.support₁ caps.support₂
    hf1 hinj hchild hcommon hpadg
    (actualSelectedOldBoxConstant_pos Bnorm hB budget Nrow).le
    (geometryMainAbsoluteBox Z Nrow 4 (nativeMu/8) (9/4)) hbox after.1.2.2.1

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actualSelectedOldTargetAt
