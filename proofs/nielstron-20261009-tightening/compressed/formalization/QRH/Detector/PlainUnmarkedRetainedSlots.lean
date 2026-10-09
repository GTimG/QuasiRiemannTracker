import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import QRH.Moments.DetectorPlainUnmarkedParameters

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Original unmarked energy, independent physical slots. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}
theorem retained_unmarked_bound_slots (D:Parameters.HighData Δ)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label Slot U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1<U)
    (hη:(η.modulus.absNorm:ℝ)≤U^(delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+delta D+stageError D) := by
  let s:=state F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=unmarked_state_admission_slots D F η Q radialMajorant radialSupportUpper hU
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width≤2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1≤U^F.m ∧ U^F.m≤U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one] using hz

end SevenEighths.ProbeDetectorPlainUnmarkedField
end
end OAI
