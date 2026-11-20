/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The true complete-label dilation controls the reflected logarithmic window.
This is geometry only; no extra power payment is introduced. -/
import Candidate.C092.transport.MixedPacketScalePacket

set_option autoImplicit false
namespace QRH.Cycle092.MixedPacketScale
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical ProbeRowRadicalConductor
open Cycle25.Weighted.Numerator
local notation "O" => HeckeFamily.O

/-- The SAME max-one dilation used by P15 places every retained Fourier
scale in the earlier long source window. It is not charged a second time. -/
theorem true_dilation_window (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (u : FreeRow) (data : PhysicalReflectionData S hS u)
    (U N Y n dilation : ℝ) (hU : 0<U) (hN : 0<N)
    (hrow : rowNorm u≤U) (hY : Y=U^n)
    (hbox : max 1 (data.combinedConductor/((fixedConductorConstant S:ℝ)*rowNorm u)*N)
      ≤ U^dilation) :
    data.combinedConductor ≤ (fixedConductorConstant S:ℝ)*
      U^(1+dilation-n)*(Y/N) := by
  let K : ℝ := fixedConductorConstant S
  have hK : 0<K := by dsimp [K];exact_mod_cast fixedConductorConstant_pos S hS
  have hr : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hcp := data.combined_pos.le
  let L := data.combinedConductor/(K*rowNorm u)
  have hLN : L*N≤U^dilation := (le_max_right _ _).trans hbox
  have hid : data.combinedConductor=K*rowNorm u*(L*N)/N := by
    dsimp [L]
    field_simp
  calc
    _ = K*rowNorm u*(L*N)/N := hid
    _ ≤ K*U*U^dilation/N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hrow hK.le) hLN
        (by dsimp [L];positivity) (by positivity)
    _ = K*U^(1+dilation-n)*(Y/N) := by
      rw [hY]
      have he : U^(1+dilation-n)*U^n = U*U^dilation := by
        rw [←Real.rpow_add hU,show 1+dilation-n+n=1+dilation by ring,
          Real.rpow_add hU,Real.rpow_one]
      rw [div_eq_mul_inv,div_eq_mul_inv]
      calc
        _ = K*(U*U^dilation)*N⁻¹ := by ring
        _ = K*(U^(1+dilation-n)*U^n)*N⁻¹ := by rw [he]
        _ = _ := by ring

#print axioms true_dilation_window
end
end QRH.Cycle092.MixedPacketScale
