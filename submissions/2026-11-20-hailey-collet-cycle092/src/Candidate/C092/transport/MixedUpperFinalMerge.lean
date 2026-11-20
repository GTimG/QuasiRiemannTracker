/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite phase multiplicities and a common fixed polynomial envelope. -/
import Candidate.C092.transport.MixedUpperFinalReserve
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeDetectorAmplitudeFirst HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.PacketJoin QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma packet_envelope_mono {C H Y Z U a d source fee strong target : ℝ} {m M : ℕ}
    (hC : 0≤C) (hH : 1≤H) (hY : 0≤Y) (hZ : 0≤Z) (hU : 1≤U)
    (hd : 0<d) (hm : m≤M) (ht : strong≤target) :
    C*H^m*Y^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*U^(finalPower a d source fee strong) ≤
    C*H^M*Y^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*U^(finalPower a d source fee target) := by
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hm) hC) (Real.rpow_nonneg hY _))
      (Real.rpow_nonneg hZ _)
  · apply Real.rpow_le_rpow_of_exponent_le hU
    have hp:=final_power_add_loss_le a d source fee strong target 0 hd (by simpa using sub_nonneg.mpr ht)
    simpa only [add_zero] using hp
  · exact Real.rpow_nonneg (zero_le_one.trans hU) _
  · positivity

lemma native_phase_sum_le (D : BaselineData) (a : ℝ) (ha : a≤7/8)
    (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (f : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t→ℝ) (A : ℝ)
    (hA : 0≤A) (hf : ∀bin∈bins,f bin≤A) :
    (∑bin∈bins,f bin) ≤ phaseCardBound D*A := by
  have hc : (bins.card:ℝ) ≤ phaseCardBound D:=
    (by exact_mod_cast Finset.card_le_univ bins : (bins.card:ℝ) ≤
      (Fintype.card (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)).trans
      (by simpa only [Nat.card_eq_fintype_card] using phase_card_le D a ha)
  calc
    _ ≤ ∑_bin∈bins,A:=Finset.sum_le_sum hf
    _ = (bins.card:ℝ)*A:=by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right hc hA

#print axioms packet_envelope_mono
#print axioms native_phase_sum_le
end
end QRH.Cycle092.MixedUpperFinal
