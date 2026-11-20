/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedPhysicalPaymentOriginal
import Candidate.C092.transport.TwistedRawSourceBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedPhysicalPaymentNative_29c6319b7f961b5a_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open QRH.Cycle092.SignedCenter
open MixedCommonRestriction

open Filter CenteredMomentFiniteProfileExceptional

open CenteredMomentSourceLiveColumn CenteredMomentCommonRawCost

open CenteredMomentDivisorAllocation MixedCommonCoefficient

/-- One literal summand of coloredFullyAllocatedPhysicalHeight. -/
def nativePhysicalTerm (r:Source ι a b) (ha:0<a) (hb:0≤b) (D:FixedCubeDatum)
    (ω₁ ω₂:Character) (G L:Id) (B:commonAlloc r G)
    (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))
    (E:fullPrimaryAlloc r G B L) (v:ℝ) : ℂ :=
  (frozenWeight (punctureProduct r.S r.H) B.val*
    TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val*
    frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P)*
  (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val))⁻¹)*
  (TwistedRawSource.primaryCanonicalScalar r (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ
    G L B E (shiftedSlotCoefficient r v) aL*
    coloredNativePrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v)

lemma native_physical_source_eq (r:Source ι a b) (ha:0<a) (hb:0≤b) (D:FixedCubeDatum)
    (ω₁ ω₂:Character) (G L:Id) (B:commonAlloc r G) (E:fullPrimaryAlloc r G B L) (v:ℝ) :
    coloredNativePrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v=
      coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v:=by
  unfold coloredNativePrimaryPhysicalSource coloredPrimaryPhysicalSource
  dsimp only
  apply Finset.sum_congr
  · ext p;simp
  · intro p hp;rfl

lemma unit_scalar_mul {x y:ℂ} (hx:‖x‖≤1) (hy:‖y‖≤1) : ‖x*y‖≤1:=by
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

lemma native_term_norm_le_original (r:Source ι a b) (ha:0<a) (hb:0≤b) (D:FixedCubeDatum)
    (ω₁ ω₂:Character) (G L:Id) (B:commonAlloc r G)
    (aL:Allocation L (Finset.univ:Finset (liveIndices B.val⊕Fin 2)))
    (E:fullPrimaryAlloc r G B L) (v:ℝ) :
    ‖nativePhysicalTerm r ha hb D ω₁ ω₂ G L B aL E v‖^2 ≤
    ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P*
      frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i:liveIndices B.val=>shiftedSlotCoefficient r v i.val)
        (fun i:liveIndices B.val=>r.Wslot i.val) (fun i:liveIndices B.val=>r.P i.val)*
      coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v‖^2 := by
  let phase:ℂ:=(frozenWeight (punctureProduct r.S r.H) B.val*
      TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val)*
    ((frozenWeight (punctureProduct r.S r.H) E.val*allocationTerm L Finset.univ E.val aL*
        idealCoeff D.row.χ (finiteTupleProduct E.val))*
      TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) E.val)
  have hw:‖frozenWeight (punctureProduct r.S r.H) B.val‖≤1:=by
    unfold frozenWeight;split_ifs <;> norm_num
  have hwE:‖frozenWeight (punctureProduct r.S r.H) E.val‖≤1:=by
    unfold frozenWeight;split_ifs <;> norm_num
  have hphaseE:‖frozenWeight (punctureProduct r.S r.H) E.val*
      allocationTerm L Finset.univ E.val aL*idealCoeff D.row.χ (finiteTupleProduct E.val)‖≤1:=
    unit_scalar_mul (unit_scalar_mul hwE
      (MixedSourceAssembly.allocation_term_norm L Finset.univ E.val aL))
      (idealCoeff_norm_le_one D.row.χ (finiteTupleProduct E.val))
  have hp:‖phase‖≤1:=
    unit_scalar_mul (unit_scalar_mul hw (TwistedRawSource.ordinaryColor_norm_le_one ω₁ ω₂ B.val))
      (unit_scalar_mul hphaseE (TwistedRawSource.ordinaryColor_norm_le_one ω₁ ω₂ E.val))
  have heq: nativePhysicalTerm r ha hb D ω₁ ω₂ G L B aL E v=phase*
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P*
      frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i:liveIndices B.val=>shiftedSlotCoefficient r v i.val)
        (fun i:liveIndices B.val=>r.Wslot i.val) (fun i:liveIndices B.val=>r.P i.val)*
      coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v):=by
    unfold nativePhysicalTerm TwistedRawSource.primaryCanonicalScalar
    rw [native_physical_source_eq]
    dsimp only [phase]
    field_simp [live_normalization_ne r G B]
    <;> ring
  rw [heq,norm_mul,mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [norm_nonneg phase])

#print axioms native_term_norm_le_original
end
end QRH.Cycle092.FixedCubeGauss
