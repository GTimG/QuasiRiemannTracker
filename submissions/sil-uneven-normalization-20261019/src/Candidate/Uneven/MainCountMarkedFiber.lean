/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountParameters
import Candidate.Uneven.MainInitialContract
import Candidate.Target836.Detector836.Count

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.MainCount
noncomputable section
open Target830
open Sil.Uneven.MainSource
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles HeckeDetectorPlainFiberCount Cycle25DetectorRawFiber

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The actual selected-product moment for one fixed detector fiber. The
source supplier must discharge this predicate on its own plain window. -/
def AffineMarkedMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (P : Plane) (C height εm : ℝ) : Prop :=
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    widthLower ≤ (∑ s∈selected,F.widths s) →
    (∑ s∈selected,F.widths s) ≤ widthUpper →
    2*F.m+P.lambda*(∑ s∈selected,F.widths s) ≤ P.B →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

theorem plane_lambda_pos (P : Plane) : 0 < P.lambda := by
  cases P <;> norm_num [OAI.SevenEighths.MainCount.Plane.lambda]

def lowerPlain (P : Plane) : ℝ := (P.B-P.lambda*widthUpper)/2

theorem plane_plain_window (P : Plane) :
    41/100 < lowerPlain P ∧ mHi < MainInitial.plainUpper := by
  cases P <;> norm_num [lowerPlain,OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,widthUpper,mHi,Target830.Count.mHi,kappa0,widthLower,MainInitial.plainUpper]

/-- Genuine fiber count from the affine selected-product moment. The
requested capacity buffer is arbitrary and positive margins stay explicit;
there is no inherited hardcoded .001 buffer. -/
theorem affine_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (P : Plane) {κplain c κinverse C height εm ν : ℝ}
    (moments : Cycle25DetectorRawFiber.Moments F κplain c κinverse C height εm)
    (affine : AffineMarkedMoment F P C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hk : 7/10 ≤ κplain) (hkhi : κplain ≤ kappa0)
    (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height)
    (hν : 0 ≤ ν) (hmhi : F.m ≤ mHi)
    (hcaplo : widthLower ≤ (P.B-2*F.m)/P.lambda-ν)
    (hcaphi : (P.B-2*F.m)/P.lambda ≤ widthUpper) :
    (F.rows.card:ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*((P.B-2*F.m)/P.lambda-ν)+
        4*ε+(2*a-1)*F.mesh+εm) := by
  let z := (P.B-2*F.m)/P.lambda-ν
  have hl := plane_lambda_pos P
  have hm2 : F.m < 1/2 := by norm_num [mHi,Target830.Count.mHi,kappa0,widthLower] at hmhi ⊢;linarith
  have hzA : (P.B-2*F.m)/P.lambda ≤ widthUpper := hcaphi
  have hz : 0 ≤ z := by dsimp [z];norm_num [widthLower] at hcaplo;linarith
  have hzpos : 0 < z := by dsimp [z];norm_num [widthLower] at hcaplo;linarith
  have hz' : z ≤ 7/37 := by dsimp [z];norm_num [widthUpper] at hzA;linarith
  let κ' := (1-2*F.m)/(6*z)
  have hκ'0 : 0 ≤ κ' := div_nonneg (by linarith) (by positivity)
  have hcap : 2*F.m+6*κ'*z ≤ 1 := by
    have he : 6*κ'*z=1-2*F.m := by dsimp [κ'];field_simp
    linarith
  have hraw : ∀ selected : Finset Slot, selected ⊆ F.slots →
      2*F.m+6*κ'*(∑ s∈selected,F.widths s) ≤ 1 →
      ∀ j k : ℕ,j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1,∀ t∈Icc (-height) height,
        ∑ u∈F.rows, ‖polynomial (F.family u F.label) false
          ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
          polynomial (F.family u F.label) false
          ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
            F.physicalProduct selected u‖^2 ≤ C*U^(1+εm) := by
    intro selected hsel hc
    have hw0 : 0 ≤ ∑ s∈selected,F.widths s :=
      Finset.sum_nonneg (fun s hs => (F.widths_pos s (hsel hs)).le)
    have hsum : (∑ s∈selected,F.widths s) ≤ z := by
      have he : 6*κ'=(1-2*F.m)/z := by dsimp [κ'];field_simp
      have h1 : (1-2*F.m)/z*(∑ s∈selected,F.widths s) ≤ 1-2*F.m := by
        rw [←he];linarith
      have hpos : 0 < 1-2*F.m := by linarith
      rw [div_mul_eq_mul_div,div_le_iff₀ hzpos] at h1
      nlinarith
    by_cases hsmall : (∑ s∈selected,F.widths s) < widthLower
    · apply moments.plain_marked selected hsel
      have hs := mul_le_mul_of_nonneg_left hsmall.le
        (show (0:ℝ) ≤ 6*κplain by linarith)
      have hκ := mul_le_mul_of_nonneg_right hkhi
        (show (0:ℝ) ≤ 6*widthLower by norm_num [widthLower])
      norm_num [mHi,Target830.Count.mHi,kappa0,widthLower] at hmhi hs hκ ⊢
      linarith
    · apply affine selected hsel (le_of_not_gt hsmall)
        (by dsimp [z] at hsum;linarith) 
      have h2 := mul_le_mul_of_nonneg_left hsum hl.le
      have h3 : P.lambda*z ≤ P.B-2*F.m := by
        dsimp [z]
        rw [mul_sub,mul_div_cancel₀ _ hl.ne']
        nlinarith
      linarith
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κ' εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hκ'0 hC hh hf hcap hraw

/-- Uniform convenience wrapper on the actual plain window. The tiny
positive count buffer is chosen before moving fibers. -/
theorem affine_marked_count_on_window
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (P : Plane)
    {κplain c κinverse C height εm ν : ℝ}
    (moments : Cycle25DetectorRawFiber.Moments F κplain c κinverse C height εm)
    (affine : AffineMarkedMoment F P C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hk : 7/10 ≤ κplain) (hkhi : κplain ≤ kappa0)
    (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height)
    (hν : 0 ≤ ν) (hνhi : ν ≤ 1/100000)
    (hmlo : lowerPlain P ≤ F.m) (hmhi : F.m ≤ mHi) :
    (F.rows.card:ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*((P.B-2*F.m)/P.lambda-ν)+
        4*ε+(2*a-1)*F.mesh+εm) := by
  have hl := plane_lambda_pos P
  have hcaplo : widthLower ≤ (P.B-2*F.m)/P.lambda-ν := by
    rw [le_sub_iff_add_le,le_div_iff₀ hl]
    cases P <;> norm_num [OAI.SevenEighths.MainCount.Plane.B,OAI.SevenEighths.MainCount.Plane.lambda,
      mHi,Target830.Count.mHi,kappa0,widthLower] at hmhi ⊢ <;> nlinarith
  have hcaphi : (P.B-2*F.m)/P.lambda ≤ widthUpper := by
    rw [div_le_iff₀ hl]
    unfold lowerPlain at hmlo
    linarith
  exact affine_marked_count F P moments affine hU ha hk hkhi hC hh hf hν hmhi hcaplo hcaphi

end
end OAI.SevenEighths.MainCount
