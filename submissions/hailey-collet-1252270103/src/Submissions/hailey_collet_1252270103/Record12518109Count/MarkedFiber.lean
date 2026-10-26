/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from Gao's Target830/Count/MarkedFiber.lean, with variable source
faces and requested width. The count is the actual cardinality of F.rows. -/
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Moments
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment
import Submissions.hailey_collet_1252270103.Record12518109Count.Arithmetic
set_option autoImplicit false
namespace QRH.Record12518109Count
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorPlainFiberCount
open QRH.Record12518109Source
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The literal selected-product second moment on one fixed supported-witness
fiber. Source-to-detector coefficient transport must supply this estimate. -/
def AffineMarkedMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (f : SourceFace) (C height εm : ℝ) : Prop :=
  f.plainLo ≤ F.m → F.m ≤ f.plainHi →
  ∀ selected : Finset Slot, selected ⊆ F.slots →
    f.slotLo ≤ (∑ s∈selected,F.widths s) →
    (∑ s∈selected,F.widths s) ≤ f.slotHi →
    2*F.m+f.lam*(∑ s∈selected,F.widths s) ≤ f.B →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (-height) height,
      ∑ u∈F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2 ≤ C*U^(1+εm)

theorem affine_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (f : SourceFace) {κplain c κinverse C height εm z : ℝ}
    (moments : Cycle25DetectorRawFiber.Moments F κplain c κinverse C height εm)
    (affine : AffineMarkedMoment F f C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hk : 0 ≤ κplain)
    (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height)
    (hm : F.m < 1/2) (hmlo : f.plainLo ≤ F.m) (hmhi : F.m ≤ f.plainHi)
    (hnatural : 2*F.m+6*κplain*f.slotLo ≤ 1)
    (hl : 0 < f.lam) (hzpos : 0 < z) (hzmax : z ≤ 7/37)
    (hzface : z ≤ f.slotHi) (hzbudget : f.lam*z ≤ f.B-2*F.m) :
    (F.rows.card:ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  let κ' := (1-2*F.m)/(6*z)
  have hκ'0 : 0 ≤ κ' := div_nonneg (by linarith) (by positivity)
  have he : 6*κ'*z=1-2*F.m := by dsimp [κ']; field_simp
  have hraw : ∀ selected : Finset Slot, selected ⊆ F.slots →
      2*F.m+6*κ'*(∑ s∈selected,F.widths s) ≤ 1 →
      ∀ j k : ℕ,j+k ≤ 2 → ∀ s∈Icc (0:ℝ) 1,∀ t∈Icc (-height) height,
        ∑ u∈F.rows, ‖polynomial (F.family u F.label) false
          ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
          polynomial (F.family u F.label) false
          ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
            F.physicalProduct selected u‖^2 ≤ C*U^(1+εm) := by
    intro selected hsel hc
    have hsum : (∑ s∈selected,F.widths s) ≤ z := by
      have he' : 6*κ'=(1-2*F.m)/z := by dsimp [κ']; field_simp
      have h1 : (1-2*F.m)/z*(∑ s∈selected,F.widths s) ≤ 1-2*F.m := by
        rw [←he']; linarith
      have hpos : 0 < 1-2*F.m := by linarith
      rw [div_mul_eq_mul_div,div_le_iff₀ hzpos] at h1
      nlinarith
    by_cases hsmall : (∑ s∈selected,F.widths s) < f.slotLo
    · apply moments.plain_marked selected hsel
      have hs := mul_le_mul_of_nonneg_left hsmall.le
        (show (0:ℝ) ≤ 6*κplain by positivity)
      linarith
    · apply affine hmlo hmhi selected hsel (le_of_not_gt hsmall) (hsum.trans hzface)
      have h2 := mul_le_mul_of_nonneg_left hsum hl.le
      linarith
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κ' εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hzpos.le (hzmax.trans F.supply) F.fixed_bin hκ'0 hC hh hf (by change 2*F.m+6*κ'*z ≤ 1; linarith) hraw
end
end QRH.Record12518109Count
#print axioms QRH.Record12518109Count.affine_marked_count
