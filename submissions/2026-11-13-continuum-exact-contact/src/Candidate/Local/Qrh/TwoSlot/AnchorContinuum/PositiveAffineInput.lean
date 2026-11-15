/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Literal physical initial energy at an explicit source face. The character,
conjugated profile, fixed ideal and natural-zero contract are unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveChosenData
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.ChosenSource

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical ComplexConjugate
open Filter
open QRH.Record1252270103Return
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalFixedRaySource
open Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- Same affine specialization as the inherited physical input, with its
source face explicit instead of read from a fixed physical schedule. -/
def affineAtFace (face : SourceFace) (A : ChosenData)
    (bPhi error U : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  InitialAffineAt (α := Fin A.D.N) A.F.modulus ⊤ le_top face
    (fun x => conj (A.F.W x)) 2 (1/4) (9/4) bPhi A.sourceMesh (33/50) (33/50) 1 1 error U
    η η (weighted_sourceFixedIdeal A.F) degree control C

/-- Genuine unit-face moments give the actual reflected physical initial
energy, on the chosen early mesh and with constants preceding the height. -/
theorem affine_input_of_unit (face : SourceFace) (A : ChosenData) {error : ℝ}
    (hsource : UnitFaceSource face A.sourceMesh error) :
    ∃ bPhi : ℝ, ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ,
      0 < C ∧ Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi ∧
      ∀ᶠ U : ℝ in atTop, affineAtFace face A bPhi error U degree control C := by
  obtain ⟨b,hb⟩ := radialMajorant_compact.isCompact.bddAbove
  let bPhi : ℝ := max 2 b
  have hbPhi : 2 ≤ bPhi := le_max_left _ _
  have hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi := by
    intro x hx
    exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  let Q := weighted_sourceFixedIdeal A.F
  obtain ⟨degree,controls,C,hC,hbound⟩ := hsource (Fin A.D.N) A.F.modulus ⊤ le_top
    (fun x => conj (A.F.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (A.F.W.smooth ⊤))
    (Cycle25CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support A.F)
    bPhi hbPhi η η Q (weighted_sourceFixedIdeal_le_modulus A.F)
    (internalQ_ne_zero Q (weighted_sourceFixedIdeal_ne_zero A.F) η)
    (internalQ_ne_top Q (weighted_sourceFixedIdeal_ne_top A.F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 A.F))
  exact ⟨bPhi,degree,controls,C,hC,hsPhi,hbound⟩

def actualInputAtFace (face : SourceFace) (A : ChosenData) : Prop :=
  ∃ bPhi error : ℝ, 0 < error ∧ error ≤ (HeckeZeroSupremum.beta-Geometry.theta)/10000 ∧
    Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi ∧
    ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, affineAtFace face A bPhi error U degree control C

/-- Specializing the explicit face recovers the existing analytic contract
definitionally, including all masks, profiles and zero extensions. -/
theorem actual_input_compat
    [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
    [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]
    (A : ChosenData) : actualInputAtFace physicalFace A ↔ Source.ActualAffineInput A := by
  rfl

/-- Both count suppliers and the physical initial energy share one source and
one early mesh. The extension and fee budgets precede all character and height
choices, and the physical source face is explicit. -/
theorem exists_initial_sources_with_costs
    [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
    (face : SourceFace)
    (hcap : 2*HeckeZeroSupremum.beta-1 ≤ scheme.naturalκ)
    (hcount : ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
      ∀ w ∈ scheme.windows, UnitFaceSource w.face mesh ε)
    (hphysical : UniformUnitFaceSource face)
    (himp : Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedFiberMoments line)
    (hgap : Geometry.theta < HeckeZeroSupremum.beta)
    {Δ fee extraMesh : ℝ} (hΔ : 0 < Δ) (hfee : 0 < fee) (hExtra : 0 < extraMesh) :
    ∃ A : ChosenData, A.sourceMesh ≤ extraMesh ∧ A.D.t ≤ Δ/4 ∧
      Δ/2+2*A.D.t ≤ Δ ∧ 159*A.D.ε+609*A.D.t ≤ fee/4 ∧
      (∀ w ∈ scheme.windows, LabelInitialMoments A.F w.face A.sourceMesh) ∧
      Qrh.TwoSlot.AnchorZeroLoss.Affine.ImprovedFineInput line A.F ∧ actualInputAtFace face A := by
  have herr : 0 < (HeckeZeroSupremum.beta-Geometry.theta)/10000 := by positivity
  obtain ⟨physicalMesh,hphysicalMesh,hphysical⟩ := hphysical _ herr
  choose rawMesh hrawMesh hrawSource using fun t : {t : ℝ // 0 < t} => hcount t.val t.property
  choose impMesh himpMesh himpSource using fun t : {t : ℝ // 0 < t} => himp t.val t.property
  let mesh : ℝ → ℝ := fun t => if ht : 0 < t then
    min (rawMesh ⟨t,ht⟩) (min (impMesh ⟨t,ht⟩) (min physicalMesh extraMesh)) else 1
  have hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t := by
    intro t ht
    simp only [mesh,dite_eq_left ht]
    exact lt_min (hrawMesh ⟨t,ht⟩) (lt_min (himpMesh ⟨t,ht⟩) (lt_min hphysicalMesh hExtra))
  obtain ⟨A,hA,ht,hpad,hbudget⟩ := exists_chosen_with_costs hgap hcap hΔ hfee mesh hmesh
  have hraw : A.sourceMesh ≤ rawMesh ⟨A.D.t,A.D.t_pos⟩ := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact min_le_left _ _
  have himproved : A.sourceMesh ≤ impMesh ⟨A.D.t,A.D.t_pos⟩ := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hphys : A.sourceMesh ≤ physicalMesh := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hextra : A.sourceMesh ≤ extraMesh := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfine : ∀ j, A.D.length j ≤ impMesh ⟨A.D.t,A.D.t_pos⟩/200 := fun j =>
    (A.source_fine j).trans (div_le_div_of_nonneg_right himproved (by norm_num))
  obtain ⟨bPhi,degree,control,C,hC,hsPhi,hbound⟩ :=
    affine_input_of_unit face A (hphysical.mono_mesh hphys)
  exact ⟨A,hextra,ht,hpad,hbudget,
    (fun w hw => QRH.Record1252270103Return.label_initial_moments_of_unit A.F w.face A.sourceMesh
      ((hrawSource ⟨A.D.t,A.D.t_pos⟩ w hw).mono_mesh hraw)),
    himpSource ⟨A.D.t,A.D.t_pos⟩ A.F rfl hfine,
    bPhi,(HeckeZeroSupremum.beta-Geometry.theta)/10000,herr,le_rfl,hsPhi,
    degree,control,C,hC,hbound⟩

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.affine_input_of_unit
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.actual_input_compat
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.exists_initial_sources_with_costs
