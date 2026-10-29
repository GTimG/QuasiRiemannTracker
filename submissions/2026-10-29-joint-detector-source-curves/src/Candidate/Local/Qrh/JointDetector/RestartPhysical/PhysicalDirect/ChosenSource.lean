/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.ChosenSource (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal initial-energy suppliers on one source, mesh and chosen geometry. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountSource
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.SourceClosure
set_option autoImplicit false
set_option maxHeartbeats 200000
open QRH.Record1252270103Return
namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme:CountScheme] [GenericArithmetic.PhysicalSchedule]
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open Qrh.JointDetector.RestartPhysical.Return.GenericArithmetic
open QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open Cycle25CenteredMomentNaturalFixedRaySource Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Filter

theorem physical_affine_input_of_unit (A : ChosenData) (hgap : theta<HeckeZeroSupremum.beta)
    (hsource : UnitFaceSource physicalFace A.sourceMesh
      ((HeckeZeroSupremum.beta-theta)/10000)) : Source.ActualAffineInput A := by
  obtain ⟨b,hb⟩ := radialMajorant_compact.isCompact.bddAbove
  let bPhi : ℝ := max 2 b
  have hbPhi : 2≤bPhi := le_max_left _ _
  have hsPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi := by
    intro x hx
    exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  let Q := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal A.F
  obtain ⟨degree,controls,C,hC,hbound⟩ := hsource (Fin A.D.N) A.F.modulus ⊤ le_top
    (fun x=>conj (A.F.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (A.F.W.smooth ⊤))
    (Cycle25CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support A.F)
    bPhi hbPhi η η Q
    (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_modulus A.F)
    (internalQ_ne_zero Q (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_zero A.F) η)
    (internalQ_ne_top Q (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_ne_top A.F) η)
    (inf_le_left.trans (Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal_le_72 A.F))
  exact ⟨bPhi,(HeckeZeroSupremum.beta-theta)/10000,by positivity,le_rfl,hsPhi,
    degree,controls,C,hC,hbound⟩

/-- Each requested source error yields a positive mesh before constructing the
finite slot dictionary and the fixed source. Both estimates use its minimum. -/
theorem exists_chosen_initial_source_small_mesh
    (hcap : 2*HeckeZeroSupremum.beta-1≤ scheme.naturalκ)
    (hcount : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧ ∀w∈scheme.windows,UnitFaceSource w.face mesh ε)
    (hphysical : UniformUnitFaceSource physicalFace)
    (hgap : theta<HeckeZeroSupremum.beta) (extraMesh : ℝ) (hExtra : 0<extraMesh) :
    ∃A : ChosenData,A.sourceMesh≤extraMesh ∧
      (∀w∈scheme.windows,LabelInitialMoments A.F w.face A.sourceMesh) ∧ Source.ActualAffineInput A := by
  obtain ⟨physicalMesh,hphysicalMesh,hphysical⟩ := hphysical
    ((HeckeZeroSupremum.beta-theta)/10000) (by positivity)
  have hraw := hcount
  choose rawMesh hrawMesh hrawSource using fun t : {t : ℝ // 0<t}=>hraw t.val t.property
  let mesh : ℝ→ℝ := fun t=>if ht : 0<t then min (rawMesh ⟨t,ht⟩) (min physicalMesh extraMesh) else 1
  have hmesh : ∀t,0<t → 0 < mesh t := by
    intro t ht
    simp only [mesh,dite_eq_left ht]
    exact lt_min (hrawMesh ⟨t,ht⟩) (lt_min hphysicalMesh hExtra)
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hgap hcap mesh hmesh
  have hAraw : A.sourceMesh≤rawMesh ⟨A.D.t,A.D.t_pos⟩ := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact min_le_left _ _
  have hAphysical : A.sourceMesh≤physicalMesh := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hAextra : A.sourceMesh≤extraMesh := by
    rw [hA]
    simp only [mesh,dite_eq_left A.D.t_pos]
    exact (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨A,hAextra,(fun w hw=>QRH.Record1252270103Return.label_initial_moments_of_unit A.F w.face A.sourceMesh
      ((hrawSource ⟨A.D.t,A.D.t_pos⟩ w hw).mono_mesh hAraw)),
    physical_affine_input_of_unit A hgap (hphysical.mono_mesh hAphysical)⟩
theorem chosen_initial_source_of_uniform_faces
    (hcap : 2*HeckeZeroSupremum.beta-1≤ scheme.naturalκ)
    (hcount : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧ ∀w∈scheme.windows,UnitFaceSource w.face mesh ε)
    (hphysical : UniformUnitFaceSource physicalFace) :
    ChosenInitialSourceInput := by
  intro hgap
  obtain ⟨A,_,hA⟩ := exists_chosen_initial_source_small_mesh hcap hcount hphysical hgap 1 (by norm_num)
  exact ⟨A,hA⟩
end
end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
