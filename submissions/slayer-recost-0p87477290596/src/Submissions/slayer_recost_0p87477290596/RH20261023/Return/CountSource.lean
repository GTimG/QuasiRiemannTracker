/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Source-to-detector transport preserves literal coefficients and full rows. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Count.InitialTransport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record12518109Count
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalFixedRaySource Cycle25ProbeFinalAssembly CenteredMomentDetectorDictionary

/-- The initial source is used with the row label's actual inducing character.
The mesh precedes labels, row parameters and all independent heights. -/
theorem label_initial_moments_of_unit {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (face : SourceFace) (mesh : ℝ)
    (hsource : UnitFaceSource face mesh D.t) : LabelInitialMoments F face mesh := by
  intro η bPhi hbPhi label
  let etaL := sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  let Q := Cycle25CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F
  exact hsource (Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (F.W.smooth ⊤))
    (Cycle25CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support F)
    bPhi hbPhi etaL etaL Q
    (Cycle25CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_modulus F)
    (internalQ_ne_zero Q (Cycle25CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_zero F) etaL)
    (internalQ_ne_top Q (Cycle25CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_ne_top F) etaL)
    (inf_le_left.trans (Cycle25CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal_le_72 F))

/-- A genuine global ordinary source supplies the actual cardinality fiber
moment after source dictionary transport, with one finite all-height degree. -/
theorem detector_affine_of_unit {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (face : SourceFace) (hplain : face.plainHi≤1/2)
    (mesh : ℝ) (hmesh : 0<mesh) (hfine : ∀j,D.ell j≤mesh/200)
    (hsource : UnitFaceSource face mesh D.t) : WeightedAffineFineInput F face :=
  actual_detector_affine_input_of_initial F face hplain mesh hmesh hfine
    (label_initial_moments_of_unit F face mesh hsource)
end
end QRH.RH20261023Return
#print axioms QRH.RH20261023Return.label_initial_moments_of_unit
#print axioms QRH.RH20261023Return.detector_affine_of_unit
