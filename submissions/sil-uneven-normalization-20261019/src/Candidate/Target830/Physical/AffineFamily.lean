/- Genuine finite affine-source family, preserving original selected products.
Predecessor OpenAI/Hailey Collet/DaysSky attribution; Apache-2.0. -/
import Candidate.Target830.Physical.AffineInput
import Candidate.Target836.Target836InitialSupplier

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Physical.InitialTransport
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
open Cycle25ProbeFinalAssembly Cycle25ProbeFinalAssemblyCertifiedBands

/-- Capacity inclusion is anchored at the ACTUAL .034 selected-product width. -/
theorem pr62_field_to_fine {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (P : Count.Plane) (hP : P=.PR62 ∨ P=.oldWeak)
    (hin : Target836InitialTransport.weighted_AffineFineInput836 S) :
    weighted_AffineFineInputAt P S := by
  intro η
  obtain ⟨J,C,hC,hev⟩ := hin η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ts T allowance i B hsub hdata hp hw hu he bin label l r hne
    height hh hex hmlo hmhi selected hsel h1 h2 hcap j k hj σ hσ t ht
  have hm0 : 41/100 ≤ (B.fiber bin label l r hne).m :=
    (Count.plane_plain_window P).1.le.trans hmlo
  have hm1 : (B.fiber bin label l r hne).m ≤ 44/100 :=
    by
      convert hmhi.trans (Count.plane_plain_window P).2.le using 1 <;> norm_num [plainUpper]
  have hc : 2*(B.fiber bin label l r hne).m+
      Detector836.lam*(∑s∈selected,(B.fiber bin label l r hne).widths s) ≤ Detector836.Bc := by
    rcases hP with hP|hP <;> subst P
    · simpa only [Count.Plane.lambda,Count.Plane.B,Detector836.lam,Detector836.Bc] using hcap
    · norm_num [Count.Plane.lambda,Count.Plane.B,Detector836.lam,Detector836.Bc,widthLower] at hcap h1 ⊢
      linarith only [hcap,h1]
  exact hz.2 rows hrows d hd a ts T allowance i B hsub hdata hp hw hu he
    bin label l r hne height hh hex selected hsel hm0 hm1 h1 h2 hc j k hj σ hσ t ht

theorem pr60_field_to_fine {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hin : weighted_AffineFineInput S) : weighted_AffineFineInputAt .PR60 S := by
  intro η
  obtain ⟨J,C,hC,hev⟩ := hin η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ts T allowance i B hsub hdata hp hw hu he bin label l r hne
    height hh hex hmlo hmhi selected hsel h1 h2 hcap j k hj σ hσ t ht
  have hm0 : 41/100 ≤ (B.fiber bin label l r hne).m :=
    (Count.plane_plain_window .PR60).1.le.trans hmlo
  have hm1 : (B.fiber bin label l r hne).m ≤ 44/100 :=
    by
      convert hmhi.trans (Count.plane_plain_window .PR60).2.le using 1 <;> norm_num [plainUpper]
  have hc : 2*(B.fiber bin label l r hne).m+
      DetectorAffine.lam*(∑s∈selected,(B.fiber bin label l r hne).widths s) ≤ DetectorAffine.Bc := by
    simpa only [Count.Plane.lambda,Count.Plane.B,DetectorAffine.lam,DetectorAffine.Bc] using hcap
  exact hz.2 rows hrows d hd a ts T allowance i B hsub hdata hp hw hu he
    bin label l r hne height hh hex selected hsel hm0 hm1 h1 h2 hc j k hj σ hσ t ht

/-- All five bounds hold for the SAME source and selected-product coefficients.
The finite family is assembled before all moving rows and heights. -/
theorem actual_five_plane_fields {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hfine : ∀j,D.ell j≤DetectorAffine.detectorMesh D.t/200)
    (newMesh : ℝ) (hmesh : 0<newMesh) (hnewfine : ∀j,D.ell j≤newMesh/200)
    (hlabels : ∀P : SourcePlane,LabelInitialMoments P S newMesh) :
    ∀P : Count.Plane, weighted_AffineFineInputAt P S := by
  have h62 := Target836InitialSupplier.actual_detector_affine_input S hβlo hβhi hfine
  have h60 := Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input S hβlo hβhi hfine
  intro P
  cases P with
  | PR62 => exact pr62_field_to_fine S .PR62 (Or.inl rfl) h62
  | PR60 => exact pr60_field_to_fine S h60
  | A => exact actual_detector_affine_input_of_initial .A S newMesh hmesh hnewfine (hlabels .A)
  | C => exact actual_detector_affine_input_of_initial .C S newMesh hmesh hnewfine (hlabels .C)
  | oldWeak => exact pr62_field_to_fine S .oldWeak (Or.inr rfl) h62

end
end OAI.SevenEighths.Target830.Physical.InitialTransport
#print axioms OAI.SevenEighths.Target830.Physical.InitialTransport.actual_five_plane_fields
