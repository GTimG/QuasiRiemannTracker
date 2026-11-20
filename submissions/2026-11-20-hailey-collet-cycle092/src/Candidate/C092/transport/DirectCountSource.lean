/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual count-fiber source via Collet's source/detector dictionary and Joseph
Bebel's coupled positive source. Both original licenses remain Apache-2.0. -/
import Candidate.C092.PhysicalInlet
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountSource
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace QRH.Cycle092.DirectCount
open OAI.SevenEighths
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record1252270103Return QRH.Record12518109Count
open Cycle25ProbeFinalAssembly

/-- The authentic count cap retains the coupled positive-source collar. -/
def countFace : SourceFace :=
  Qrh.TwoSlot.AnchorContinuum.PositiveSource.face QRH.Cycle090.sourceCost

/-- The original count source is proved, not an additional analytic premise. -/
theorem q_count_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    UniformUnitFaceSource countFace := by
  apply Qrh.TwoSlot.AnchorContinuum.PositiveSource.source QRH.Cycle090.allowances_pos.1 _ hβ
  linarith [QRH.Cycle090.sourceCost_le_rowPad,QRH.Cycle090.rowPad_small]

/-- A positive mesh function may be supplied to the authentic D/F constructor.
For each t its choice precedes all source labels, rows, heights and fibers. -/
theorem q_count_mesh (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
      ∀ (D : Cycle25.Weighted.MomentData) (F : WeightedSourceData D),
        (∀ j, D.ell j ≤ mesh D.t/200) → WeightedAffineFineInput F countFace := by
  have hs := q_count_source hβ
  choose mesh hm hsource using (fun t : {t : ℝ // 0 < t} => hs t.val t.property)
  let chosen : ℝ → ℝ := fun t => if ht : 0 < t then mesh ⟨t,ht⟩ else 1
  refine ⟨chosen,?_,?_⟩
  · intro t ht
    simpa only [chosen,dite_eq_left ht] using hm ⟨t,ht⟩
  · intro D F hfine
    have ht : 0 < D.t := D.t_pos
    have hm' : 0 < mesh ⟨D.t,ht⟩ := hm ⟨D.t,ht⟩
    have hfine' : ∀ j, D.ell j ≤ mesh ⟨D.t,ht⟩/200 := by
      simpa only [chosen,dite_eq_left ht] using hfine
    exact detector_affine_of_unit F countFace (by rfl) _ hm' hfine' (hsource ⟨D.t,ht⟩)

end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.q_count_source
#print axioms QRH.Cycle092.DirectCount.q_count_mesh
