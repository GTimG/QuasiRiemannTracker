import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRowCountGeometry

/- Scalar capacity budgets for the retuned crossing. These do not assert
   that any analytic moment estimate is available at the requested capacity. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.FiberExtension
noncomputable section
open OAI.SevenEighths.HeckeDetectorBranchBudget

theorem plain_marked_loss (m δ x capacity ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(6*capacity)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(6*capacity)+commonLoss ε εm mesh ν := by
  have h := OAI.SevenEighths.HeckeDetectorBranchBudget.plain_marked_loss
    m δ x ((capacity-3/4)/2) ε εm mesh ν hδ hδ1 hx hx1 hε hmesh hν
  have he : (9/2:ℝ)+12*((capacity-3/4)/2)=6*capacity := by ring
  rwa [he] at h

theorem plain_requested_capacity (c capacity x t r m ε ν : ℝ)
    (hc : 4/9≤c) (hcu : c≤6/13) (hcapacity : 13/18≤capacity)
    (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤RowCountExtension.crossing c x t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*capacity)) :
    0≤(1-2*m)/(6*capacity)-ν ∧ (1-2*m)/(6*capacity)-ν≤7/37 ∧
      2*m+6*capacity*((1-2*m)/(6*capacity)-ν)≤1 := by
  have hcross := RowCountExtension.crossing_bounds hc hcu hx hx1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<6*capacity := by linarith
  have hcap : (1-2*m)/(6*capacity)≤7/37 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  rw [mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

#print axioms plain_marked_loss
#print axioms plain_requested_capacity
end
end BelowSevenEighthsTight.FiberExtension
