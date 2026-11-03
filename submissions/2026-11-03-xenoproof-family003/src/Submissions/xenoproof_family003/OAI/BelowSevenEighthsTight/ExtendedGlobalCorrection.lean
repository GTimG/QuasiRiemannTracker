/- Uses the pinned global correction product and its original CorrectionTail.
   Compilation and replay status are recorded in the verification receipts. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedEulerRegion
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CubicRoot

set_option autoImplicit false
namespace BelowSevenEighthsTight.CorrectionExtension
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbeEuler
open OAI.ActualEisensteinCubic OAI.CompletedGauss
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 13/15≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply BelowSevenEighthsTight.EulerExtension.unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 13/15≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 13/15≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|13/15<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply BelowSevenEighthsTight.EulerExtension.unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 13/15≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply BelowSevenEighthsTight.EulerExtension.unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 13/15≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply BelowSevenEighthsTight.EulerExtension.unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


theorem rational_correction_analytic (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x 1 (1/6))
      {x : ℂ | sigmaRat < x.re} := by
  apply (globalClosedCorrection_analytic_x η S hS 1 (1/6)
    (by norm_num) (by norm_num)).mono
  intro x hx
  exact (show (13/15:ℝ) ≤ sigmaRat by norm_num [sigmaRat]).trans_lt hx

theorem rational_correction_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x : ℂ) (hx : sigmaRat < x.re) :
    ‖globalClosedCorrection η S x 1 (1/6)-1‖ ≤ 1/2 := by
  exact globalClosedCorrection_bound η S hS x 1 (1/6)
    ((show (13/15:ℝ) ≤ sigmaRat by norm_num [sigmaRat]).trans hx.le)
    (by norm_num) (by norm_num)

#print axioms rational_correction_analytic
#print axioms rational_correction_bound

theorem cubic_correction_analytic (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x 1 (1/6))
      {x : ℂ | sigmaRoot < x.re} := by
  apply (globalClosedCorrection_analytic_x η S hS 1 (1/6)
    (by norm_num) (by norm_num)).mono
  intro x hx
  have hs := sigmaRoot_enclosure.1
  exact (show (13/15:ℝ) ≤ sigmaRoot by linarith).trans_lt hx

theorem cubic_correction_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x : ℂ) (hx : sigmaRoot < x.re) :
    ‖globalClosedCorrection η S x 1 (1/6)-1‖ ≤ 1/2 := by
  have hs := sigmaRoot_enclosure.1
  exact globalClosedCorrection_bound η S hS x 1 (1/6)
    ((show (13/15:ℝ) ≤ sigmaRoot by linarith).trans hx.le)
    (by norm_num) (by norm_num)

#print axioms cubic_correction_analytic
#print axioms cubic_correction_bound

theorem exists_uniform_extended_correction (S₀ : Finset Id)
    (hprime : ∀ P ∈ S₀, Prime P) :
    ∃ S : Finset Id, S₀ ⊆ S ∧ (∀ P ∈ S, Prime P) ∧ CorrectionTail S ∧
      ∀ η : HeckeFamily.Character,
        AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x 1 (1/6))
          {x : ℂ | (13/15:ℝ) < x.re} ∧
        ∀ x : ℂ, (13/15:ℝ) < x.re →
          ‖globalClosedCorrection η S x 1 (1/6)-1‖ ≤ 1/2 ∧
          globalClosedCorrection η S x 1 (1/6) ≠ 0 := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  let S := S₀ ∪ smallPrimeSet N
  have hS : CorrectionTail S := by
    apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S,Finset.subset_union_left,?_,hS,?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hp | hp
    · exact hprime P hp
    · exact (Finset.mem_filter.mp hp).2
  · intro η
    refine ⟨globalClosedCorrection_analytic_x η S hS 1 (1/6)
      (by norm_num) (by norm_num),?_⟩
    intro x hx
    have hb := globalClosedCorrection_bound η S hS x 1 (1/6) hx.le
      (by norm_num) (by norm_num)
    refine ⟨hb,?_⟩
    intro hz
    rw [hz] at hb
    norm_num at hb

#print axioms exists_uniform_extended_correction
end
end BelowSevenEighthsTight.CorrectionExtension
