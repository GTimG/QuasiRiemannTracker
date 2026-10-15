/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B024
import Submissions.gao_cycle61_plane_20261013.Bundles.B031
import Submissions.gao_cycle61_plane_20261013.Bundles.B032
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductX
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalContours
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalTransport

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderFiniteProduct; sha256 595a0ab19d0a00dc3c873068c8ea5fe4439941be74b9a913f643d4464c274a36 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                          
                                                
                                                               
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace Cycle61.Transport.PrincipalFiniteProduct
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeFiniteProductBounds
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (remainder_idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith [Cycle61.Transport.theta_bounds] : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith [Cycle61.Transport.theta_bounds])

lemma marked_differentiableAt_w (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := remainder_unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := remainder_unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : theta ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith [Cycle61.Transport.theta_bounds]
  have hQ1 : 1 ≤ Q := by linarith [Cycle61.Transport.theta_bounds]
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith [Cycle61.Transport.theta_bounds]))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [Cycle61.Transport.theta_bounds])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [Cycle61.Transport.theta_bounds] : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith [Cycle61.Transport.theta_bounds]))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [Cycle61.Transport.theta_bounds] : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith [Cycle61.Transport.theta_bounds]

lemma localBound_nonneg (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (theta) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith [Cycle61.Transport.theta_bounds]
  have hQ1 : 1 ≤ Q := by linarith [Cycle61.Transport.theta_bounds]
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [Cycle61.Transport.theta_bounds] : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [Cycle61.Transport.theta_bounds, hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [Cycle61.Transport.theta_bounds, hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound η S hS P hP x w z hx.1 (by linarith [Cycle61.Transport.theta_bounds]) (by linarith [Cycle61.Transport.theta_bounds, hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

theorem slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (theta) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := remainder_globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (remainder_globalClosedCorrection_analytic_w η S hS x z hx hz).mul (slot_analytic_w η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : theta ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (remainder_globalClosedCorrection_analytic_z η S hS x w hx hw).mul (slot_analytic_z η S hS J T b hT x w hx hw)

theorem combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (theta) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS x w z hx.1 (by linarith [Cycle61.Transport.theta_bounds]) (by linarith [Cycle61.Transport.theta_bounds, hz.1]))
    (slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : theta ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1<cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith [Cycle61.Transport.theta_bounds])).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : theta ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : theta ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem local_eq_regionSlot (η : Character) (P : PrimeIdeal) (s w z : ℂ) :
    localMultiplier η P s w z = (Ideal.absNorm P.val : ℂ)^(z-1) *
      PrincipalSlotEstimate.regionSlot (Ideal.absNorm P.val)
        (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s w z := by
  simp only [localMultiplier,PrincipalSlotEstimate.regionSlot,PrincipalSlotEstimate.regionReplacement,
    PrincipalSlotEstimate.regionMarked,idealMarkedClosed,idealClosedCorrection,Complex.ofReal_natCast]

theorem window_at_residue {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) :
    windowMultiplier η J T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      ∏ j ∈ J, ∑ P ∈ T j,
        ((W j ((Ideal.absNorm P.val : ℝ)/scale j) *
          (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ)) : ℝ) : ℂ) *
        PrincipalSlotEstimate.principalSlot (Ideal.absNorm P.val)
          (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s := by
  unfold windowMultiplier slotMultiplier
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro P hp
  rw [local_eq_regionSlot,PrincipalSlotEstimate.region_slot_at_residue]
  have hQ : 0 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hQ.le]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num
  ring_nf

theorem slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : theta ≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(theta : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using Cycle61.Transport.PrincipalSlots.weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : theta ≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(theta : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS s w z hs (by linarith [Cycle61.Transport.theta_bounds]) (by linarith [Cycle61.Transport.theta_bounds]))
    (slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : Character) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

lemma boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

end Cycle61.Transport.PrincipalFiniteProduct
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderFiniteProduct -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderFiniteProductX; sha256 c5a68546bbf655ec27b7bd8364defde2a178d98ca66fb449b56c7c7f8da42c43 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                                 
                                                          
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace Cycle61.Transport.PrincipalFiniteProductX
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
open Cycle61.Transport.PrincipalFiniteProduct
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | theta < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Cycle61.Transport.theta_bounds]
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := remainder_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | theta < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (theta : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (theta : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (remainder_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : theta < a) (hβ : HeckeZeroSupremum.beta<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

end Cycle61.Transport.PrincipalFiniteProductX
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderFiniteProductX -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderContours; sha256 a32ba364e4cdee8178342b24e21380a31bea0c094a132c37d57475530ad38cb4 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                                  
                                                             
noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Cycle61.Transport.PrincipalContours
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalFiniteProductX
local notation "Id" => Ideal ActualEisensteinCubic.O
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0<Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => ideal_correction_measurable η P.val x w z hx hw hz)

lemma local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (local_multiplier_measurable η P x w z hx hw hz)

lemma zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0 ≤ zBoxAmplitude M Bz := by
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖ ≤ zBoxAmplitude M Bz*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ) ≤ (6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖ ≤ max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ) ≤ max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1 ≤ max 6 (6*Bz+1) := (by linarith [Cycle61.Transport.theta_bounds, hξ.2] : 6*ξ+1 ≤ 6*Bz+1).trans (le_max_right _ _)
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero,add_zero]
    rw [abs_of_pos (by linarith [Cycle61.Transport.theta_bounds, hξ.1] : 0<6*ξ+1),abs_mul]
    norm_num
    unfold height
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg t)]
  have hi : |(6*((ξ:ℂ)+t*I) : ℂ).im|=6*|t| := by simp [abs_mul]
  have ht : (3+6*|t|)^2 ≤ 36*height t^2 := by
    have hh : 3+6*|t| ≤ 6*height t := by unfold height; linarith [Cycle61.Transport.theta_bounds]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have hmax : 0 ≤ max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _  ≤  principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _  ≤  principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta<a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ ≤ ‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖ ≤ A) :
    ‖LFunction χ s‖ ≤ A/δ := by
  apply (le_div_iff₀ hδ).mpr
  calc
    _  ≤  ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _  ≤  A := hA

lemma fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1<cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖ ≤ 
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖ ≤ 
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1| ≤ ‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

lemma arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0<boxScale X Y Z a Bs Bz cw := by
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma height_le_joint_s (t v u : ℝ) : height t ≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma height_le_joint_z (t v u : ℝ) : height v ≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma height_le_joint_w (t v u : ℝ) : height u ≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0 ≤ C) (hR : ∀s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw ≤ ‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz ≤ ‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ ≤ 
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ ≤ C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := Cycle61.Transport.PrincipalFiniteProduct.combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith [Cycle61.Transport.theta_bounds]
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith [Cycle61.Transport.theta_bounds]
  have hlz0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖ ≤ 
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖ ≤ 
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ) ≤ 3/2) (Cycle61.Transport.PrincipalFiniteProduct.slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _  ≤  scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _  ≤  scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0 ≤ C) (hR : ∀s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ ≤ 
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  apply arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith [Cycle61.Transport.theta_bounds]) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith [Cycle61.Transport.theta_bounds]) hξ1 (by linarith [Cycle61.Transport.theta_bounds, hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  filter_upwards [outer_height_ne_zero_ae] with p hp
  apply Cycle61.Transport.PrincipalFiniteProductX.continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  apply (continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  dsimp only
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1<cw) (hC : 0 ≤ C) (hw : 0 ≤ δw) (hz : 0 ≤ δz) :
    0 ≤ arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (boxScale_pos X Y Z a Bs Bz cw).le
  have hb := Cycle61.Transport.PrincipalFiniteProduct.slotBound_nonneg J T b Bs Bz
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0<K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤ 
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith [Cycle61.Transport.theta_bounds]) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith [Cycle61.Transport.theta_bounds]) hξ1 (by linarith [Cycle61.Transport.theta_bounds, hυ.1]) hυ1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,arithmetic_profile_eq_source] using hh

theorem source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  obtain ⟨C,K,hC,hK,hslice⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [Cycle61.Transport.theta_bounds]
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,Cycle61.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : theta  ≤  s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0<e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (Cycle61.Transport.PrincipalFiniteProduct.slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (Cycle61.Transport.PrincipalFiniteProduct.combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using Cycle61.Transport.PrincipalFiniteProduct.combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (theta : ℝ) ≤ (((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (Cycle61.Transport.PrincipalFiniteProduct.source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith [Cycle61.Transport.theta_bounds])).mono
    intro w hw
    change (9/10 : ℝ)<w.re
    linarith [hw.1]
  · intro z hz
    have hh := Cycle61.Transport.PrincipalFiniteProduct.source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith [Cycle61.Transport.theta_bounds]) hη hcw
    convert Cycle61.Transport.PrincipalFiniteProduct.boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (Cycle61.Transport.PrincipalFiniteProduct.source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)<z.re
    linarith [hz.1]
  · exact hzb
  · exact source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
    ∀ᵐt : ℝ, let s : ℂ := (a:ℂ)+t*I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1/6+e) (fun z => verticalIntegral cw
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
      HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
      (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (hβ : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hH := global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun q : ℝ×ℝ => 6*q.2))
  have hL' : Measurable (fun q : ℝ×ℝ => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+q.2*I))) := by
    convert hL using 1
    funext q
    congr 1
    push_cast
    ring
  unfold residueArithmetic
  fun_prop (disch := aesop)

lemma residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0<X) (hZ : 0<Z) (ha : theta  ≤  a) (hξ : 33/200 ≤ ξ) (hξ1 : 6*ξ≠1)
    (hC : 0 ≤ C) (hR : ∀s : ℂ,a ≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖ ≤ 
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ ≤ C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := Cycle61.Transport.PrincipalFiniteProduct.combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ) ≤ 3/2) (Cycle61.Transport.PrincipalFiniteProduct.slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X^(1/2-ξ)*Z^(a+ξ-1)*
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ *
        ‖globalClosedCorrection η S ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
          slotMultiplier η J T b ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ := by
      simp only [residueArithmetic,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _  ≤  X^(1/2-ξ)*Z^(a+ξ-1)*(C*height q.1^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*height q.2^3) := by
      gcongr
      first | positivity | exact hL
    _  ≤  X^(1/2-ξ)*Z^(a+ξ-1)*(C*jointHeight q.1 q.2 0^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hC : 0 ≤ C) : 0 ≤ residueAmplitude S J T b X Z a ξ C := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := Cycle61.Transport.PrincipalFiniteProduct.slotBound_nonneg J T b a ξ
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith [Cycle61.Transport.theta_bounds]) 5 0
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith [Cycle61.Transport.theta_bounds]) hξ1
  have hb := residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  apply (continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [Cycle61.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200 ≤ ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hi := residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let B := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let D := fun s => R*verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))
  let E := fun s => R^2/6*K s 1 (1/6)
  have hA : Integrable (fun t : ℝ => A ((a:ℂ)+t*I)) :=
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith [Cycle61.Transport.theta_bounds]) hcw ⟨by linarith [Cycle61.Transport.theta_bounds],le_rfl⟩
      (by linarith [Cycle61.Transport.theta_bounds]) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith [Cycle61.Transport.theta_bounds]) hcw ⟨le_rfl,by linarith [Cycle61.Transport.theta_bounds]⟩
      (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a:ℂ)+t*I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a:ℂ)+t*I)-B ((a:ℂ)+t*I)-D ((a:ℂ)+t*I)=E ((a:ℂ)+t*I)
    rw [ht]
    ring
  have heq : verticalIntegral a A=verticalIntegral a (fun s => B s+D s+E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A=verticalIntegral a B+R*verticalIntegral a _+R^2/6*verticalIntegral a _
  rw [heq]
  simp only [D,E,verticalIntegral,integral_const_mul]
  ring

end Cycle61.Transport.PrincipalContours
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderContours -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderTransport; sha256 ce087a0fa13391d835e166796903713e9106b96faeb8f9dd3833af4d9f758089 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                            
                                                              
noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Cycle61.Transport.PrincipalTransport
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalTransport
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalFiniteProductX Cycle61.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t  ≤  (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _  ≤  ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert shifted_gaussian_top n (-v) using 1
  funext t
  rw [←gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a ≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖ ≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖ ≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0 ≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖ ≤ A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith [Cycle61.Transport.theta_bounds]) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0 ≤ A := Cycle61.Transport.PrincipalContours.arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith [Cycle61.Transport.theta_bounds])
  have hB : 0 ≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [Cycle61.Transport.theta_bounds, hξ.1],hξ.2⟩
  have hw : (2:ℝ) ≤ ‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1 ≤ ‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0 ≤ 6*ξ-1 := by linarith [Cycle61.Transport.theta_bounds, hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [Cycle61.Transport.theta_bounds, hξ.1]) h
  have hb := Cycle61.Transport.PrincipalContours.arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith [Cycle61.Transport.theta_bounds]) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←Cycle61.Transport.PrincipalContours.arithmetic_profile_eq_source,norm_mul]
  calc
    _  ≤  (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _  ≤  A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := Cycle61.Transport.PrincipalFiniteProductX.continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ) ≤ ξ by linarith [Cycle61.Transport.theta_bounds])) ha hβ
    (c:=3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25<z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25<z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0<z.re; change (4/25:ℝ)<z.re at hz; linarith [Cycle61.Transport.theta_bounds])
  have hH := (Cycle61.Transport.PrincipalFiniteProduct.combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6<z.re} := by
  have hK := continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)<z.re; change (1/6:ℝ)<z.re at hz; linarith [Cycle61.Transport.theta_bounds])).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith [Cycle61.Transport.theta_bounds]
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith [Cycle61.Transport.theta_bounds]
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)<z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _  ≤  A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _  ≤  A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := Cycle61.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num)
  have hi3 := Cycle61.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Cycle61.Transport.theta_bounds])) (hβ.trans_le ha3) (by linarith [Cycle61.Transport.theta_bounds])
    (by norm_num) (by norm_num) (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := Cycle61.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Cycle61.Transport.theta_bounds]) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := Cycle61.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [Cycle61.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith [Cycle61.Transport.theta_bounds]) (by linarith [Cycle61.Transport.theta_bounds])
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  exact (source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (Cycle61.Transport.PrincipalContours.source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

theorem source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (Cycle61.Transport.PrincipalContours.source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Cycle61.Transport.theta_bounds])) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end Cycle61.Transport.PrincipalTransport
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderTransport -/
