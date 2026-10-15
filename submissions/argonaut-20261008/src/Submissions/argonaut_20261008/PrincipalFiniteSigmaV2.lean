import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import Submissions.argonaut_20261008.PrincipalBoundaryB0
import Submissions.argonaut_20261008.FullGlobalRegion
import Submissions.argonaut_20261008.FullGlobalHolomorphic
import Submissions.argonaut_20261008.FullGlobalCorrection

/- NEW LOCAL CANDIDATE. Kernel NOT_RUN. Same actual mathematical objects;
   only analytic x boundary and Sigma evidence are adapted. No final estimate assumption. -/
namespace OAI.SevenEighths.LocalPrincipalFiniteV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Set MeasureTheory Filter Asymptotics
open ActualEisensteinCubic HeckeFamily CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary
open ProbeFiniteProductBounds

local notation "Id" => Ideal HeckeFamily.O

theorem correction_lower_bound_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (idealClosedCorrection_sigma_bound η P (hS.norm_four P hP) x w z
    ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound_pc2 η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound_pc2 η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w_pc2 (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z_pc2 (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz
  have hc := unramifiedClosed_contour_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w_pc2 η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero_pc2 η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_contour_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx)
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz.le
  have hmc := marked_differentiableAt_z_pc2 η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero_pc2 η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound_pc2 (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : analyticBoundaryB0 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hxfloor : (87/100 : ℝ) ≤ x.re := by
    exact (by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx

  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
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

lemma replacement_bound_pc2 (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
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
    _ ≤ 200*(1+R) := by linarith

lemma localBound_nonneg_pc2 (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (analyticBoundaryB0) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  have hxfloor : (87/100 : ℝ) ≤ x.re := by
    exact (by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx.1

  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound_pc2 Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound_pc2 _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound_pc2 η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
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

lemma selectedBound_nonneg_pc2 (T : Finset PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => localBound_nonneg_pc2 Bx Bz P)

lemma slotBound_nonneg_pc2 {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg_pc2 Bx Bz P))

theorem selected_analytic_w_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_w_pc2 η S hS P (hT P hp) x z hx hz)

theorem selected_analytic_z_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_z_pc2 η S hS P (hT P hp) x w hx hw)

theorem slot_analytic_w_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w_pc2 η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z_pc2 η S hS P (hT j hj P hp) x w hx hw)

theorem selected_norm_bound_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (analyticBoundaryB0) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => local_norm_bound_pc2 η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem slot_norm_bound_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (analyticBoundaryB0) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound_pc2 η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (x w z : ℂ) (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := globalClosedCorrection_sigma_bound η S hS x w z
    ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (globalClosedCorrection_sigma_analytic_w η S hS x z ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz).mul (slot_analytic_w_pc2 η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : analyticBoundaryB0 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (globalClosedCorrection_sigma_analytic_z η S hS x w ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hw).mul (slot_analytic_z_pc2 η S hS J T b hT x w hx hw)

theorem combined_slot_bound_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (analyticBoundaryB0) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound_pc2 η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound_pc2 η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem selected_initial_identity_pc2 (η : Character) (S : Finset Id) (hS : SourceExclusionsSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  rw [spectralCompensatedHigh_continued S hS.toSourceExclusions T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem source_w_boundary_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1<cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg_pc2 J T b _ _)) 0
  · exact (combined_slot_analytic_w_pc2 η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound_pc2 η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_z_boundary_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (slotBound_nonneg_pc2 J T b _ _)) 0
  · exact (combined_slot_analytic_z_pc2 η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound_pc2 η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem source_multiplier_differentiable_w_pc2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusionsSigma S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w_pc2 η S hS.tail J T b hT s z hs hz).differentiableOn
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

theorem source_multiplier_differentiable_z_pc2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusionsSigma S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z_pc2 η S hS.tail J T b hT s w hs hw).differentiableOn
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

theorem source_w_shift_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1<cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (source_multiplier_differentiable_w_pc2 η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · exact source_w_boundary_pc2 η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem source_residue_z_shift_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : analyticBoundaryB0 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (source_multiplier_differentiable_z_pc2 η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · exact source_z_boundary_pc2 η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'


theorem window_at_residue_pc2 {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
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



theorem selected_as_slots_pc2 (η : Character) (T : Finset PrimeIdeal) (s w z : ℂ) :
    selectedMultiplier η T s w z = slotMultiplier η T (fun P => {P}) (fun _ _ => 1) s w z := by
  simp [selectedMultiplier,slotMultiplier]

theorem fixed_source_boundaries_pc2 {ι : Type*} (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : analyticBoundaryB0 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact source_w_boundary_pc2 η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact source_z_boundary_pc2 η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma boundary_mul_const_pc2 (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem fixed_source_ordered_boundaries_pc2 {ι : Type*} (S : Finset Id) (hS : SourceExclusionsSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : analyticBoundaryB0 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hh := fixed_source_boundaries_pc2 S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert boundary_mul_const_pc2 _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem uniform_closed_box_bound_pc2 {ι : Type*} (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (analyticBoundaryB0) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (slotBound_nonneg_pc2 J T b Bx Bz),
    fun η s w z hs hw hz => combined_slot_bound_pc2 η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩


end
end OAI.SevenEighths.LocalPrincipalFiniteV2
