import Submissions.argonaut_20261008.PrincipalFiniteSigmaV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductX

/- NEW LOCAL CANDIDATE. Kernel NOT_RUN. Same actual mathematical objects;
   only analytic x boundary and Sigma evidence are adapted. No final estimate assumption. -/
namespace OAI.SevenEighths.LocalPrincipalFiniteXV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Set MeasureTheory Filter Asymptotics
open ActualEisensteinCubic HeckeFamily CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary
open ProbeFiniteProductBounds
open ProbeFiniteProductX LocalPrincipalFiniteV2
local notation "Id" => Ideal HeckeFamily.O

lemma marked_differentiableAt_x_pc2 (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : analyticBoundaryB0 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx) hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | analyticBoundaryB0 < x.re} := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_contour_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := contour_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) ≤ analyticBoundaryB0).trans hx.le) hz
  have hm := marked_differentiableAt_x_pc2 η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) < analyticBoundaryB0).trans hx)).differentiableAt
  have hh := correction_ne_zero_pc2 η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | analyticBoundaryB0 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x_pc2 η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | analyticBoundaryB0 < x.re} := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x_pc2 η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | analyticBoundaryB0 < x.re} :=
  slot_analytic_x_pc2 η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x_pc2 (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | analyticBoundaryB0 < x.re} :=
  ((globalClosedCorrection_sigma_analytic_x η S hS w z hw hz).mono
    (by intro x hx; exact (by norm_num [analyticBoundaryB0] : (87/100 : ℝ) < analyticBoundaryB0).trans hx)).mul
    (selected_analytic_x_pc2 η S hS T hT w z hw hz)

theorem combined_slot_analytic_x_pc2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | analyticBoundaryB0 < x.re} :=
  ((globalClosedCorrection_sigma_analytic_x η S hS w z hw hz).mono
    (by intro x hx; exact (by norm_num [analyticBoundaryB0] : (87/100 : ℝ) < analyticBoundaryB0).trans hx)).mul
    (slot_analytic_x_pc2 η S hS J T b hT w z hw hz)

theorem continued_source_analytic_x_pc2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusionsSigma S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (analyticBoundaryB0 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (analyticBoundaryB0 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (globalClosedCorrection_sigma_analytic_x η S hS.tail w z hw hz x ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) < analyticBoundaryB0).trans hx')).differentiableAt
  have hB := (slot_analytic_x_pc2 η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)



theorem source_analytic_x_off_one_pc2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusionsSigma S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (analyticBoundaryB0 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (analyticBoundaryB0 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (globalClosedCorrection_sigma_analytic_x η S hS.tail w z hw hz x ((by norm_num [analyticBoundaryB0] : (87/100 : ℝ) < analyticBoundaryB0).trans hx')).differentiableAt
  have hB := (slot_analytic_x_pc2 η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip_pc2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusionsSigma S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : analyticBoundaryB0<a) (hβ : HeckeZeroSupremum.beta<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤c} := by
  have hboundary_pos : 0 < analyticBoundaryB0 := analyticBoundaryB0_pos

  apply (continued_source_analytic_x_pc2 η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1


end
end OAI.SevenEighths.LocalPrincipalFiniteXV2
