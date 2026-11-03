/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighGlobalCorrection.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighGlobalRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def perturbedGlobalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(5 / 3 : ℝ))

theorem perturbed_global_prime_defect_bound_nonnegative (P : PrimeIdeal) :
    0 ≤ perturbedGlobalPrimeDefectBound P := by
  unfold perturbedGlobalPrimeDefectBound
  positivity

theorem sum_perturbed_global_prime_defects :
    Summable perturbedGlobalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    ((5 / 3 : ℝ) : ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal => P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240 * ‖CubicEisenstein.fullIdealWeight ((5 / 3 : ℝ) : ℂ) P.val‖ =
    perturbedGlobalPrimeDefectBound P
  unfold perturbedGlobalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure PerturbedCorrectionTail (S : Finset Id) : Prop where
  norm_four : ∀ P : PrimeIdeal, P.val ∉ S → 4 ≤ Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val ∉ S},
    perturbedGlobalPrimeDefectBound P.val) ≤ 1 / 6

theorem PerturbedCorrectionTail.sum_defects {S : Finset Id}
    (_h : PerturbedCorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val ∉ S} =>
      perturbedGlobalPrimeDefectBound P.val) :=
  sum_perturbed_global_prime_defects.subtype _

theorem PerturbedCorrectionTail.bound_single_defect {S : Finset Id}
    (h : PerturbedCorrectionTail S)
    (P : {P : PrimeIdeal // P.val ∉ S}) :
    perturbedGlobalPrimeDefectBound P.val ≤ 1 / 2 := by
  have hterm := Summable.le_tsum h.sum_defects P
    (fun Q _ => perturbed_global_prime_defect_bound_nonnegative Q.val)
  linarith [h.small]

theorem PerturbedCorrectionTail.to_source {S : Finset Id}
    (h : PerturbedCorrectionTail S) : CorrectionTail S := by
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hpoint (P : T) :
      globalPrimeDefectBound P.val ≤ perturbedGlobalPrimeDefectBound P.val := by
    unfold globalPrimeDefectBound perturbedGlobalPrimeDefectBound
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ Ideal.absNorm P.val.val by
        have := h.norm_four P.val P.property
        omega))
    norm_num
  refine ⟨h.norm_four, ?_⟩
  exact (Summable.tsum_le_tsum hpoint
    (globalPrimeDefectBound_summable.subtype _)
    h.sum_defects).trans h.small

theorem bound_ideal_closed_correction_on_perturbed_region
    (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : (boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖idealClosedCorrection η P x w z - 1‖ ≤
      perturbedGlobalPrimeDefectBound P := by
  apply bound_unramified_closed_on_perturbed_open_region
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem bound_global_closed_correction_on_perturbed_region
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S) (x w z : ℂ)
    (hx : (boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖globalClosedCorrection η S x w z - 1‖ ≤ 1 / 2 :=
  product_defect_le _ _ hS.sum_defects
    (fun P => bound_ideal_closed_correction_on_perturbed_region η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.bound_single_defect hS.small

theorem global_closed_correction_analytic_x_on_perturbed_region
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S) (w z : ℂ)
    (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z)
      {x : ℂ | boundary < x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.sum_defects
  · intro P
    apply unramified_closed_analytic_x_on_perturbed_region
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact bound_ideal_closed_correction_on_perturbed_region η P.val
      (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.bound_single_defect

theorem global_closed_correction_analytic_w_on_perturbed_region
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S) (x z : ℂ)
    (hx : (boundary : ℝ) ≤ x.re)
    (hz : (4 / 25 : ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z)
      {w : ℂ | 9 / 10 < w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.sum_defects
  · intro P
    apply unramified_closed_analytic_w_on_perturbed_region
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact bound_ideal_closed_correction_on_perturbed_region η P.val
      (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.bound_single_defect

theorem global_closed_correction_analytic_z_on_perturbed_region
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : PerturbedCorrectionTail S) (x w : ℂ)
    (hx : (boundary : ℝ) ≤ x.re)
    (hw : (9 / 10 : ℝ) ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z)
      {z : ℂ | 4 / 25 < z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.sum_defects
  · intro P
    apply unramified_closed_analytic_z_on_perturbed_region
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact bound_ideal_closed_correction_on_perturbed_region η P.val
      (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.bound_single_defect

theorem exists_uniform_perturbed_global_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ S : Finset Id,
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
        PerturbedCorrectionTail S := by
  have ht := (tendsto_order.1
    (tendsto_tsum_compl_atTop_zero perturbedGlobalPrimeDefectBound)).2
    (1 / 6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    exact P.property (hS P.val
      ((Finset.le_sup (f := fun P : PrimeIdeal => Ideal.absNorm P.val) hm).trans
        (le_max_right _ _)))
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg
      (fun P : {P : PrimeIdeal // P ∉ F} => P.val) h)
  constructor
  · intro P hP
    have hn : ¬ Ideal.absNorm P.val ≤ N := fun hn => hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => perturbed_global_prime_defect_bound_nonnegative P.val)
      (fun _ => le_rfl)
      (sum_perturbed_global_prime_defects.subtype _)
      (sum_perturbed_global_prime_defects.subtype _)

theorem exists_perturbed_global_correction (S₀ : Finset Id) :
    ∃ S : Finset Id, S₀ ⊆ S ∧ PerturbedCorrectionTail S := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_perturbed_global_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbePhysical

end

end OAI
