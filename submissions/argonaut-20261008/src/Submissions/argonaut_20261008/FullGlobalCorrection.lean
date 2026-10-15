import Submissions.argonaut_20261008.FullGlobalHolomorphic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceExclusions

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def globalPrimeDefectBoundSigma (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(169/100:ℝ))

lemma globalPrimeDefectBoundSigma_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBoundSigma P := by
  unfold globalPrimeDefectBoundSigma
  positivity

lemma globalPrimeDefectBoundSigma_summable : Summable globalPrimeDefectBoundSigma := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((169/100:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((169/100:ℝ):ℂ) P.val‖=globalPrimeDefectBoundSigma P
  unfold globalPrimeDefectBoundSigma CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure CorrectionTailSigma (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},globalPrimeDefectBoundSigma P.val)≤1/6

lemma CorrectionTailSigma.summable {S : Finset Id} (_h : CorrectionTailSigma S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBoundSigma P.val) :=
  globalPrimeDefectBoundSigma_summable.subtype _

lemma CorrectionTailSigma.half {S : Finset Id} (h : CorrectionTailSigma S)
    (P : {P : PrimeIdeal // P.val∉S}) : globalPrimeDefectBoundSigma P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>globalPrimeDefectBoundSigma_nonneg Q.val)
  linarith [h.small]

lemma idealClosedCorrection_sigma_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 87/100≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBoundSigma P := by
  apply unramifiedClosed_contour_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_sigma_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (x w z : ℂ)
    (hx : 87/100≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_sigma_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_sigma_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (x w z : ℂ)
    (hx : 87/100≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBoundSigma P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_sigma_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_sigma_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|87/100<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_contour_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_sigma_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_sigma_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (x z : ℂ) (hx : 87/100≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_contour_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_sigma_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_sigma_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (x w : ℂ) (hx : 87/100≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_contour_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_sigma_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

theorem exists_uniform_global_sigma_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTailSigma S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBoundSigma)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>globalPrimeDefectBoundSigma_nonneg P.val) (fun _=>le_rfl)
      (globalPrimeDefectBoundSigma_summable.subtype _) (globalPrimeDefectBoundSigma_summable.subtype _)

theorem exists_global_sigma_correction (S₀ : Finset Id) :
    ∃S : Finset Id,S₀⊆S ∧ CorrectionTailSigma S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_sigma_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

lemma globalPrimeDefectBound_le_sigma (P : PrimeIdeal) :
    globalPrimeDefectBound P ≤ globalPrimeDefectBoundSigma P := by
  have hQ2 : (2:ℝ) ≤ (Ideal.absNorm P.val:ℝ) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ1 : (1:ℝ) ≤ (Ideal.absNorm P.val:ℝ) := by linarith
  unfold globalPrimeDefectBound globalPrimeDefectBoundSigma
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hQ1
      (by norm_num : -(17/10:ℝ) ≤ -(169/100:ℝ))) (by norm_num)

lemma CorrectionTailSigma.toCorrectionTail {S : Finset Id} (h : CorrectionTailSigma S) :
    CorrectionTail S := by
  constructor
  · exact h.norm_four
  · exact (Summable.tsum_le_tsum
      (fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound_le_sigma P.val)
      (globalPrimeDefectBound_summable.subtype _) h.summable).trans h.small

structure SourceExclusionsSigma (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTailSigma S

lemma SourceExclusionsSigma.toSourceExclusions {S : Finset Id} (h : SourceExclusionsSigma S) :
    SourceExclusions S :=
  ⟨h.prime,h.bad,h.tail.toCorrectionTail⟩

theorem exists_source_exclusions_sigma (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusionsSigma S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_sigma_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbePhysical
end

end OAI

