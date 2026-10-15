import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalProduct
import Submissions.argonaut_20261008.EulerSigma
namespace OAI
noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O
def primeDefectBoundSigma (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-σ-(47/50:ℝ))
lemma primeDefectBoundSigma_nonneg (σ : ℝ) (P : PrimeIdeal) : 0 ≤ primeDefectBoundSigma σ P := by unfold primeDefectBoundSigma; positivity
lemma primeDefectBoundSigma_summable (σ : ℝ) (hσ : (79/100:ℝ) ≤ σ) :
    Summable (primeDefectBoundSigma σ) := by
  have hs : 1 < (((σ+47/50:ℝ):ℂ)).re := by simp only [Complex.ofReal_re]; linarith
  have h : Summable (fun P : PrimeIdeal =>
      ‖CubicEisenstein.fullIdealWeight ((σ+47/50:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs).comp_injective Subtype.val_injective
  apply (h.mul_left 240).congr; intro P
  unfold primeDefectBoundSigma CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp [neg_add, sub_eq_add_neg, add_comm]
lemma principalLocal_sigma_bound (σ : ℝ) (hσlo : (79/100:ℝ) ≤ σ) (hσhi : σ ≤ 1)
    (eta : HeckeFamily.Character) (P : PrimeIdeal) (hP : 4 ≤ Ideal.absNorm P.val)
    (s : ℂ) (hs : σ < s.re) : ‖principalLocal eta P s-1‖ ≤ primeDefectBoundSigma σ P := by
  apply unramifiedClosed_sigma_region_bound (σ := σ)
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hσlo
  · exact hσhi
  · exact hs.le
  · norm_num
  · norm_num
lemma principalLocal_sigma_analytic (σ : ℝ) (hσ : (79/100:ℝ) ≤ σ)
    (eta : HeckeFamily.Character) (P : PrimeIdeal) (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | σ < s.re} := by
  apply principalClosed_sigma_analytic (σ := σ)
  · exact_mod_cast hP
  · exact hσ
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
theorem exists_uniform_principal_cutoff_sigma (σ : ℝ)
    (hσlo : (79/100:ℝ) ≤ σ) (hσhi : σ ≤ 1) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ S : Finset (Ideal O),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | σ < s.re} ∧
        ∀ s : ℂ, σ < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (primeDefectBoundSigma σ))).2 (1/6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)))
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => primeDefectBoundSigma σ P.val) :=
    (primeDefectBoundSigma_summable σ hσlo).subtype _
  have hsmall : (∑' P : T, primeDefectBoundSigma σ P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => primeDefectBoundSigma_nonneg σ P.val) (fun _ => le_rfl)
      hsum ((primeDefectBoundSigma_summable σ hσlo).subtype _)
  have hhalf (P : T) : primeDefectBoundSigma σ P.val ≤ 1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _ => primeDefectBoundSigma_nonneg σ Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => primeDefectBoundSigma σ P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_sigma_analytic σ hσlo eta P.val (hnorm P))
      (fun P s hs => principalLocal_sigma_bound σ hσlo hσhi eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => primeDefectBoundSigma σ P.val) hsum
      (fun P => principalLocal_sigma_bound σ hσlo hσhi eta P.val (hnorm P) s hs) hhalf hsmall
theorem exists_principal_correction_sigma (σ : ℝ) (hσlo : (79/100:ℝ) ≤ σ) (hσhi : σ ≤ 1)
    (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | σ < s.re} ∧
      ∀ s : ℂ, σ < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  obtain ⟨N, _, hcut⟩ := exists_uniform_principal_cutoff_sigma σ hσlo hσhi
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut; intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
theorem exists_uniform_principal_cutoff_tau :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ S : Finset (Ideal O),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | (3499999/4000000:ℝ) < s.re} ∧
        ∀ s : ℂ, (3499999/4000000:ℝ) < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 :=
  exists_uniform_principal_cutoff_sigma _ (by norm_num) (by norm_num)
theorem exists_principal_correction_tau (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | (3499999/4000000:ℝ) < s.re} ∧
      ∀ s : ℂ, (3499999/4000000:ℝ) < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 :=
  exists_principal_correction_sigma _ (by norm_num) (by norm_num) S₀
end SevenEighths.ProbeEuler
end
end OAI
