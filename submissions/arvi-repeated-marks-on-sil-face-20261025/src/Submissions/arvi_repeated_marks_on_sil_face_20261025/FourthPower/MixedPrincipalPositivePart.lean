/- Copyright (c) 2026 Sil. Apache-2.0.
The all-scale branch is the already proved principal theorem at alpha=0.
Combining it with alpha>0 justifies the positive-part saving without
altering the actual prefix denominator or profile homogeneity.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedPrincipalCentered

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalPositivePart
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open MixedCenteredEnergy MixedPrincipalCentered
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem control_mono {S T : Finset (ℕ×ℕ)} (hST : S⊆T) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S W≤sourceControl T W := by
  apply Seminorm.finset_sup_apply_le (sourceControl_nonneg T W)
  intro p hp
  exact Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (hST hp)

def profileCost (C : ℝ) (S : Finset (ℕ×ℕ)) (J : ℕ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (t₁ t₂ : ℝ) : ℝ :=
  C*(sourceControl S W₁*sourceControl S W₂)*(1+‖t₁‖+‖t₂‖)^J

theorem profileCost_mono {C D : ℝ} (hC : 0≤C) (hCD : C≤D)
    {S T : Finset (ℕ×ℕ)} (hST : S⊆T) {J K : ℕ} (hJK : J≤K)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (t₁ t₂ : ℝ) :
    profileCost C S J W₁ W₂ t₁ t₂≤profileCost D T K W₁ W₂ t₁ t₂ := by
  have hH : 1≤1+‖t₁‖+‖t₂‖ := by linarith [norm_nonneg t₁,norm_nonneg t₂]
  unfold profileCost
  apply mul_le_mul
  · apply mul_le_mul hCD
      (mul_le_mul (control_mono hST W₁) (control_mono hST W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
      (hC.trans hCD)
  · exact pow_le_pow_right₀ hH hJK
  · positivity
  · exact mul_nonneg (hC.trans hCD)
      (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))

/-- Literal conversion to the logarithmic positive-part form. -/
theorem max_power_saving (Z l v α : ℝ) (hZ : 1≤Z) :
    (max 1 (Z^(l-v)))^(-α)=Z^(-α*max (l-v) 0) := by
  by_cases h : l-v≤0
  · rw [max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ h),max_eq_right h]
    simp
  · have h0 : 0≤l-v := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (Real.one_le_rpow hZ h0),max_eq_left h0,
      ←Real.rpow_mul (zero_le_one.trans hZ)]
    congr 1
    ring

/-- The same finite-seminorm principal bound with no loss when a prefix
shortens L below one. Constants and control sets are chosen before both
profiles, every actual family parameter, and every live index type. -/
theorem uniform_centered_positive (α B a b ε : ℝ) (hα : 0≤α) (hα4 : α<4/5)
    (hB : 0≤B) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀Z : ℝ,1≤Z→∀Fhole F : Id,Fhole≠0→(Fhole.absNorm:ℝ)≤Z^B→F≠0→
      ∀S H : Finset PrimeIdeal,(∀P∈S,Supported P.val)→(∀P∈H,P.val∣Fhole)→
      ∀(η : Character)(z : O),z≠0→
      (HeckeRowClosure.rowConductorBound η (fixedBadMask*idealGenerator F) 1 z:ℝ)≤Z^B→
      CenteredExceptionalProfile.FixedInducingRow η Q fixedBadMask 1 z→
      ∀(ι : Type*) [Fintype ι],
      ∀(pool : ι→Finset Id)(β : ι→Id→ℂ)(P M : ι→ℝ),
      (∀i,0<P i)→(∀i,0≤M i)→
      (∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i)→
      (∀i I,I∈pool i→‖β i I‖≤M i)→(∏i,2*P i)≤Z^B→
      ∀(e : Id×Id),e.1≠0∧e.2≠0→
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*(U₁/e.1.absNorm)∨
        (I.absNorm:ℝ)≤b*(U₂/e.2.absNorm))→primeSupport I⊆primeValues S)→
      ‖centeredRow (excluded (naturalCharacter η z) F) S H pool β P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂ Y₁ Y₂ e‖≤
        (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*Real.sqrt (T*∏i,P i)/pairNorm e)*
          (max 1 (L/prefixNormMax e))^(-α) := by
  obtain ⟨J₀,control₀,h00₀,hbound₀⟩ := uniform_centered 0 B a b ε
    le_rfl (by norm_num) hB ha hb hε
  obtain ⟨Jα,controlα,h00α,hboundα⟩ := uniform_centered α B a b ε hα hα4 hB ha hb hε
  let J := max J₀ Jα
  let control := control₀∪controlα
  refine ⟨J,control,Finset.mem_union_left _ h00₀,?_⟩
  intro Q hQ
  obtain ⟨C₀,hC₀,hCbound₀⟩ := hbound₀ Q hQ
  obtain ⟨Cα,hCα,hCboundα⟩ := hboundα Q hQ
  let C := max C₀ Cα
  have hC : 0<C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ Fhole F hFhole hFcut hF S H hS hH η z hz hcond hex
    ι instι pool β P M hP hM hp hβ hV e he
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let E := Z^ε*(∏i,256*M i)*Real.sqrt (T*∏i,P i)/pairNorm e
  have hE : 0≤E := by
    dsimp [E]
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (hM i)))) (Real.sqrt_nonneg _))
      (pairNorm_pos he.1 he.2).le
  by_cases hs : L/prefixNormMax e≤1
  · have hh := hCbound₀ W₁ W₂ hs₁ hs₂ Z hZ Fhole F hFhole hFcut hF S H hS hH η z hz hcond hex
      ι pool β P M hP hM hp hβ hV e he
      t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    rw [max_eq_left hs,Real.one_rpow,mul_one]
    apply hh.trans
    calc
      _ = profileCost C₀ control₀ J₀ W₁ W₂ t₁ t₂*E := by dsimp [profileCost,E];ring
      _ ≤ profileCost C control J W₁ W₂ t₁ t₂*E := mul_le_mul_of_nonneg_right
        (profileCost_mono hC₀.le (le_max_left _ _) Finset.subset_union_left (le_max_left _ _)
          W₁ W₂ t₁ t₂) hE
      _ = _ := by dsimp [profileCost,E];ring
  · have hs' : 1≤L/prefixNormMax e := le_of_lt (lt_of_not_ge hs)
    have hh := hCboundα W₁ W₂ hs₁ hs₂ Z hZ Fhole F hFhole hFcut hF S H hS hH η z hz hcond hex
      ι pool β P M hP hM hp hβ hV e he
      t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
    rw [max_eq_right hs']
    apply hh.trans
    calc
      _ = profileCost Cα controlα Jα W₁ W₂ t₁ t₂*(E*(L/prefixNormMax e)^(-α)) := by
        dsimp [profileCost,E];ring
      _ ≤ profileCost C control J W₁ W₂ t₁ t₂*(E*(L/prefixNormMax e)^(-α)) :=
        mul_le_mul_of_nonneg_right
          (profileCost_mono hCα.le (le_max_right _ _) Finset.subset_union_right (le_max_right _ _)
            W₁ W₂ t₁ t₂)
          (mul_nonneg hE (Real.rpow_nonneg (div_pos hL (prefixNormMax_pos e he)).le _))
      _ = _ := by dsimp [profileCost,E];ring

end
end Candidate.FourthPower.MixedPrincipalPositivePart
