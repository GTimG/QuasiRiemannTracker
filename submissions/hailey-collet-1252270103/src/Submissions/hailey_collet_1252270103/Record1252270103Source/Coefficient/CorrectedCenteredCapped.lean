/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected centered saving is capped at one without any lower bound on
the positive raw scales. Both analytic bounds are obtained from checked sources. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedCenteredSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentAbsoluteEnergy
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O

theorem corrected_centered_source_control_capped
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0 →∃C : ℝ,0<C ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀Z : ℝ,1≤Z →∀η χ ψ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^Bχ →Q≤ψ.modulus →InducedBy χ ψ →
      ∀m A z : O,goodLambda∣m →(2:O)∣m →
      (∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) →
      ∀A₁ A₂ D M : Ideal O,A₁≠0 →A₂≠0 →((A₁*A₂).absNorm:ℝ)≤Z^BA →
      ∀P : Finset (Ideal O),0<P.card →(∀p∈P,Prime p) →(∀p∈P,16≤p.absNorm) →
      (∀p∈P,(p.absNorm:ℝ)≤Z^Bpool) →(∀p∈P,¬p∣M) →
      2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      (∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
        frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→ rowWeight η m A z t (n.1*n.2)≠0→
        IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
          (idealDividingPool P (D*(M*n.1*n.2))).card<P.card) →
      ‖correctedCenteredRow P D M A₁ A₂ (rowWeight η m A z t) W₁ W₂ b X₁ X₂ Y₁ Y₂ T‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*Real.sqrt T*(max 1 L)^(-α) := by
  obtain ⟨J₀,S₀,hS₀,hzero⟩ := corrected_centered_source_control_fractional
    a b ε Bχ BA Bpool 0 depth ha hb hε hBχ hBA hBpool (by norm_num) (by norm_num)
  obtain ⟨J₁,S₁,hS₁,hfrac⟩ := corrected_centered_source_control_fractional
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨max J₀ J₁,S₀∪S₁,Finset.mem_union_left _ hS₀,?_⟩
  intro Q hQ
  obtain ⟨C₀,hC₀,hzero⟩ := hzero Q hQ
  obtain ⟨C₁,hC₁,hfrac⟩ := hfrac Q hQ
  refine ⟨C₀+C₁,add_pos hC₀ hC₁,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow A₁ A₂ D M
    hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget t X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport
  have hcontrol {S U : Finset (ℕ×ℕ)} (h : S⊆U) (W : 𝓢(ℝ,ℂ)) :
      sourceControl S W≤sourceControl U W := Seminorm.le_def.mp (Finset.sup_mono h) W
  have hlift {S : Finset (ℕ×ℕ)} {j : ℕ} {c : ℝ}
      (hS : S⊆S₀∪S₁) (hj : j≤max J₀ J₁) (hc : 0≤c) (hcc : c≤C₀+C₁) :
      c*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^j≤
        (C₀+C₁)*(sourceControl (S₀∪S₁) W₁*sourceControl (S₀∪S₁) W₂)*Z^ε*
          (1+‖t‖)^(max J₀ J₁) := by
    have hpw : (1+‖t‖)^j≤(1+‖t‖)^max J₀ J₁ :=
      pow_le_pow_right₀ (by linarith [norm_nonneg t]) hj
    have hctrl := mul_le_mul (hcontrol hS W₁) (hcontrol hS W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul hcc hctrl (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
        (add_nonneg hC₀.le hC₁.le)) (Real.rpow_nonneg (zero_le_one.trans hZ) _))
      hpw (by positivity) (mul_nonneg (mul_nonneg (add_nonneg hC₀.le hC₁.le)
        (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)))
          (Real.rpow_nonneg (zero_le_one.trans hZ) _))
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    apply (hfrac W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
      A₁ A₂ D M hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hlift Finset.subset_union_right (le_max_right _ _) hC₁.le (by linarith))
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg hL.le _)
  · rw [max_eq_left (le_of_not_ge hlarge),Real.one_rpow,mul_one]
    have hz := hzero W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
      A₁ A₂ D M hA₁ hA₂ hnormA P hP hp hN hpool havoid hbudget
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY hsupport
    simp only [neg_zero,Real.rpow_zero,mul_one] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right
      (hlift Finset.subset_union_left (le_max_left _ _) hC₀.le (by linarith))
      (Real.sqrt_nonneg _))

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_centered_source_control_capped
