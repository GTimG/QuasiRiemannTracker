/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact finite divisor transport of the actual centered ordinary rectangle.
The divisor character may be retained in the complex coefficient with zeros. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CenteredOrdinary

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentHeckeTwist CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

def centeredRectangle (χ : Character) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
    twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)

theorem centered_divisor_scalar (T L d α : ℝ) (hT : 0<T) (hL : 0<L) (hd : 0<d) :
    (Real.sqrt d)⁻¹*(Real.sqrt (T/d)*(L/d)^(-α))=
      Real.sqrt T*L^(-α)/d^(1-α) := by
  rw [Real.sqrt_div hT.le,Real.div_rpow hL.le hd.le,sub_eq_add_neg,
    Real.rpow_add hd,Real.rpow_one]
  have hs : Real.sqrt d≠0 := (Real.sqrt_pos.mpr hd).ne'
  have hp : d^(-α)≠0 := (Real.rpow_pos_of_pos hd _).ne'
  field_simp
  rw [Real.sq_sqrt hd.le]

theorem divisor_common_lower (L X d e : ℝ) (hL : 0≤L) (hX : L≤X)
    (hd : 1≤d) (he : 1≤e) : L/(d*e)≤X/d := by
  rw [mul_comm d e,←div_div]
  exact div_le_div_of_nonneg_right ((div_le_self hL he).trans hX) (by linarith)

/-- The real exponent 1-α is forced by the central normalization and the
equal-product scale. No termwise deletion or square-norm comparison is used. -/
theorem centered_divisor_transport {ι : Type*} (D : Finset ι)
    (χ : Character) (W₁ W₂ : 𝓢(ℝ,ℂ)) (t X₁ X₂ Y₁ Y₂ T L α A : ℝ)
    (hT : 0<T) (hL : 0<L)
    (hX₁ : L≤X₁) (hX₂ : L≤X₂) (hY₁ : L≤Y₁) (hY₂ : L≤Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T)
    (d₁ d₂ : ι→ℝ) (w : ι→ℂ)
    (hd₁ : ∀i∈D,1≤d₁ i) (hd₂ : ∀i∈D,1≤d₂ i)
    (hchild : ∀x₁ x₂ y₁ y₂ t' l : ℝ,0<l →
      l≤x₁ →l≤x₂ →l≤y₁ →l≤y₂ →x₁*x₂=t' →y₁*y₂=t' →
      ‖centeredRectangle χ W₁ W₂ t x₁ x₂ y₁ y₂ t'‖≤A*Real.sqrt t'*l^(-α)) :
    ‖∑i∈D,(w i/(Real.sqrt (d₁ i*d₂ i):ℂ))*
      centeredRectangle χ W₁ W₂ t (X₁/d₁ i) (X₂/d₂ i) (Y₁/d₁ i) (Y₂/d₂ i)
        (T/(d₁ i*d₂ i))‖≤
      A*Real.sqrt T*L^(-α)*(∑i∈D,‖w i‖/(d₁ i*d₂ i)^(1-α)) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h₁ : 0<d₁ i := lt_of_lt_of_le zero_lt_one (hd₁ i hi)
  have h₂ : 0<d₂ i := lt_of_lt_of_le zero_lt_one (hd₂ i hi)
  have hd : 0<d₁ i*d₂ i := mul_pos h₁ h₂
  have hl : 0<L/(d₁ i*d₂ i) := div_pos hL hd
  have lo₁ := divisor_common_lower L X₁ (d₁ i) (d₂ i) hL.le hX₁ (hd₁ i hi) (hd₂ i hi)
  have lo₂ := divisor_common_lower L X₂ (d₂ i) (d₁ i) hL.le hX₂ (hd₂ i hi) (hd₁ i hi)
  have loy₁ := divisor_common_lower L Y₁ (d₁ i) (d₂ i) hL.le hY₁ (hd₁ i hi) (hd₂ i hi)
  have loy₂ := divisor_common_lower L Y₂ (d₂ i) (d₁ i) hL.le hY₂ (hd₂ i hi) (hd₁ i hi)
  rw [mul_comm (d₂ i) (d₁ i)] at lo₂ loy₂
  have heX : (X₁/d₁ i)*(X₂/d₂ i)=T/(d₁ i*d₂ i) := by
    rw [div_mul_div_comm,hpX]
  have heY : (Y₁/d₁ i)*(Y₂/d₂ i)=T/(d₁ i*d₂ i) := by
    rw [div_mul_div_comm,hpY]
  have hc := hchild _ _ _ _ _ _ hl lo₁ lo₂ loy₁ loy₂ heX heY
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hc (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).trans_eq
  calc
    _ = (‖w i‖*A)*((Real.sqrt (d₁ i*d₂ i))⁻¹*
        (Real.sqrt (T/(d₁ i*d₂ i))*(L/(d₁ i*d₂ i))^(-α))) := by ring
    _ = _ := by rw [centered_divisor_scalar T L (d₁ i*d₂ i) α hT hL hd];ring

/-- Uniform source control for every exact finite divisor expansion of the
ordinary centered rectangle, with the original fixed-inducing and row data. -/
theorem rectangle_divisor_sum_source_control_fractional (a b ε B α : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B)
    (hα0 : 0≤α) (hα1 : α≤1) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ →L≤X₂ →L≤Y₁ →L≤Y₂ →X₁*X₂=T →Y₁*Y₂=T →
      ∀ (ι : Type) (D : Finset ι) (d₁ d₂ : ι→ℝ) (w : ι→ℂ),
      (∀i∈D,1≤d₁ i) →(∀i∈D,1≤d₂ i) →
      ‖∑i∈D,(w i/(Real.sqrt (d₁ i*d₂ i):ℂ))*
        centeredRectangle χ W₁ W₂ t (X₁/d₁ i) (X₂/d₂ i) (Y₁/d₁ i) (Y₂/d₂ i)
          (T/(d₁ i*d₂ i))‖≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          Real.sqrt T*L^(-α)*(∑i∈D,‖w i‖/(d₁ i*d₂ i)^(1-α)) := by
  obtain ⟨J,S,hS,hsource⟩ := rectangle_source_control_fractional a b ε B α ha hb hε hB hα0 hα1
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY ι D d₁ d₂ w hd₁ hd₂
  have hcontrol : 0≤sourceControl S W₁*sourceControl S W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  apply centered_divisor_transport D χ W₁ W₂ t X₁ X₂ Y₁ Y₂ T L α
    (C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J)
    hT hL hX₁ hX₂ hY₁ hY₂ hpX hpY d₁ d₂ w hd₁ hd₂
  intro x₁ x₂ y₁ y₂ t' l hl hx₁ hx₂ hy₁ hy₂ hpx hpy
  exact hsource W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t x₁ x₂ y₁ y₂ t' l hl hx₁ hx₂ hy₁ hy₂ hpx hpy

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.centered_divisor_scalar
#print axioms OAI.SevenEighths.Record1252270103Source.centered_divisor_transport
#print axioms OAI.SevenEighths.Record1252270103Source.rectangle_divisor_sum_source_control_fractional
