/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Elementary centered lattice control for exact divisor transport. The full
ordinary rectangle is retained until equal-product cancellation is applied. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalRectangle

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CenteredMomentHeckeTwist CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem centered_rectangle_absolute
    (χ : Character) (W₁ W₂ : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
      twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
      (2*(128*b)^2)*(sourceControl S W₁*sourceControl S W₂)*Real.sqrt T := by
  have hbound (W : 𝓢(ℝ,ℂ)) (x : ℝ) : ‖W x‖ ≤ sourceControl S W := by
    have hsup : (schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W ≤
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS
    exact (SchwartzMap.norm_le_seminorm ℝ W x).trans hsup
  have h₁ (X : ℝ) (hX : 0<X) := twistedIdealSum_absolute χ W₁ a b
    (sourceControl S W₁) ha hb (sourceControl_nonneg _ _) hs₁ (W₁.smooth ⊤)
    (hbound W₁) t X hX
  have h₂ (X : ℝ) (hX : 0<X) := twistedIdealSum_absolute χ W₂ a b
    (sourceControl S W₂) ha hb (sourceControl_nonneg _ _) hs₂ (W₂.smooth ⊤)
    (hbound W₂) t X hX
  have hc₁ : 0≤sourceControl S W₁ := sourceControl_nonneg _ _
  have hc₂ : 0≤sourceControl S W₂ := sourceControl_nonneg _ _
  have hp (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (hXY : X*Y=T) :
      ‖twistedIdealSum χ W₁ t X*twistedIdealSum χ W₂ t Y‖ ≤
        (128*b)^2*(sourceControl S W₁*sourceControl S W₂)*T := by
    rw [norm_mul]
    apply (mul_le_mul (h₁ X hX) (h₂ Y hY) (norm_nonneg _) (by positivity)).trans_eq
    rw [←hXY]
    ring
  have hD := (norm_sub_le _ _).trans (add_le_add (hp X₁ X₂ hX₁ hX₂ hpX)
    (hp Y₁ Y₂ hY₁ hY₂ hpY))
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsqrt : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg T)]
  apply (mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr hsqrt.le)).trans_eq
  have he := Real.mul_self_sqrt hT.le
  have hsq : (Real.sqrt T)^2=T := by nlinarith [he]
  field_simp
  rw [hsq]
  ring

/-- Ordinary equal-product cancellation with every fractional saving 0≤α≤1.
The estimate is valid at subunit scales too, by interpolation with the true
absolute bound; no lower-scale truncation has been inserted. -/
theorem rectangle_source_control_fractional (a b ε B α : ℝ)
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
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          Real.sqrt T*L^(-α) := by
  obtain ⟨J,S,hS,hsource⟩ := rectangle_source_control a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hsource Q hQ
  let C' := C+2*(128*b)^2+1
  have hC' : 0<C' := by dsimp [C']; positivity
  have hCC : C≤C' := by dsimp [C']; nlinarith [sq_nonneg (128*b)]
  refine ⟨C',hC',?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hcontrol : 0≤sourceControl S W₁*sourceControl S W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hZpow : 1≤Z^ε := Real.one_le_rpow hZ hε.le
  have ht : 1≤(1+‖t‖)^J := one_le_pow₀ (by linarith [norm_nonneg t])
  by_cases hLone : 1≤L
  · have hrpow : L⁻¹≤L^(-α) := by
      rw [←Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
    apply (hbound W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
    rw [div_eq_mul_inv,←mul_assoc]
    gcongr
  · have hrpow : 1≤L^(-α) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hL (le_of_not_ge hLone) (by linarith)
    have habs := centered_rectangle_absolute χ W₁ W₂ S hS a b ha hb hs₁ hs₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply habs.trans
    calc
      _ ≤ C'*(sourceControl S W₁*sourceControl S W₂)*Real.sqrt T := by
        gcongr
        dsimp [C']
        linarith
      _ ≤ C'*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          Real.sqrt T*L^(-α) := by
        have hprod : 1≤Z^ε*(1+‖t‖)^J*L^(-α) :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hZpow ht) hrpow
        have hh := mul_le_mul_of_nonneg_left hprod
          (show 0≤C'*(sourceControl S W₁*sourceControl S W₂)*Real.sqrt T by positivity)
        convert hh using 1 <;> ring

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.centered_rectangle_absolute
#print axioms OAI.SevenEighths.Record1252270103Source.rectangle_source_control_fractional
