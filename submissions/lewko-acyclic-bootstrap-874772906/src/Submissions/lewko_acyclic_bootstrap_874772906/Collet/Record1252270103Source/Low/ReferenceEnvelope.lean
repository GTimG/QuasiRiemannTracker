/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Adapted from OpenAI/math ReferenceProfileBudget (Apache-2.0), retaining two
independent plain heights in all three envelopes. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyReferenceProfileBudget

theorem independent_reference_envelopes (a b:ℝ)(ha:0<a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0<Cref)(hDc:0<Dchild)(hDr:0<Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀u t height:ℝ,0≤height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|u|+|t|+height)^J;
      ((independentProfiles ha W₂ W₁ hs₂ hs₁ u t).control S)^2*(1+|t|+height)^degree≤E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖u‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖u‖)^(2*nlong)≤E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ u t height hheight
  dsimp only
  let H:=1+|u|+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg u,abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hA:0≤A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₂ W₁ hs₂ hs₁ u t).control S≤Ca*A*(2*H)^(2*na):=by
    apply (hprof W₂ W₁ hs₂ hs₁ u t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      simpa only [mul_comm] using mul_le_mul (control_mono haU W₂) (control_mono haU W₁)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg u,abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₂ W₁ hs₂ hs₁ u t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖u‖)^(2*nlong)≤H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith [abs_nonneg t]
  have hcm: Cref*Dchild≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤C:=by dsimp only [C];nlinarith
  have htd : (1+|t|+height)^degree ≤ H^degree := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    linarith [abs_nonneg u]
  refine ⟨(mul_le_mul_of_nonneg_left htd (sq_nonneg _)).trans
    (hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J))),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖u‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)):=by ring
      _≤C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by
        gcongr
        dsimp only [H]
        linarith [abs_nonneg u]
      _≤C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖u‖)^(2*nlong):=by ring
      _≤C*A^2*H^(2*nlong):=by gcongr
      _≤C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

/-- Extra arbitrary reflection decay pays every short exponent up to Mcap. -/
theorem decay_short_le (Z saving Mcap width short : ℝ) (hZ : 1 ≤ Z)
    (hMcap : 0 ≤ Mcap) (hwidth : 0 ≤ width) (hshort : short ≤ Mcap) :
    Z^(-2*(saving+Mcap))*Z^short ≤ Z^(-2*saving)*Z^(width/4) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [←Real.rpow_add hz, ←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.independent_reference_envelopes
#print axioms OAI.SevenEighths.Record1252270103Low.decay_short_le
