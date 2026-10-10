import Cycle25.Numerator.Imported.FullWReconstruction

/-! Uniform integration of the two remaining Mellin variables after inversion. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open ProbePhysical ProbeMellinBoundary EisensteinSchwartzPoisson

def szProfile (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (q : ℝ×ℝ) : ℂ :=
  Complex.exp ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2)*
    mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)

def szEnvelope (J : ℕ) (q : ℝ×ℝ) : ℝ :=
  gaussianMoment J (q.1+q.2)*cauchy q.2

lemma szEnvelope_nonneg (J : ℕ) (q : ℝ×ℝ) : 0 ≤ szEnvelope J q :=
  mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)

lemma szEnvelope_integrable (J : ℕ) : Integrable (szEnvelope J) (volume.prod volume) := by
  have hp : MeasurePreserving (fun q : ℝ×ℝ=>(q.1+q.2,q.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 := measurePreserving_prod_add_swap (volume : Measure ℝ) (volume : Measure ℝ)
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  exact hp.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)

lemma szProfile_norm (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (q : ℝ×ℝ) :
    ‖szProfile W0 σ r q‖=Real.exp ((σ+r-1)^2)*Real.exp (-((q.1+q.2)^2))*
      ‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖ := by
  unfold szProfile
  rw [norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2).re=
      (σ+r-1)^2+(-((q.1+q.2)^2)) := by simp [pow_two];ring
  rw [hr,Real.exp_add]

lemma szProfile_continuous (W0 : SchwartzMap ℝ ℂ) (σ r : ℝ) (hr : 0<r) :
    Continuous (szProfile W0 σ r) := by
  have hR : Continuous (fun t : ℝ=>mellin (paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  exact (by fun_prop : Continuous (fun q : ℝ×ℝ=>
    Complex.exp ((((σ:ℂ)+q.1*I)+((r:ℂ)+q.2*I)-1)^2))).mul (hR.comp continuous_snd)

lemma szProfile_moment_majorant (W0 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi rlo rhi σ r C : ℝ} (hσ : σ∈Icc slo shi) (hr : r∈Icc rlo rhi)
    (hC : 0≤C)
    (hR : ∀v : ℝ,height v^(J+2)*‖mellin (paperRadialFourier W0) ((r:ℂ)+v*I)‖≤C)
    (q : ℝ×ℝ) :
    jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖≤
      (realGaussianBound slo shi rlo rhi*2^J*C)*szEnvelope J q := by
  have hb := weighted_coupled_cauchy J q.1 q.2 0
    ‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖ 1 C 1
    (norm_nonneg _) (by norm_num) hC (by norm_num) (hR _) (by simp [height])
  simp only [mul_one,cauchy,zero_pow (by decide : 2≠0),add_zero,inv_one] at hb
  rw [szProfile_norm]
  calc
    _ = Real.exp ((σ+r-1)^2)*(jointHeight q.1 q.2 0^J*
        Real.exp (-((q.1+q.2)^2))*‖mellin (paperRadialFourier W0) ((r:ℂ)+q.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi rlo rhi*((2:ℝ)^J*C*szEnvelope J q) :=
      mul_le_mul (realGaussian_le hσ hr) hb (by
        have hh := (jointHeight_pos q.1 q.2 0).le
        positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by ring

theorem szProfile_uniform_moments (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (slo shi rlo rhi : ℝ) (hrlo : 0<rlo) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Icc slo shi,∀r∈Icc rlo rhi,
      Integrable (fun q : ℝ×ℝ=>jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖ ∂(volume.prod volume))≤C := by
  obtain ⟨D,hD,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 rlo rhi hrlo (J+2)
  let A := realGaussianBound slo shi rlo rhi*2^J*D
  have hA : 0<A := by dsimp [A];exact mul_pos (mul_pos (realGaussianBound_pos _ _ _ _) (by positivity)) hD
  refine ⟨A*(1+|∫q,szEnvelope J q ∂(volume.prod volume)|),by positivity,?_⟩
  intro σ hσ r hr
  have hb := szProfile_moment_majorant W0 J hσ hr hD.le (hR r hr)
  have hc := szProfile_continuous W0 σ r (hrlo.trans_le hr.1)
  have hi : Integrable (fun q : ℝ×ℝ=>jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) (volume.prod volume) := by
    apply ((szEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight;fun_prop : Continuous (fun q : ℝ×ℝ=>jointHeight q.1 q.2 0^J)).mul
        hc.norm).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro q
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))]
      exact hb q
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q,A*szEnvelope J q ∂(volume.prod volume) :=
      integral_mono hi ((szEnvelope_integrable J).const_mul A) hb
    _ = A*(∫q,szEnvelope J q ∂(volume.prod volume)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∫q,szEnvelope J q ∂(volume.prod volume))]) hA.le

lemma sourceSZWeight_norm (W0 : SchwartzMap ℝ ℂ) (X Z σ r : ℝ)
    (hX : 0<X) (hZ : 0<Z) (q : ℝ×ℝ) :
    ‖sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)‖=
      X^(1/2-r)*Z^(σ+r-1)*‖szProfile W0 σ r q‖ := by
  simp only [sourceSZWeight,szProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,mul_zero,zero_mul,sub_zero,add_zero]
  norm_num
  ring

/-- Any proved numerator bound can be integrated with no loss in the contour height. -/
theorem sourceSZ_uniform_integral_bound (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (slo shi rlo rhi : ℝ) (hrlo : 0<rlo) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Icc slo shi,∀r∈Icc rlo rhi,
      ∀X Z : ℝ,0<X→0<Z→∀H A : ℝ,0≤A→∀G : (ℝ×ℝ)→ℂ,
      IntegrableOn (fun q=>sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q)
        (szRectangle H) (volume.prod volume)→
      (∀q∈szRectangle H,‖G q‖≤A*jointHeight q.1 q.2 0^J)→
      ‖∫q in szRectangle H,sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q
        ∂(volume.prod volume)‖≤C*X^(1/2-r)*Z^(σ+r-1)*A := by
  obtain ⟨C,hC,hprofile⟩ := szProfile_uniform_moments W0 a0 b0 ha0 hW0 slo shi rlo rhi hrlo J
  refine ⟨C,hC,?_⟩
  intro σ hσ r hr X Z hX hZ H A hA G hG hbound
  obtain ⟨hp,hpbound⟩ := hprofile σ hσ r hr
  let scale : ℝ := X^(1/2-r)*Z^(σ+r-1)
  have hs : 0 ≤ scale := by dsimp [scale];positivity
  have hi := hp.const_mul (scale*A)
  have hn : ∀q : ℝ×ℝ,0≤(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖) := by
    intro q
    exact mul_nonneg (mul_nonneg hs hA)
      (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
  calc
    _ ≤ ∫q in szRectangle H,‖sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*G q‖
        ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫q in szRectangle H,(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖)
        ∂(volume.prod volume) := by
      apply integral_mono_ae hG.norm hi.integrableOn
      filter_upwards [ae_restrict_mem (szRectangle_measurable H)] with q hq
      rw [norm_mul,sourceSZWeight_norm W0 X Z σ r hX hZ]
      calc
        _ ≤ (scale*‖szProfile W0 σ r q‖)*(A*jointHeight q.1 q.2 0^J) :=
          mul_le_mul_of_nonneg_left (hbound q hq) (mul_nonneg hs (norm_nonneg _))
        _ = _ := by ring
    _ ≤ ∫q,(scale*A)*(jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖)
        ∂(volume.prod volume) := setIntegral_le_integral hi (Filter.Eventually.of_forall hn)
    _ = (scale*A)*(∫q,jointHeight q.1 q.2 0^J*‖szProfile W0 σ r q‖ ∂(volume.prod volume)) :=
      integral_const_mul _ _
    _ ≤ (scale*A)*C := mul_le_mul_of_nonneg_left hpbound (mul_nonneg hs hA)
    _ = _ := by dsimp [scale];ring

end Cycle25.Weighted.FullWContour
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
