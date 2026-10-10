/- Adapted from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Cycle25.Assembly.Transport.GeometryFacts
import Cycle25.Assembly.Transport.PrincipalRemainderContours
import OAI.NumberTheory.DirichletL.Detector.PrincipalTransport
noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Cycle25.Transport.PrincipalTransport
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalTransport
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Cycle25.Transport.PrincipalFiniteProduct Cycle25.Transport.PrincipalFiniteProductX Cycle25.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t  ≤  (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _  ≤  ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert shifted_gaussian_top n (-v) using 1
  funext t
  rw [←gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a ≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖ ≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖ ≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (hβ : HeckeZeroSupremum.beta<a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0 ≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖ ≤ A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith [Cycle25.Transport.theta_bounds]) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0 ≤ A := Cycle25.Transport.PrincipalContours.arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith [Cycle25.Transport.theta_bounds])
  have hB : 0 ≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [Cycle25.Transport.theta_bounds, hξ.1],hξ.2⟩
  have hw : (2:ℝ) ≤ ‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1 ≤ ‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0 ≤ 6*ξ-1 := by linarith [Cycle25.Transport.theta_bounds, hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [Cycle25.Transport.theta_bounds, hξ.1]) h
  have hb := Cycle25.Transport.PrincipalContours.arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith [Cycle25.Transport.theta_bounds]) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←Cycle25.Transport.PrincipalContours.arithmetic_profile_eq_source,norm_mul]
  calc
    _  ≤  (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _  ≤  A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := Cycle25.Transport.PrincipalFiniteProductX.continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ) ≤ ξ by linarith [Cycle25.Transport.theta_bounds])) ha hβ
    (c:=3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25<z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25<z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0<z.re; change (4/25:ℝ)<z.re at hz; linarith [Cycle25.Transport.theta_bounds])
  have hH := (Cycle25.Transport.PrincipalFiniteProduct.combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : theta  ≤  s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6<z.re} := by
  have hK := continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)<z.re; change (1/6:ℝ)<z.re at hz; linarith [Cycle25.Transport.theta_bounds])).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith [Cycle25.Transport.theta_bounds]
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith [Cycle25.Transport.theta_bounds]
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)<z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _  ≤  A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _  ≤  A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := Cycle25.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith [Cycle25.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Cycle25.Transport.theta_bounds]) (by norm_num)
  have hi3 := Cycle25.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds])) (hβ.trans_le ha3) (by linarith [Cycle25.Transport.theta_bounds])
    (by norm_num) (by norm_num) (by linarith [Cycle25.Transport.theta_bounds]) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta  ≤  a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := Cycle25.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith [Cycle25.Transport.theta_bounds]) (by norm_num) (by norm_num) (by linarith [Cycle25.Transport.theta_bounds]) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := Cycle25.Transport.PrincipalContours.continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [Cycle25.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith [Cycle25.Transport.theta_bounds]) (by linarith [Cycle25.Transport.theta_bounds])
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  exact (source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (Cycle25.Transport.PrincipalContours.source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

theorem source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (Cycle25.Transport.PrincipalContours.source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by first | (solve | norm_num) | (linarith [Cycle25.Transport.theta_bounds])) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end Cycle25.Transport.PrincipalTransport
end

