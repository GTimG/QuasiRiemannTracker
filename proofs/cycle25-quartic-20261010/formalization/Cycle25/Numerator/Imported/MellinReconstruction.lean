import OAI.NumberTheory.DirichletL.Hecke.DyadicContour
import OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth
import OAI.NumberTheory.DirichletL.Detector.MellinBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Mellin reconstruction for the actual nonprincipal numerator L-function.
The coefficient index will be arbitrary countable, with positive real scales. -/
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.MellinReconstruction
open HeckeFamily ProbeHighRowFamily ProbeMellinBoundary

def plainIntegrand (χ : Character) (W : ℝ→ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D:ℂ)^(s-(1/2:ℂ)) * LFunction χ s

lemma plainIntegrand_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (s : ℂ) :
    plainIntegrand χ W D s = HeckeDyadic.integrand χ false W D 0 0 s := by
  simp [plainIntegrand,HeckeDyadic.integrand,HeckeDyadic.shift,HeckeDyadic.series]

lemma plainIntegrand_differentiableAt (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0<D) (s : ℂ) :
    DifferentiableAt ℂ (plainIntegrand χ W D) s := by
  have heq : plainIntegrand χ W D = HeckeDyadic.integrand χ false W D 0 0 :=
    funext (plainIntegrand_eq χ W D)
  rw [heq]
  exact HeckeDyadic.integrand_differentiableAt χ false W a b ha hsupp hW D 0 0 hD
    (HeckeDyadic.series_differentiableAt_nonprincipal χ hχ false (by intro hh; cases hh))

/-- A common integrable envelope for the Mellin transform times L on the full strip. -/
theorem mellin_L_cauchy (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0≤C ∧ ∀v∈Icc (1/2:ℝ) 2,∀t : ℝ,
      ‖mellin W ((v:ℂ)+t*I)*LFunction χ ((v:ℂ)+t*I)‖≤C*cauchy t := by
  obtain ⟨A,hA,hgrowth⟩ := nonprincipal_positive_growth (1/2) 1 (by norm_num) (by norm_num)
  obtain ⟨D,hD,hdecay⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hsupp hW (1/2) 2 4
  let B := A*(χ.modulus.absNorm:ℝ)^(3/5+1:ℝ)
  have hB : 0≤B := by dsimp [B];positivity
  refine ⟨9*B*D,by positivity,?_⟩
  intro v hv t
  have hg := hgrowth χ hχ ((v:ℂ)+t*I) (by simpa using hv.1)
  simp only [HeckeOrigin.continued,ite_eq_right hχ,add_im,ofReal_im,mul_im,
    ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hg
  change ‖LFunction χ ((v:ℂ)+t*I)‖≤B*(3+|t|)^2 at hg
  have hpow : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  have hg' : ‖LFunction χ ((v:ℂ)+t*I)‖≤9*B*(height t)^2 :=
    hg.trans ((mul_le_mul_of_nonneg_left hpow hB).trans_eq (by ring))
  have hm : (height t)^4*‖mellin W ((v:ℂ)+t*I)‖≤D := by
    simpa only [height] using hdecay v hv t
  apply CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t
  rw [norm_mul]
  calc
    _ ≤ (height t)^2*(‖mellin W ((v:ℂ)+t*I)‖*(9*B*(height t)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (norm_nonneg _)) (sq_nonneg _)
    _ = 9*B*((height t)^4*‖mellin W ((v:ℂ)+t*I)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem plainIntegrand_cauchy (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0<D) :
    ∃C : ℝ,0≤C ∧ ∀v∈Icc (1/2:ℝ) 2,∀t : ℝ,
      ‖plainIntegrand χ W D ((v:ℂ)+t*I)‖≤C*cauchy t := by
  obtain ⟨C,hC,hbound⟩ := mellin_L_cauchy χ hχ W a b ha hsupp hW
  refine ⟨scaleBound D 0 (3/2)*C,mul_nonneg (scaleBound_pos _ _ _).le hC,?_⟩
  intro v hv t
  have hd := cpow_le_scaleBound hD (((v:ℂ)+t*I)-(1/2:ℂ))
    (show (((v:ℂ)+t*I)-(1/2:ℂ)).re∈Icc 0 (3/2) by simp;constructor <;> linarith [hv.1,hv.2])
  have heq : plainIntegrand χ W D ((v:ℂ)+t*I)=
      (D:ℂ)^(((v:ℂ)+t*I)-(1/2:ℂ))*(mellin W ((v:ℂ)+t*I)*LFunction χ ((v:ℂ)+t*I)) := by
    unfold plainIntegrand;ring
  rw [heq,norm_mul]
  exact (mul_le_mul hd (hbound v hv t) (norm_nonneg _) (scaleBound_pos _ _ _).le).trans_eq (by ring)

theorem plainIntegrand_vertical_integrable (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0<D) (v : ℝ) (hv : v∈Icc (1/2:ℝ) 2) :
    Integrable (fun t : ℝ=>plainIntegrand χ W D ((v:ℂ)+t*I)) := by
  obtain ⟨C,hC,hbound⟩ := plainIntegrand_cauchy χ hχ W a b ha hsupp hW D hD
  have hc : Continuous (fun t : ℝ=>plainIntegrand χ W D ((v:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (plainIntegrand_differentiableAt χ hχ W a b ha hsupp hW D hD _).continuousAt.comp (by fun_prop)
  exact (cauchy_integrable.const_mul C).mono' hc.aestronglyMeasurable (ae_of_all _ (hbound v hv))

/-- Exact inversion on Re(w)=1/2 for the original dyadic polynomial. -/
theorem polynomial_central_mellin (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0<D) :
    HeckeDyadic.polynomial χ false W D 0 0 = (1/(2*Real.pi):ℂ)*
      ∫t : ℝ,plainIntegrand χ W D ((1/2:ℂ)+t*I) := by
  obtain ⟨C,hC,hbound⟩ := plainIntegrand_cauchy χ hχ W a b ha hsupp hW D hD
  have heq := Continuation.vertical_integral_eq_of_even_envelope
    (plainIntegrand χ W D) cauchy cauchy_integrable (by intro t;simp [cauchy])
    cauchy_tendsto (by norm_num : (1/2:ℝ)≤2)
    (fun s _=>(plainIntegrand_differentiableAt χ hχ W a b ha hsupp hW D hD s).differentiableWithinAt) hbound
  rw [HeckeDyadic.polynomial_mellin χ false W a b ha hsupp hW D 2 0 0 hD (by norm_num)]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_zero,add_zero,HeckeDyadic.series,Bool.false_eq_true,ite_false,Complex.ofReal_ofNat]
  change (1/(2*Real.pi):ℂ)*(∫t : ℝ,plainIntegrand χ W D ((2:ℂ)+t*I))=_
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] using congrArg (fun z=>(1/(2*Real.pi):ℂ)*z) heq.symm

lemma coefficient_line_norm (A : ℂ) (N c t : ℝ) (hN : 0<N) :
    ‖A*(N:ℂ)^(-((c:ℂ)+t*I))‖=‖A‖*N^(-c) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

/-- Absolute mass also proves genuine integrability of the whole coefficient
series, which is needed before separating finite error subsets. -/
theorem coefficient_series_integrable {κ : Type*}
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0<N i) (c : ℝ)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-c)))
    (g : ℝ→ℂ) (hg : Integrable g) :
    Integrable (fun t : ℝ=>g t*(∑'i,A i*(N i:ℂ)^(-((c:ℂ)+t*I)))) := by
  have hc (i : κ) : Continuous (fun t : ℝ=>A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
    exact continuous_const.mul ((show Continuous (fun t : ℝ=>-((c:ℂ)+t*I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne')))
  have hs := continuous_tsum hc hmass (fun i t=>(coefficient_line_norm (A i) (N i) c t (hN i)).le)
  apply hg.mul_bdd hs.aestronglyMeasurable
  apply ae_of_all
  intro t
  have hn : Summable (fun i=>‖A i*(N i:ℂ)^(-((c:ℂ)+t*I))‖) := by
    simpa only [coefficient_line_norm _ _ _ _ (hN _)] using hmass
  simpa only [coefficient_line_norm _ _ _ _ (hN _)] using norm_tsum_le_tsum_norm hn

/-- Countable coefficient interchange uses absolute mass on the exact w line. -/
theorem coefficient_integral_interchange {κ : Type*} [Countable κ]
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0<N i) (c : ℝ)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-c)))
    (g : ℝ→ℂ) (hg : Integrable g) :
    (∫t : ℝ,g t*(∑'i,A i*(N i:ℂ)^(-((c:ℂ)+t*I))))=
      ∑'i,∫t : ℝ,g t*(A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
  let F := fun i t=>g t*(A i*(N i:ℂ)^(-((c:ℂ)+t*I)))
  have hi (i : κ) : Integrable (F i) := by
    have hc : Continuous (fun t : ℝ=>A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
      exact continuous_const.mul ((show Continuous (fun t : ℝ=>-((c:ℂ)+t*I)) by fun_prop).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne')))
    exact hg.mul_bdd hc.aestronglyMeasurable
      (ae_of_all _ (fun t=>(coefficient_line_norm (A i) (N i) c t (hN i)).le))
  have hint (i : κ) : (∫t : ℝ,‖F i t‖)=(∫t : ℝ,‖g t‖)*(‖A i‖*(N i)^(-c)) := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i)]
    simp only [neg_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
    rw [←integral_mul_const]
  have hs : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp_rw [hint]
    exact hmass.mul_left _
  simp_rw [←tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm hi hs).symm

lemma reconstruction_scale (Y N : ℝ) (hY : 0<Y) (hN : 0<N) (w : ℂ) :
    (Y:ℂ)^(w-1)*(N:ℂ)^(-w)=
      (Y:ℂ)^(-(1/2:ℂ))*(N:ℂ)^(-(1/2:ℂ))*((Y/N:ℝ):ℂ)^(w-(1/2:ℂ)) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hY.le hN.le]
  simp only [div_eq_mul_inv]
  rw [←Complex.cpow_neg]
  symm
  calc
    _ = ((Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(w-(1/2:ℂ)))*
        ((N:ℂ)^(-(1/2:ℂ))*(N:ℂ)^(-(w-(1/2:ℂ)))) := by ring
    _ = _ := by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY.ne'),
        ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hN.ne')]
      congr 2 <;> ring

lemma coefficient_kernel_identity (χ : Character) (W : ℝ→ℂ) (A : ℂ)
    (Y N : ℝ) (hY : 0<Y) (hN : 0<N) (w : ℂ) :
    (Y:ℂ)^(w-1)*mellin W w*LFunction χ w*(A*(N:ℂ)^(-w))=
      ((Y:ℂ)^(-(1/2:ℂ))*(A*(N:ℂ)^(-(1/2:ℂ))))*plainIntegrand χ W (Y/N) w := by
  have hs := reconstruction_scale Y N hY hN w
  unfold plainIntegrand
  calc
    _ = ((Y:ℂ)^(w-1)*(N:ℂ)^(-w))*(A*mellin W w*LFunction χ w) := by ring
    _ = _ := by rw [hs];ring

/-- Reconstruction of one coefficient at its physical scale Y/N. -/
theorem coefficient_central_mellin (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (A : ℂ) (Y N : ℝ) (hY : 0<Y) (hN : 0<N) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*LFunction χ ((1/2:ℂ)+t*I)*
        (A*(N:ℂ)^(-((1/2:ℂ)+t*I))))=
      (Y:ℂ)^(-(1/2:ℂ))*(A*(N:ℂ)^(-(1/2:ℂ)))*HeckeDyadic.polynomial χ false W (Y/N) 0 0 := by
  simp_rw [coefficient_kernel_identity χ W A Y N hY hN]
  rw [integral_const_mul,polynomial_central_mellin χ hχ W a b ha hsupp hW (Y/N) (div_pos hY hN)]
  ring

lemma reconstruction_kernel_integrable (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
      LFunction χ ((1/2:ℂ)+t*I)) := by
  have hi := (plainIntegrand_vertical_integrable χ hχ W a b ha hsupp hW Y hY (1/2) ⟨le_rfl,by norm_num⟩).const_mul
    ((Y:ℂ)^(-(1/2:ℂ)))
  apply hi.congr
  apply ae_of_all
  intro t
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  unfold plainIntegrand
  have hpow : (Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(((1/2:ℂ)+t*I)-(1/2:ℂ))=
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY.ne')]
    congr 1
    ring
  calc
    _ = ((Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(((1/2:ℂ)+t*I)-(1/2:ℂ)))*
        mellin W ((1/2:ℂ)+t*I)*LFunction χ ((1/2:ℂ)+t*I) := by ring
    _ = _ := by rw [hpow]

/-- Actual L-function reconstruction with any countable coefficient index. -/
theorem weighted_numerator_mellin {κ : Type*} [Countable κ]
    (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y)
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0<N i)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-(1/2:ℝ)))) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*HeckeOrigin.continued χ ((1/2:ℂ)+t*I)*
        (∑'i,A i*(N i:ℂ)^(-((1/2:ℂ)+t*I))))=
      (Y:ℂ)^(-(1/2:ℂ))*∑'i,A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 := by
  simp only [HeckeOrigin.continued,ite_eq_right hχ]
  have hint := coefficient_integral_interchange A N hN (1/2) hmass _
    (reconstruction_kernel_integrable χ hχ W a b ha hsupp hW Y hY)
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hint
  rw [hint,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro i
  simpa only [mul_assoc] using coefficient_central_mellin χ hχ W a b ha hsupp hW (A i) Y (N i) hY (hN i)


/-- Absolute summability survives the actual Mellin reconstruction.  The common
integrable Mellin--L envelope bounds every coefficient before inversion. -/
theorem reconstructed_series_norm_summable {κ : Type*}
    (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y)
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0<N i)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-(1/2:ℝ)))) :
    Summable (fun i=>‖A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0‖) := by
  let g (t : ℝ) := (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
    LFunction χ ((1/2:ℂ)+t*I)
  let F (i : κ) (t : ℝ) := g t*(A i*(N i:ℂ)^(-((1/2:ℂ)+t*I)))
  have hint (i : κ) : (∫t : ℝ,‖F i t‖)=(∫t : ℝ,‖g t‖)*(‖A i‖*(N i)^(-(1/2:ℝ))) := by
    have hr (t : ℝ) : (-((1/2:ℂ)+t*I)).re=-(1/2:ℝ) := by simp
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),hr]
    rw [integral_mul_const]
  have hs : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp_rw [hint]
    exact hmass.mul_left _
  have hi : Summable (fun i=>‖∫t : ℝ,F i t‖) :=
    hs.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>norm_integral_le_integral_norm _)
  have hn := hi.mul_left ‖(1/(2*Real.pi):ℂ)‖
  have hid (i : κ) : (1/(2*Real.pi):ℂ)*(∫t : ℝ,F i t)=
      (Y:ℂ)^(-(1/2:ℂ))*(A i*(N i:ℂ)^(-(1/2:ℂ)))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 :=
    coefficient_central_mellin χ hχ W a b ha hsupp hW (A i) Y (N i) hY (hN i)
  simp_rw [←norm_mul,hid,mul_assoc,norm_mul] at hn
  have hy : ‖(Y:ℂ)^(-(1/2:ℂ))‖≠0 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    exact (Real.rpow_pos_of_pos hY _).ne'
  apply (summable_mul_left_iff hy).mp
  simpa only [norm_mul,mul_assoc] using hn

/-- Compact support cuts off the actual numerator before reflection. -/
theorem polynomial_zero_of_scale_cutoff (χ : Character) (W : ℝ→ℂ)
    (a b Y N : ℝ) (hsupp : Function.support W⊆Icc a b)
    (hY : 0<Y) (hN : 0<N) (hcut : b*Y<N) :
    HeckeDyadic.polynomial χ false W (Y/N) 0 0=0 := by
  unfold HeckeDyadic.polynomial
  suffices hh : (∑'J : HeckeDyadic.NonzeroIdeal,HeckeDyadic.summand χ false W (Y/N) 0 0 J)=0 by
    rw [hh,mul_zero]
  suffices hzero : ∀J : HeckeDyadic.NonzeroIdeal,HeckeDyadic.summand χ false W (Y/N) 0 0 J=0 by
    simp only [hzero,tsum_zero]
  intro J
  have hJ : 1≤HeckeDyadic.norm J := by
    have hj := HeckeDyadic.norm_pos J
    unfold HeckeDyadic.norm at *
    exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hj) : 1≤J.val.absNorm)
  have harg : b<HeckeDyadic.norm J/(Y/N) := by
    rw [div_div_eq_mul_div]
    apply (lt_div_iff₀ hY).mpr
    exact hcut.trans_le (le_mul_of_one_le_left hN.le hJ)
  have hz : W (HeckeDyadic.norm J/(Y/N))=0 := by
    by_contra hn
    exact (not_le_of_gt harg) (hsupp hn).2
  simp [HeckeDyadic.summand,hz]

/-- The countable reconstructed sum has no contribution at N>bY. -/
theorem reconstruction_exact_cutoff {κ : Type*} [Countable κ]
    (χ : Character) (W : ℝ→ℂ) (a b Y : ℝ) (hsupp : Function.support W⊆Icc a b)
    (hY : 0<Y) (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0<N i) :
    (∑'i,A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0)=
      ∑'i,if N i≤b*Y then
        A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 else 0 := by
  apply tsum_congr
  intro i
  split_ifs with hi
  · rfl
  · rw [polynomial_zero_of_scale_cutoff χ W a b Y (N i) hsupp hY (hN i) (lt_of_not_ge hi),mul_zero]

end Cycle25.Weighted.MellinReconstruction
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
