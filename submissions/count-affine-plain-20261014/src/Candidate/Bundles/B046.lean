/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B044
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.MellinBoundary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicContour
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.FullWAggregate; sha256 0b17703036a379b28233be37d8a4972c0e2c62ea8a4d830b0be26abb783ef0b1 -/
section
                                                  
                                                               

/-! The actual weighted physical finite sum with the full numerator integral. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def fullWWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  (fullWSlab H).indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50))

theorem fullWWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fullWWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continued_kernel_strip_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (1/2) (17/50) le_rfl (by linarith) le_rfl (by linarith)
  let E := fullWSlab H
  have hE : MeasurableSet E := fullWSlab_measurable H
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1/2) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=>ht.1.1)).const_mul _

lemma fullWWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,fullWWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1/2) := by
  have hE : MeasurableSet (fullWSlab H) := fullWSlab_measurable H
  unfold fullWWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralFullWIntegral
  ring

theorem finiteCentralFullWRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      fullWWeightedRow S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := fullWWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact fullWWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=>hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralFullWRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (fullWWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm


end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.FullWAggregate -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.MellinReconstruction; sha256 b7d0faf376435484e06de73d22cdd38501e5cbf5e9b24cc1bcf9893770e58386 -/
section
                                                      
                                                        
                                                          
                                                          
                                                   

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

end
/- END ORIGINAL Cycle25.Numerator.Imported.MellinReconstruction -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.FullWReconstruction; sha256 d42fb02e80902c8e69b45ff0e792387c4381308f46bcbdfb54c206e672cbe5f6 -/
section
                                                
                                                      

/-! The complete numerator integral is taken before any row amplitude estimate. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

def sourceSZWeight (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z

def rowNumeratorIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∫t : ℝ,(Y:ℂ)^((1/2:ℂ)+t*I-1)*mellin W1 ((1/2:ℂ)+t*I)*
    calibratedTupleValue S hS hmax η u P hPS W Yp s ((1/2:ℂ)+t*I) z

def integratedRowValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  frequencyWeight z ⟨u.val,u.property.1⟩ *
    rowNumeratorIntegral S hS hmax η u P hPS W Yp W1 Y s z

lemma weightedRow_w_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r : ℝ) (q : ℝ×ℝ) :
    (∫t : ℝ,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r (q,t))=
      sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
        integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I) := by
  unfold integratedRowValue rowNumeratorIntegral
  rw [←mul_assoc,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold weightedRowOnLines sourceMellinWeight sourceSZWeight
  norm_num only [ofReal_div,ofReal_one,ofReal_ofNat]
  ring

lemma fullW_inner_integrable (H : ℝ) (f : HeightSpace→ℂ)
    (hf : IntegrableOn f (fullWSlab H) heightMeasure) :
    IntegrableOn (fun q : ℝ×ℝ=>∫t : ℝ,f (q,t)) (szRectangle H) (volume.prod volume) := by
  have hi : Integrable f (((volume.prod volume).restrict (szRectangle H)).prod volume) := by
    simpa only [IntegrableOn,fullWSlab,heightMeasure,←Measure.prod_restrict,Measure.restrict_univ] using hf
  exact hi.integral_prod_left

lemma fullW_factored_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ r H : ℝ)
    (hf : IntegrableOn (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r)
      (fullWSlab H) heightMeasure) :
    let F := fun q : ℝ×ℝ=>sourceSZWeight W0 X Z ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u P hPS W Yp W1 Y ((σ:ℂ)+q.1*I) ((r:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      (∫p in fullWSlab H,weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ (1/2) r p
        ∂heightMeasure) = ∫q in szRectangle H,F q ∂(volume.prod volume) := by
  constructor
  · simpa only [weightedRow_w_integral] using fullW_inner_integrable H _ hf
  · rw [fullWSlab_fubini H _ hf]
    simp_rw [weightedRow_w_integral]

def integratedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ)
    (Y : ℝ) (s z : ℂ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),integratedRowValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i _ (P i).property) W Yp W1 Y s z

theorem finiteFullW_reconstruction {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun q : ℝ×ℝ=>sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
    IntegrableOn F (szRectangle H) (volume.prod volume) ∧
      finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫q in szRectangle H,F q ∂(volume.prod volume)) := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun j=>(P j).val) (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z (a+16*e) (1/2) (17/50)
  let g (u : FreeRow) (P : ∀i,T i) (q : ℝ×ℝ) :=
    sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedRowValue S hS hmax η u (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
        W Yp W1 Y (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : IntegrableOn (f u P) (fullWSlab H) heightMeasure := by
    have hh := fullWWeightedRow_integrable e a B H i he he' ha haTop hB hH S hS hmax hfirst
      (fun j=>(P j).val) (fun j=>hT j _ (P j).property) η u (hR u hu) (ψ u) (hbin u hu)
      W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    change Integrable ((fullWSlab H).indicator (f u P)) heightMeasure at hh
    exact (integrable_indicator_iff (fullWSlab_measurable H)).mp hh
  have hg (u : FreeRow) (hu : u∈R) (P : ∀i,T i) :
      IntegrableOn (g u P) (szRectangle H) (volume.prod volume) ∧
        (∫p in fullWSlab H,f u P p ∂heightMeasure)=∫q in szRectangle H,g u P q ∂(volume.prod volume) := by
    have hh := fullW_factored_integral S hS hmax η u (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
      W Yp W0 W1 X Y Z (a+16*e) (17/50) H (hi u hu P)
    simpa only [g,f,ofReal_div,ofReal_ofNat] using hh
  have hgi (u : FreeRow) (hu : u∈R) :
      IntegrableOn (fun q=>∑P:(∀i,T i),g u P q) (szRectangle H) (volume.prod volume) :=
    integrable_finsetSum _ (fun P _=>(hg u hu P).1)
  have hF : (fun q : ℝ×ℝ=>sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)*
      integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I))=
      (fun q=>∑u∈R,∑P:(∀i,T i),g u P q) := by
    funext q
    simp only [integratedDyadValue,Finset.mul_sum,g]
  dsimp only
  rw [hF]
  refine ⟨integrable_finsetSum _ hgi,?_⟩
  rw [integral_finsetSum R hgi,Finset.mul_sum]
  unfold finiteCentralFullWRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>(hg u hu P).1),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [←(hg u hu P).2]
  have hh := fullWWeightedRow_integral S hS hmax (fun j=>(P j).val)
    (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H
  rw [show (∫p,fullWWeightedRow S hS hmax (fun j=>(P j).val)
      (fun j=>hT j _ (P j).property) η u W Yp W0 W1 X Y Z a e H p ∂heightMeasure)=
      ∫p in fullWSlab H,f u P p ∂heightMeasure by
        exact integral_indicator (fullWSlab_measurable H)] at hh
  exact hh.symm

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.FullWReconstruction -/

/- BEGIN ORIGINAL Cycle25.Numerator.SourceSZBound; sha256 7122a666247c4f5f042a9abffbb7b1ab519df9a3e976e6cb3c02566980aa5853 -/
section
                                                     

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

end
/- END ORIGINAL Cycle25.Numerator.SourceSZBound -/
