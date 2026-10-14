/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Mathlib
import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.FullWContour; sha256 9080b01f0bb1128fc4778a011c92baeca21ee644c2dafa4ad645b41d5133541f -/
section
                                                             
                                                        
                                                                 

/-! Full-w contour transport on the retained s,z rectangle. The extension of
BufferedGrowth/BufferedIntegral below leaves the actual row kernel unchanged,
and allows every w line to the right of the original buffered line.
-/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem calibrated_buffered_strip_growth
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → 1-a-6*e≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring


lemma rowAmplitude_buffered_strip_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (σ υ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) (hυ : 1-a-6*e≤υ) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_buffered_strip_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continued_kernel_strip_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ υ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) (hυ : 1-a-6*e≤υ) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ υ r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitude_buffered_strip_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ υ r hσ hσ2 hr hυ
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)


/-- The complete w integral may be moved right on a detector-controlled s line. -/
theorem buffered_w_integral_eq {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ)
    (hσ : a+16*e≤x.re) (hσ2 : x.re≤2) (hxi : |x.im|≤H)
    (hz : (17/50:ℝ)≤z.re) (l r : ℝ) (hl : 1-a-6*e≤l) (hlr : l≤r) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := calibrated_buffered_strip_growth e a B H i he he' ha haTop hB hH
    S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu ψ hbin
  have hf : FirstTail ((8*e)/2) S := by convert hfirst using 1 <;> ring
  apply nonprincipal_w_integral_eq_of_polynomial (8*e) (by positivity) S hS hf hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY x z l r (9*C) 2 (by positivity) hlr
    (by linarith) (by linarith) hz (by linarith)
  intro v hv t
  have hb := hbound x ((v:ℂ)+t*I) z hσ hσ2 hxi (by simpa using hl.trans hv.1) hz
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have ht : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  nlinarith

def szRectangle (T : ℝ) : Set (ℝ×ℝ) := {q | |q.1|≤T ∧ |q.2|≤T}
def fullWSlab (T : ℝ) : Set HeightSpace := szRectangle T ×ˢ Set.univ

lemma szRectangle_measurable (T : ℝ) : MeasurableSet (szRectangle T) := by
  unfold szRectangle
  measurability
lemma fullWSlab_measurable (T : ℝ) : MeasurableSet (fullWSlab T) :=
  (szRectangle_measurable T).prod MeasurableSet.univ

/-- Fubini is applied with the whole w axis, never a truncated w interval. -/
theorem fullWSlab_fubini (T : ℝ) (f : HeightSpace→ℂ)
    (hf : IntegrableOn f (fullWSlab T) heightMeasure) :
    (∫p in fullWSlab T,f p ∂heightMeasure)=
      ∫q in szRectangle T,(∫w : ℝ,f (q,w)) ∂(volume.prod volume) := by
  simpa only [fullWSlab, Measure.restrict_univ] using setIntegral_prod f hf

def centralFullWIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H υ : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3 * ∫p in fullWSlab H,
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) υ (17/50) p ∂heightMeasure

/-- Exact equality of the full-w slab integrals, prior to amplitude partition. -/
theorem centralFullWIntegral_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (l r : ℝ) (hl : 1-a-6*e≤l) (hlr : l≤r) :
    centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H l =
      centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H r := by
  have hi (v : ℝ) (hv : 1-a-6*e≤v) :
      IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) v (17/50))
        (fullWSlab H) heightMeasure :=
    (continued_kernel_strip_integrable e a B H i he he' ha haTop hB hH S hS hmax hfirst P hPS η u hu ψ hbin
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ (a+16*e) v (17/50)
      le_rfl (by linarith) le_rfl hv).mono_set (fun _ ht=>ht.1.1)
  unfold centralFullWIntegral
  rw [fullWSlab_fubini _ _ (hi l hl), fullWSlab_fubini _ _ (hi r (hl.trans hlr))]
  congr 1
  apply setIntegral_congr_fun (szRectangle_measurable H)
  intro q hq
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using
    buffered_w_integral_eq e a B H i he he' ha haTop hB hH S hS hmax hfirst P hPS η u hu ψ hbin
    W0 W1 a1 b1 ha1 hW1 X Y Z hY (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
    (by simp) (by simp;linarith) (by simpa using hq.1) (by simp) l r hl hlr

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.FullWContour -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.FullWTransport; sha256 34fbb2de36aa8d35a0a7e02a18598d79c97cd37a506c7145a751084e3fe0c400 -/
section
                                              

/-! Transport from the original physical row integral to the complete numerator
integral over w, retaining a bounded rectangle in s and z only. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem centralFullWIntegral_cube_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_w_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E := fullWSlab H
  let T : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hsub : T⊆E := fun _ ht=>⟨⟨ht.1.1,ht.2⟩,Set.mem_univ _⟩
  have hi0 : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure :=
    continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
      S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hi : IntegrableOn f E heightMeasure := hi0.mono_set (fun _ ht=>ht.1.1)
  have heq : centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)-
      centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H =
      n*(∫t in E\T,f t ∂heightMeasure) := by
    rw [setIntegral_sdiff hT hi hsub]
    dsimp [centralFullWIntegral,centralCubeIntegral,n,E,T,f]
    ring
  have htail : (∫t in E\T,‖f t‖ ∂heightMeasure)≤
      C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply le_trans _ (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
      (a+16*e) ⟨le_rfl,by linarith⟩)
    apply setIntegral_mono_set ((show IntegrableOn (fun t=>‖f t‖) {t : HeightSpace | |t.1.1|≤H} heightMeasure from hi0.norm).mono_set (fun _ ht=>ht.1))
      (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    apply Filter.Eventually.of_forall
    intro t ht
    refine ⟨ht.1.1.1,?_⟩
    by_contra hh
    exact ht.2 ⟨⟨ht.1.1.1,le_of_not_gt hh⟩,ht.1.1.2⟩
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in E\T,‖f t‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

/-- The physical row equals the full-w central expression up to a rapidly
vanishing tail. This theorem refers to the actual upstream rowIntegral. -/
theorem uniform_original_row_fullW_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1/2)‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := centralFullWIntegral_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hZp : 0<Z := by linarith
  have heq := centralFullWIntegral_transport e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZp (1-a-6*e) (1/2) le_rfl (by linarith)
  rw [←heq]
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY hZp a B H i ha haTop hB hH0 hH hbin
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    rw [norm_sub_rev]
    apply h1'.trans
    gcongr
    · exact pow_nonneg (height_pos _).le _
    · exact mul_nonneg hC1 (contourArithmeticCost_nonneg η u P)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.FullWTransport -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.Parameters; sha256 1dba1bb378b2f93b88e833d45fea753ca42ee98ab09bceb93bde31520358d501 -/
section
              

/-!
Exact real parameters for the weighted physical numerator proof.
No analytic theorem or QRH conclusion is assumed in this module.
-/

namespace Cycle25.Weighted

noncomputable section

def theta : ℝ := 10499 / 12000
def ell : ℝ := 167 / 1000
def b : ℝ := 43 / 500
def lx : ℝ := 747 / 2000
def ly : ℝ := 919 / 2000
def h : ℝ := 1587 / 2000
def kappa : ℝ := 3 / 4
def endpointMargin : ℝ := 1 / 10000
def rowExtension : ℝ := 1 / 1000000
def publicBenchmark : ℝ := 874957019420098946128604623 / 10^27
def signal (s : ℝ) : ℝ := s - (4 + b) / 6

theorem theta_eq : theta = (11 : ℝ) / 12 - ell / 4 := by
  norm_num [theta, ell]

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7 : ℝ) / 8 := by norm_num [theta]
theorem theta_lt_public : theta < publicBenchmark := by
  norm_num [theta, publicBenchmark]
theorem theta_gt_half : (1 : ℝ) / 2 < theta := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]
theorem kappa_admissible : (1 + kappa) / 2 = (7 : ℝ) / 8 := by
  norm_num [kappa]
theorem endpointMargin_pos : 0 < endpointMargin := by norm_num [endpointMargin]
theorem rowExtension_pos : 0 < rowExtension := by norm_num [rowExtension]
theorem rowExtension_cost : 2 * rowExtension < endpointMargin / 2 := by
  norm_num [rowExtension, endpointMargin]

theorem length_sum : lx + ly = 1 - ell := by norm_num [lx, ly, ell]
theorem length_difference : ly - lx = b := by norm_num [lx, ly, b]
theorem row_endpoint : h = 1 - lx + ell := by norm_num [h, lx, ell]
theorem signal_low : signal theta = lx / 2 + b / 12 := by
  norm_num [signal, theta, lx, b]
theorem signal_slope (s t : ℝ) : signal s - signal t = s - t := by
  simp only [signal]; ring

theorem b_pos : 0 < b := by norm_num [b]
theorem ell_pos : 0 < ell := by norm_num [ell]
theorem ell_lt_one_fifth : ell < (1 : ℝ) / 5 := by norm_num [ell]
theorem x_rescaled_pos : 0 < lx - ell := by norm_num [lx, ell]
theorem y_rescaled_pos : 0 < ly - ell := by norm_num [ly, ell]
theorem row_rescaled_pos : 0 < 1 - 3 * ell := by norm_num [ell]
theorem gram_domination : 0 < ly - ell - (11 : ℝ) / 6 * b := by
  norm_num [ly, ell, b]
theorem h_pos : 0 < h := by norm_num [h]
theorem h_gt_half : (1 : ℝ) / 2 < h := by norm_num [h]
theorem h_lt_one : h < 1 := by norm_num [h]
theorem row_count_supply : (7 : ℝ) / 37 < ell / h := by norm_num [ell, h]
theorem row_extension_supply : h < 5 * ell := by norm_num [h, ell]
theorem numerator_short : h < 2 * ly := by norm_num [h, ly]
theorem ly_lt_half : ly < (1 : ℝ) / 2 := by norm_num [ly]
theorem numerator_supply : (2 * ly - (1 : ℝ) / 2) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell]
theorem extended_row_count_supply : (7 : ℝ) / 37 < ell / (h + rowExtension) := by
  norm_num [ell, h, rowExtension]
theorem extended_numerator_short : h + rowExtension < 2 * ly := by
  norm_num [h, rowExtension, ly]
theorem extended_h_lt_one : h + rowExtension < 1 := by norm_num [h, rowExtension]
theorem extended_row_supply : h + rowExtension < 5 * ell := by
  norm_num [h, rowExtension, ell]

theorem numerator_supply_all {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) :
    (2 * ly - d) / (6 * kappa) < ell := by
  norm_num [ly, kappa, ell] at *
  linarith

theorem numerator_range {d : ℝ} (hd : (1 : ℝ) / 2 ≤ d) (hdh : d ≤ h) :
    d / 2 < ly ∧ ly < d := by
  norm_num [h, ly] at *
  constructor <;> linarith

theorem low_rescaled_tuple {v : ℝ} (hv : 0 ≤ v) :
    -v + max 0 (5 * ell - 1 + v) / 8 ≤ 0 := by
  have hm : max 0 (5 * ell - 1 + v) ≤ 8 * v := by
    apply max_le
    · linarith
    · norm_num [ell]
      linarith
  linarith

theorem low_rescaled_identity (v : ℝ) :
    (1 - ell - 2 * v) + (ell - v) - 1 = -3 * v := by ring

theorem small_row_margin :
    h * ((17 : ℝ) / 50 - 1 / 6) - ly / 2 + 63 / 5000 < 0 := by
  norm_num [h, ly]
theorem principal_w_margin : 0 < ly / 20 := by norm_num [ly]
theorem principal_z_margin : 0 < h / 600 := by norm_num [h]
theorem euler_tail_capacity_gap : (1 : ℝ) / 4 - 1 / (12 * kappa) = 5 / 36 := by
  norm_num [kappa]

theorem principal_local_exponents :
    -(6 : ℝ) * (33 / 200) ≤ -theta ∧
    4 - 5 * theta - 6 * (33 / 200) ≤ -theta ∧
    1 - (19 : ℝ) / 20 - 6 * (33 / 200) ≤ -theta := by
  norm_num [theta]

theorem principal_euler_defects :
    4 - 6 * theta - 6 * ((33 : ℝ) / 200) < -1 ∧
    1 - theta - (19 : ℝ) / 20 - 6 * (33 / 200) < -1 := by
  norm_num [theta]

/-- The exact nonnegative dual identity for the unchanged low estimates. -/
theorem low_barrier_identity (M ℓ e : ℝ) :
    M / 12 - ℓ / 6 + e / 2 - 1 / 30 =
      (1 / 5 : ℝ) * (e - (1 + 3 * ℓ - 2 * M) / 4) +
      (1 / 60 : ℝ) * (e - (M + ℓ - 1)) + (17 / 60 : ℝ) * e := by ring

/-- A limitation of the stated sufficient low-exponent system, not of zeros. -/
theorem low_barrier {B M ℓ e : ℝ}
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * M) / 4 ≤ e)
    (henergy₂ : M + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + M / 12 - ℓ / 6 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  linarith

/-- The same scoped barrier before eliminating the Gram exponent g. -/
theorem physical_low_barrier {B xLen yLen ℓ g e : ℝ}
    (hg : (yLen - xLen) / 6 ≤ g)
    (he : 0 ≤ e)
    (henergy₁ : (1 + 3 * ℓ - 2 * (xLen + yLen)) / 4 ≤ e)
    (henergy₂ : xLen + yLen + ℓ - 1 ≤ e)
    (hlow : (5 : ℝ) / 6 + xLen / 6 - ℓ / 6 + g / 2 + e / 2 ≤ B) :
    (13 : ℝ) / 15 ≤ B := by
  apply low_barrier he henergy₁ henergy₂
  linarith

end
end Cycle25.Weighted

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.Parameters -/

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.FullWFiniteError; sha256 389dd51824b86240e2fc640fa840a924038d7e304727898a3b7aa675e8563585 -/
section
                                            
                                                
                                                            

/-! Summable physical row/tuple errors for the full-w transport at the new
lengths, with arbitrary power savings chosen after the height exponent. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma fullW_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^lx)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^ly)^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num [lx,ly] at *; nlinarith)

lemma fullW_prime_product_bound {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^ell := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma fullW_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*ell) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show h+ζ≤1 by norm_num [h] at *;linarith))
  have hp := fullW_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(ell*(3:ℕ))=Z^(6+3*ell) := by rw [←Real.rpow_add hZ0];congr 1;push_cast;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


lemma fullW_prime_tuple_count {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^ell := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


theorem original_row_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(h+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=ell →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^lx) (Z^ly) Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 (Z^lx) (Z^ly) Z a e H (1/2)‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*ell)+saving)/τ)
  have hN' : (8+3*ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^lx) (Z^ly) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := fullW_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := fullW_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*ell)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*ell)/height H^N) := by
      have hh : Z^(6+3*ell)*Z^(2:ℝ)=Z^(8+3*ell) := by rw [←Real.rpow_add hZ0];congr 1;push_cast;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


def finiteCentralFullWRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralFullWIntegral S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u) (1/2)

theorem finite_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(h+ζ)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^lx) (Z^ly) Z-
        finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^lx) (Z^ly) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_fullW_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(h+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show h+ζ≤1 by norm_num [h] at *;linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (fullW_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show ell≤1 by norm_num [ell])) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^lx) (Z^ly) Z u-
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^lx) (Z^ly) Z (a u) e (H u) (1/2)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralFullWRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^lx) (Z^ly) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^lx) (Z^ly) Z (a u) e (H u) (1/2)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]


end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.FullWFiniteError -/
