import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary

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
