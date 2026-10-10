import Cycle25.Numerator.Imported.FullWContour

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
