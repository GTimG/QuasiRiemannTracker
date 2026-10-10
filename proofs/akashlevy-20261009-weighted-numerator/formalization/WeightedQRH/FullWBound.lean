import WeightedQRH.SourceSZBound

/-! Convert the actual w-integrated numerator estimate into a full physical cell bound. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace WeightedQRH.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

theorem finiteFullW_uniform_norm_bound (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι],
      ∀(e a B H : ℝ) (i : ℕ),0<e→e<1/1000→(51/100:ℝ)≤a→a≤1→2<B→H≤(3*i+2:ℕ)*B→
      ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
      FirstTail (4*e) S→∀(η : Character) (R : Finset FreeRow),(∀u∈R,u.val≠1)→
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)→
      ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ),
      0<a1→Function.support W1⊆Icc a1 b1→∀X Y Z A : ℝ,0<X→0<Y→0<Z→0≤A→
      (∀q∈szRectangle H,‖integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖≤A)→
      ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A := by
  obtain ⟨C,hC,hprofile⟩ := sourceSZ_uniform_integral_bound W0 a0 b0 ha0 hW0
    (51/100) 2 (17/50) (17/50) (by norm_num) 0
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨(‖c‖+1)*C,by positivity,?_⟩
  intro K ι _ e a B H i he he' ha haTop hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp W1
    a1 b1 ha1 hW1 X Y Z A hX hY hZ hA hbound
  let G (q : ℝ×ℝ) := integratedDyadValue S hS hmax η R T hT W Yp W1 Y
    (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hh := finiteFullW_reconstruction e a B H i he he' ha haTop hB hH S hS hmax hfirst
    η R hR T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh
  have hp := hprofile (a+16*e) ⟨by linarith,by linarith⟩ (17/50) ⟨le_rfl,le_rfl⟩
    X Z hX hZ H A hA G
  simp only [ofReal_div,ofReal_ofNat,pow_zero,mul_one] at hp
  have hb := hp hh.1 hbound
  rw [hh.2,norm_mul]
  change ‖c‖*‖∫q in szRectangle H,sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I)
      ((17/50:ℂ)+q.2*I)*G q ∂(volume.prod volume)‖≤_
  calc
    _ ≤ ‖c‖*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ (‖c‖+1)*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = _ := by ring

end WeightedQRH.FullWContour
end
