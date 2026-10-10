import Cycle25.Numerator.Imported.NumeratorIntegral
import Cycle25.Numerator.Imported.NumeratorPrimeSeparation

/-! Absolute integrability before the finite error subsets are interchanged. -/
noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem actual_error_packet_integrable (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (hη : ∀P∈T,IsCoprime P.val η.modulus)
    (x z : ℂ) (hQ : ∀P∈T,(4:ℝ)≤P.val.absNorm)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*I)*
      ((∏P:T,rawErrorSlot η u P.val (hT P.val P.property) x ((1/2:ℂ)+t*I) z)*
        continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x ((1/2:ℂ)+t*I) z)) := by
  have he (t : ℝ) := error_packet_expansion S hS firsteps hfirst η u T hT hη
    x ((1/2:ℂ)+t*I) z hQ hx hz (by simp;norm_num) (by simpa using hmargin)
  simp_rw [he]
  simp only [HeckeOrigin.continued,ite_eq_right hrow]
  have hh := MellinReconstruction.coefficient_series_integrable
    (errorPacketCoefficient S hS η u T hT x z) (fun e=>(errorPacketScale S u T e:ℝ))
    (fun e=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) (1/2)
    (error_packet_central_summable S hS firsteps hfirst η u T hT x z hx hz hmargin)
    _ (MellinReconstruction.reconstruction_kernel_integrable (rowCharacter S hS.prime u) hrow
      W a b ha hsupp hW Y hY)
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh

def finsetImageEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α→β) (hf : Function.Injective f) : s≃s.image f :=
  Equiv.ofBijective (fun i:s=>⟨f i.val,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩)
    ⟨by intro i j hij;apply Subtype.ext;exact hf (congrArg Subtype.val hij),by
      intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩⟩

theorem error_product_image {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val) (x w z : ℂ) :
    (∏i∈I,rawErrorSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z)=
      ∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z := by
  rw [←Finset.prod_coe_sort I]
  exact Fintype.prod_equiv (finsetImageEquiv I P hP) _ _ (fun _=>rfl)

theorem weightedErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I P hPS W Yp x w z=
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)*
      ((∏Q:I.image P,rawErrorSlot η u Q.val (hT Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (I.image P))
          (markedSourceExclusions S hS (I.image P)) η u x w z) := by
  unfold weightedErrorTuple
  rw [Finset.prod_mul_distrib,error_product_image S hS η u I P hP hPS hT]
  ring


theorem weightedErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (P : Fin K → HeckeInverseAmplification.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (hT : ∀Q∈I.image P,Supported Q.val)
    (hη : ∀Q∈I.image P,IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈I.image P,(4:ℝ)≤Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      weightedErrorTuple S hS η u I P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    (I.image P) hT hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i∈I,physicalSlotWeight (P i) (W i) (Yp i) z)
  apply hi.congr
  filter_upwards with t
  rw [weightedErrorTuple_packet S hS η u I P hP hPS hT]
  ring

theorem partialErrorTuple_packet {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x w z : ℂ) :
    partialErrorTuple S hS η u I T hT P W Yp x w z=
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x w z) := by
  have hp : (∏i:I,rawErrorSlot η u (P i).val
      (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z)=
      ∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x w z := by
    let e : I ≃ Finset.univ.image (fun i:I=>(P i).val) :=
      Equiv.ofBijective (fun i=>⟨(P i).val,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
        ⟨by intro i j hij;exact hP (congrArg Subtype.val hij),by
          intro Q
          obtain ⟨i,hi,hieq⟩ := Finset.mem_image.mp Q.property
          exact ⟨i,Subtype.ext hieq⟩⟩
    exact Fintype.prod_equiv e _ _ (fun _=>rfl)
  unfold partialErrorTuple
  rw [Finset.prod_mul_distrib,hp]
  ring

theorem partialErrorTuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (hη : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),IsCoprime Q.val η.modulus)
    (hQ : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),(4:ℝ)≤Q.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hi := (actual_error_packet_integrable S hS firsteps hfirst η u hrow
    _ hTS hη x z hQ hx hz hmargin W1 a b ha hsupp hW Y hY).const_mul
      (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)
  apply hi.congr
  filter_upwards with t
  rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  ring

theorem partialErrorTuple_mellin {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (I : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:I,T i.val)
    (hP : Function.Injective (fun i:I=>(P i).val))
    (hTS : ∀Q∈Finset.univ.image (fun i:I=>(P i).val),Supported Q.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u I T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z)=
    (∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:I=>(P i).val)) hTS x z W1 Y := by
  simp_rw [partialErrorTuple_packet S hS η u I T hT P hP hTS]
  unfold errorNumeratorIntegral
  rw [show (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z)))=
      (fun t : ℝ=>(∏i:I,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
        ((Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      ((∏Q:Finset.univ.image (fun i:I=>(P i).val),rawErrorSlot η u Q.val
          (hTS Q.val Q.property) x ((1/2:ℂ)+t*Complex.I) z)*
        continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
          (markedSourceExclusions S hS _) η u x ((1/2:ℂ)+t*Complex.I) z))) by funext t;ring]
  rw [integral_const_mul]
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
