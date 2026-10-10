import WeightedQRH.NumeratorErrorIntegrable
import WeightedQRH.FullWReconstruction

/-! Exact reconstruction of the actual prime tuples, with finite interchanges
justified before taking any absolute value or splitting rows into amplitudes. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (P : Fin K→HeckeInverseAmplification.PrimeIdeal)
    (hP : ∀i,(P i).val∉S) : ∀Q∈J.image P,Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i) (hP i)

theorem partial_image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:J,T i.val) :
    ∀Q∈Finset.univ.image (fun i:J=>(P i).val),Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)

theorem calibrated_tuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hQ : ∀i,(4:ℝ)≤(P i).val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      calibratedTupleValue S hS hmax η u P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hη' (J : Finset (Fin K)) : ∀Q∈J.image P,IsCoprime Q.val η.modulus := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hη i
  have hQ' (J : Finset (Fin K)) : ∀Q∈J.image P,(4:ℝ)≤Q.val.absNorm := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hQ i
  have hi (J : Finset (Fin K)) :=
    (weightedErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J P hP hPS
      (image_supported S hS J P hPS) (hη' J) (hQ' J) W Yp x z hx hz hmargin
      W1 a b ha hsupp hW Y hY).mul_const (physicalMainTuple u J P W Yp z)
  have hsum := (integrable_finsetSum Finset.univ.powerset (fun J _=>hi J)).const_mul
    (numeratorFreeRowScalar S hS hmax η u x z)
  apply hsum.congr
  filter_upwards with t
  rw [calibratedTupleValue_error_subsets firsteps S hS hfirst hmax P hP hPS η u W Yp x
    ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

/-- A literal finite error-label numerator; its coefficients are those reconstructed
from the original row integral. -/
def errorLabelNumerator {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (J : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑P:(∀i:J,T i.val),(∏i:J,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
    errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:J=>(P i).val))
      (partial_image_supported S hS J T hT P) x z W1 Y

/-- The normalized full-w integral of the actual calibrated prime tuples equals
its error-label numerators times the remaining, unaltered prime sums. -/
theorem normalized_prime_tuple_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0<Y) :
    (1/(2*Real.pi):ℂ)*(∑P:(∀i,T i),FullWContour.rowNumeratorIntegral S hS hmax η u
      (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp W1 Y x z)=
    numeratorFreeRowScalar S hS hmax η u x z*
      ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val))) := by
  let kern (t : ℝ) := (Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)
  let f (J : Finset (Fin K)) (P : ∀i:J,T i.val) (t : ℝ) :=
    kern t*HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z
  let main (J : Finset (Fin K)) :=
    ∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
      (-star (idealRowHom u.val P.val.val))
  have hi (P : ∀i,T i) := calibrated_tuple_kernel_integrable S hS hmax firsteps hfirst η u hrow
    (fun i=>(P i).val) (hdisAll P) (fun i=>hT i _ (P i).property)
    (fun i=>hη i _ (P i).property) (fun i=>hQ i _ (P i).property)
    W Yp x z hx hz hmargin W1 a b ha hsupp (W1.smooth ⊤) Y hY
  have hfi (J : Finset (Fin K)) (P : ∀i:J,T i.val) : Integrable (f J P) := by
    apply partialErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J T hT P (hdis J P)
      (partial_image_supported S hS J T hT P) _ _ W Yp x z hx hz hmargin
      W1 a b ha hsupp (W1.smooth ⊤) Y hY
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hη i.val _ (P i).property
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hQ i.val _ (P i).property
  have hsum (J : Finset (Fin K)) : Integrable (fun t=>(∑P:(∀i:J,T i.val),f J P t)*main J) :=
    (integrable_finsetSum Finset.univ (fun P _=>hfi J P)).mul_const (main J)
  have he (t : ℝ) :
      (∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
        (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=
      numeratorFreeRowScalar S hS hmax η u x z*
        ∑J∈Finset.univ.powerset,(∑P:(∀i:J,T i.val),f J P t)*main J := by
    rw [←Finset.mul_sum,calibrated_prime_error_slots_separate firsteps S hS hfirst hmax η u T hT
      hdisAll W Yp x ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
    simp only [Finset.mul_sum,f,main]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    ring
  unfold FullWContour.rowNumeratorIntegral
  rw [←integral_finsetSum Finset.univ (fun P _=>hi P)]
  change (1/(2*Real.pi):ℂ)*(∫t : ℝ,∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=_
  simp_rw [he]
  rw [integral_const_mul,integral_finsetSum Finset.univ.powerset (fun J _=>hsum J)]
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [integral_mul_const,integral_finsetSum Finset.univ (fun P _=>hfi J P)]
  change (1/(2*Real.pi):ℂ)*((∑P:(∀i:J,T i.val),∫t : ℝ,f J P t)*main J)=_
  rw [←mul_assoc,Finset.mul_sum]
  change (∑P:(∀i:J,T i.val),(1/(2*Real.pi):ℂ)*(∫t : ℝ,f J P t))*main J=_
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  exact partialErrorTuple_mellin S hS η u J T hT P (hdis J P)
    (partial_image_supported S hS J T hT P) W Yp x z W1 Y


def reconstructedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑u∈R,frequencyWeight z ⟨u.val,u.property.1⟩ * numeratorFreeRowScalar S hS hmax η u x z *
    ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
      (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
        (-star (idealRowHom u.val P.val.val)))

theorem integratedDyadValue_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (R : Finset FreeRow)
    (hrow : ∀u∈R,(rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0<Y) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      (2*Real.pi:ℂ)*reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
  have he : (1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
    unfold FullWContour.integratedDyadValue reconstructedDyadValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [FullWContour.integratedRowValue,←Finset.mul_sum]
    rw [mul_left_comm,normalized_prime_tuple_reconstruction S hS hmax firsteps hfirst η u
      (hrow u hu) T hT hdis hdisAll hη hQ W Yp x z hx hz hmargin W1 a b ha hsupp Y hY]
    ring
  have hc : (2*Real.pi:ℂ)*(1/(2*Real.pi):ℂ)=1 := by
    apply mul_one_div_cancel
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    _ = (2*Real.pi:ℂ)*((1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue
        S hS hmax η R T hT W Yp W1 Y x z) := by rw [←mul_assoc,hc,one_mul]
    _ = _ := by rw [he]

end WeightedQRH.Numerator
end
