import Cycle25.Numerator.Imported.NumeratorLabelPacket
import Cycle25.Numerator.Imported.NumeratorReconstruction

/-! The literal error-label numerator has precisely the global coefficient packet
whose damped mass is used in the weighted fourth moment. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem label_packet_central_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2) :
    Summable (fun e : LabelPacketIndex S u T=>‖labelPacketCoefficient S hS η u T hT weight x z e‖*
      (labelPacketScale S u T e:ℝ)^(-(1/2:ℝ))) := by
  apply (summable_sigma_of_nonneg (fun e=>mul_nonneg (norm_nonneg _) (by positivity))).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro P
  have hs := (error_packet_central_summable S hS firsteps hfirst η u (labelPrimes T P)
    (labelSupported S hS T hT P) x z hx hz hmargin).mul_left ‖∏i,weight i (P i)‖
  simpa only [labelPacketCoefficient,labelPacketScale,norm_mul,mul_assoc] using hs

theorem partialErrorTuple_label_series {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2) (t : ℝ) :
    (∑P:(∀i:J,T i.val),partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*I) z)=
    ∑'e : LabelPacketIndex S u (fun i:J=>T i.val),
      labelPacketCoefficient S hS η u (fun i:J=>T i.val) (fun i=>hT i.val)
        (fun i P=>physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
      (labelPacketScale S u (fun i:J=>T i.val) e:ℂ)^(-((1/2:ℂ)+t*I)) := by
  have hs := label_packet_central_summable S hS firsteps hfirst η u
    (fun i:J=>T i.val) (fun i=>hT i.val)
    (fun i P=>physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z hx hz hmargin
  have hc : Summable (fun e : LabelPacketIndex S u (fun i:J=>T i.val)=>
      labelPacketCoefficient S hS η u (fun i:J=>T i.val) (fun i=>hT i.val)
        (fun i P=>physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
      (labelPacketScale S u (fun i:J=>T i.val) e:ℂ)^(-((1/2:ℂ)+t*I))) := by
    apply Summable.of_norm
    convert hs using 1
    funext e
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u (fun i:J=>T i.val) e))]
    norm_num
  unfold LabelPacketIndex at hc ⊢
  rw [hc.tsum_sigma,tsum_fintype]
  apply Finset.sum_congr rfl
  intro P hP
  rw [partialErrorTuple_packet S hS η u J T hT P (hdis P) (partial_image_supported S hS J T hT P)]
  have hηP : ∀Q∈labelPrimes (fun i:J=>T i.val) P,IsCoprime Q.val η.modulus := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hη i.val _ (P i).property
  have hQP : ∀Q∈labelPrimes (fun i:J=>T i.val) P,(4:ℝ)≤Q.val.absNorm := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hQ i.val _ (P i).property
  have he := error_packet_expansion S hS firsteps hfirst η u (labelPrimes (fun i:J=>T i.val) P)
    (labelSupported S hS (fun i:J=>T i.val) (fun i:J=>hT i.val) P) hηP x ((1/2:ℂ)+t*I) z hQP hx hz
    (by simp;norm_num) (by simpa using hmargin)
  simp only [labelPrimes] at he
  apply Eq.trans (congrArg (fun v : ℂ=>(∏i:J,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*v) he)
  simp only [labelPacketCoefficient,labelPacketScale,labelPrimes]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro e
  ring

theorem errorLabelNumerator_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0<Y) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y=
      (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex S u (fun i:J=>T i.val),
        labelPacketCoefficient S hS η u (fun i:J=>T i.val) (fun i=>hT i.val)
          (fun i P=>physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z e*
        (labelPacketScale S u (fun i:J=>T i.val) e:ℂ)^(-(1/2:ℂ))*
        HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
          (Y/(labelPacketScale S u (fun i:J=>T i.val) e:ℝ)) 0 0 := by
  let f (P : ∀i:J,T i.val) (t : ℝ) :=
    (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W1 ((1/2:ℂ)+t*I)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*I)*
      partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*I) z
  have hfi (P : ∀i:J,T i.val) : Integrable (f P) := by
    apply partialErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J T hT P (hdis P)
      (partial_image_supported S hS J T hT P) _ _ W Yp x z hx hz hmargin W1 a b ha hsupp hW Y hY
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hη i.val _ (P i).property
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hQ i.val _ (P i).property
  have he : errorLabelNumerator S hS η u J T hT W Yp x z W1 Y=
      (1/(2*Real.pi):ℂ)*(∫t : ℝ,∑P:(∀i:J,T i.val),f P t) := by
    rw [integral_finsetSum Finset.univ (fun P _=>hfi P),Finset.mul_sum]
    unfold errorLabelNumerator
    apply Finset.sum_congr rfl
    intro P hP
    exact (partialErrorTuple_mellin S hS η u J T hT P (hdis P)
      (partial_image_supported S hS J T hT P) W Yp x z W1 Y).symm
  rw [he]
  simp only [f,←Finset.mul_sum]
  simp_rw [partialErrorTuple_label_series S hS firsteps hfirst η u J T hT hdis hη hQ W Yp x z hx hz hmargin]
  exact MellinReconstruction.weighted_numerator_mellin (rowCharacter S hS.prime u) hrow
    W1 a b ha hsupp hW Y hY _ _
    (fun e=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u (fun i:J=>T i.val) e))
    (label_packet_central_summable S hS firsteps hfirst η u (fun i:J=>T i.val) (fun i=>hT i.val)
      (fun i P=>physicalSlotWeight P.val (W i.val) (Yp i.val) z) x z hx hz hmargin)

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
