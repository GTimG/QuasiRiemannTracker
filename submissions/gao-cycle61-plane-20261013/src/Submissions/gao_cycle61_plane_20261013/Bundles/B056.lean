/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B053
import Submissions.gao_cycle61_plane_20261013.Bundles.B055

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelReconstruction; sha256 2ff4d0865f5264bf0f516667cb4967c41034e435a8474f874cdbf62ce852d0aa -/
section
                                                      
                                                         

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

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorLabelReconstruction -/

/- BEGIN ORIGINAL Cycle25.Numerator.BoxReconstruction; sha256 0c088bc1f8e5d45d7e6c984dfce0966895338b81ecaec1d96a51ec420529a4d3 -/
section
                                                              
                                   

/-! Exact finite normalized dilation decomposition of the reconstructed numerator. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def normalizedBox {κ : Type*} (U xi : ℝ) (n j : ℕ) (rho M : ℝ)
    (t : κ → ℝ) (f : κ → ℂ) : ℂ :=
  ((U^(rho*((j : ℝ)*xi))/M : ℝ) : ℂ) * ∑' e, boxSeriesTerm U xi n j t f e

theorem normalized_box_reconstruction {κ : Type*} (U xi : ℝ) (n : ℕ)
    (rho M : ℝ) (hU : 0 < U) (hM : M ≠ 0)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1),
      ((M*U^(-rho*((j : ℝ)*xi)) : ℝ) : ℂ) * normalizedBox U xi n j rho M t f := by
  rw [tsum_box_decomposition U xi n t f hf]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedBox
  rw [←mul_assoc,←Complex.ofReal_mul]
  have he : M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) = 1 := by
    rw [show M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) =
      (M/M)*(U^(-rho*((j : ℝ)*xi))*U^(rho*((j : ℝ)*xi))) by ring,
      div_self hM,one_mul,←Real.rpow_add hU]
    simp
  rw [he,Complex.ofReal_one,one_mul]

/-- Every term outside the exact source cutoff is zero, including before any
coefficient mass bound or choice of a row-dependent dilation box. -/
theorem actual_label_term_zero_of_cutoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ) (W : ℝ→ℂ) (a b Y : ℝ)
    (hY : 0 < Y) (hsupp : Function.support W ⊆ Set.Icc a b)
    (e : LabelPacketIndex S u T) (hcut : b*Y < (labelPacketScale S u T e : ℝ)) :
    labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0 = 0 := by
  have hp := MellinReconstruction.polynomial_zero_of_scale_cutoff
    (rowCharacter S hS.prime u) W a b Y
    (labelPacketScale S u T e : ℝ) hsupp hY
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e)) hcut
  rw [hp,mul_zero]


/-- A real packet box inherits the actual polynomial choice moment. The cutoff
condition is used only to identify the finite active scales. -/
theorem normalized_dilation_box_fourth {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U xi : ℝ) (n j : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hrho : 0 ≤ rho)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (L i * N i e) ≤ U^((n : ℝ)*xi))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (L i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖normalizedBox U xi n j rho M (fun e=>max 1 (L i*N i e))
      (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)‖^4 * ‖Q i‖^2) ≤ E := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  let active (i : ι) (e : α i) := valid i e ∧ dilationBox U xi n (max 1 (L i*N i e)) = j
  have hlo (i : ι) (e : α i) (he : active i e) : U^((j : ℝ)*xi) ≤ max 1 (L i*N i e) := by
    have hh := (dilationBox_spec U xi hU hxi n (max 1 (L i*N i e))
      (le_max_left _ _) (hupper i e he.1)).1
    rwa [he.2] at hh
  have hh := packet_box_fourth base A S N hN L rho U ((j : ℝ)*xi) active Q M E hM hU0 hrho
    hlo hs hm hselection
  have ht (i : ι) (e : α i) :
      boxSeriesTerm U xi n j (fun e=>max 1 (L i*N i e))
        (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) e =
      A i e*(N i e:ℂ)^(-(1/2:ℂ))*(if active i e then S i e else 0) := by
    by_cases hv : valid i e
    · by_cases hb : dilationBox U xi n (max 1 (L i*N i e)) = j
      · simp [boxSeriesTerm,active,hv,hb]
      · simp [boxSeriesTerm,active,hv,hb]
    · simp [boxSeriesTerm,active,hv,hzero i e hv]
  simpa only [normalizedBox,ht] using hh


theorem actual_label_series_norm_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+firsteps≤x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hsupp : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0<Y) :
    Summable (fun e : LabelPacketIndex S u T =>
      ‖labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0‖) :=
  MellinReconstruction.reconstructed_series_norm_summable (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY _ _
    (fun e=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e))
    (label_packet_central_summable S hS firsteps hfirst η u T hT weight x z hx hz hmargin)

theorem errorLabelNumerator_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀ i:J,T i.val)) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y = 0 := by
  letI : IsEmpty (∀ i:J,T i.val) := not_nonempty_iff.mp hempty
  simp only [errorLabelNumerator,Finset.univ_eq_empty,Finset.sum_empty]

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.BoxReconstruction -/

/- BEGIN ORIGINAL Cycle25.Numerator.PacketBinBound; sha256 854dfc532a596a71214981a9b8093738b6a838240aafb1f0a0e68c8549e3b2f4 -/
section
                                          

/-! The complete coefficient-packet and dilation-bin estimate. All infinite
coefficient sums and rowwise choice moments have been eliminated here. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (kap U xi : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L z delta loss epsilon Ccount Cmoment M : ℝ)
    (hkap : 7/10 ≤ kap) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i * N i e) ≤ U^((n : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)))
    (hmass : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/4)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*selectedCapacity kap z ((j : ℝ)*xi+xi)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/4 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/4) M
    (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/4) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/4) M hU0 hM.ne'
      (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 3
    ring
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/4) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins Finset.univ n B Q P _ kap U R q L z xi delta loss epsilon
    Ccount Cmoment M hkap hU hc hm hM.le hq hqdelta hxi (by simpa using hcard)
    (fun i hi=>hsplit i) (fun j hj i hi=>hselected j hj i) (fun i hi=>hfull i) henergy

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.PacketBinBound -/

/- BEGIN ORIGINAL Cycle25.Numerator.AmplitudeLoss; sha256 f38dbe7847252215d83171a700e752416f150ead80e00bf68545ef414dbde4fe -/
section
                                       

/-! Upper amplitude-bin slack is restored after the packet estimate, without
changing the diluted lower-bin mean used by either the count or the capacity. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

theorem upper_bin_normalized (P : ℂ) (U a loss : ℝ) (hU : 0 < U)
    (hP : ‖P‖ ≤ U^(a+loss)) :
    ‖P / ((U^loss : ℝ) : ℂ)‖ ≤ U^a := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hU _)).mpr
  simpa only [Real.rpow_add hU] using hP

theorem restore_upper_bin_loss {ι : Type*} (s : Finset ι) (S P : ι→ℂ)
    (U loss E C : ℝ) (hU : 0 < U)
    (hb : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) ≤ C*U^E) :
    (∑ i ∈ s, ‖S i*P i‖) ≤ C*U^(E+loss) := by
  have he : (∑ i ∈ s, ‖S i * (P i / ((U^loss : ℝ) : ℂ))‖) =
      (∑ i ∈ s, ‖S i*P i‖) / U^loss := by
    simp_rw [←mul_div_assoc,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
    exact (Finset.sum_div _ _ _).symm
  rw [he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU loss)).mp hb
  simpa only [mul_assoc,←Real.rpow_add hU] using hh

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/

end
/- END ORIGINAL Cycle25.Numerator.AmplitudeLoss -/
