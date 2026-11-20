/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One fixed height polynomial for all three genuine native count prefactors. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSlicePrefactor
import Candidate.C092.transport.MixedOutsideActualFourthEnvelope
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorRawFiber
open QRH.Record1252270103Return
open QRH.Cycle092.PacketJoin QRH.Cycle092.MixedOffsetCount QRH.Cycle092.MixedMiddleReturn
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma dyadic_length_one (U : ℝ) : 1 ≤ (dyadicLength U:ℝ) := by
  have h : 1 ≤ dyadicLength U := by unfold dyadicLength;omega
  exact_mod_cast h

lemma native_height_nonneg {Z : ℝ} (hZ : 0 ≤ Z) (d τ : ℝ) (i : ℕ) :
    0 ≤ nativeHeight Z d τ i := by unfold nativeHeight;positivity

lemma height_coefficient_le_envelope {A C : ℝ} {j J : ℕ} {Z d τ : ℝ} {i : ℕ}
    (hH : 0 ≤ nativeHeight Z d τ i) (hA : 0 ≤ A) (hAC : A ≤ C) (hj : j ≤ J) :
    A*(1+nativeHeight Z d τ i)^j ≤ outsideCountEnvelope C J Z d τ i := by
  unfold outsideCountEnvelope
  exact mul_le_mul (hAC.trans (le_max_right _ _))
    (pow_le_pow_right₀ (by linarith) hj) (by positivity) (by positivity)

/-- All source constants and degrees are fixed before Z,d,tau,i,U or the
live phase bins. The same envelope contains the native outside and all-long
counts as well as the complete middle count, including its phase alphabet. -/
theorem native_count_common_envelope (labels : ℕ) (binCap : ℝ) (hbinCap : 0 ≤ binCap)
    (K : CountConstants) (Co Ci Ki : ℝ) (Jo Ji : ℕ)
    (hCo : 0 < Co) (hCi : 0 < Ci) (hKi : 0 ≤ Ki) :
    ∃ Cc : ℝ,0 < Cc ∧ ∃ Jc : ℕ,∀ (Z d τ U : ℝ) (i bins : ℕ),
      0 ≤ nativeHeight Z d τ i → (bins:ℝ) ≤ binCap →
    let H := nativeHeight Z d τ i;
    let E := outsideCountEnvelope Cc Jc Z d τ i*(dyadicLength U:ℝ)^2;
      max 1 (countCoefficient labels bins U H K.K₀ K.Ki K.C₀ K.Cr K.Ci K.J₀ K.Jr K.Ji) ≤ E ∧
      max 1 (192*(1+H)*(Co*(1+H)^Jo)) ≤ E ∧
      max 1 (12*(1+H)*((Ci*(1+H)^Ji)*Ki)) ≤ E := by
  let Cm := paidCountConstant labels binCap K
  have hCm : 1 ≤ Cm := by
    dsimp [Cm,paidCountConstant]
    have h0 : 0 ≤ (labels:ℝ)*binCap*192*K.C₀*max 1 K.K₀ := by positivity [K.C₀_pos.le]
    have hr : 0 ≤ 192*K.Cr := by positivity [K.Cr_pos.le]
    have hi : 0 ≤ 12*K.Ci*K.Ki := by positivity [K.Ci_pos.le,K.Ki_nonneg]
    linarith only [h0,hr,hi]
  let Cc := 2*Cm+192*Co+12*Ci*Ki+2
  let Jc := paidCountDegree K+Jo+Ji+2
  have hCc : 0 < Cc := by dsimp [Cc]; nlinarith only [hCm,hCo,hCi,hKi,mul_nonneg hCi.le hKi]
  refine ⟨Cc,hCc,Jc,?_⟩
  intro Z d τ U i bins hH hb
  have hdyad := dyadic_length_one U
  dsimp only
  let L := (dyadicLength U:ℝ)^2
  have hL : 1 ≤ L := by dsimp [L]; nlinarith only [hdyad]
  have hLE : 1 ≤ outsideCountEnvelope Cc Jc Z d τ i*L :=
    one_le_mul_of_one_le_of_one_le
      (by unfold outsideCountEnvelope;exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (by linarith))) hL
  have hm0 : 0 ≤ Cm := zero_le_one.trans hCm
  have hcM : 2*Cm ≤ Cc := by dsimp [Cc];nlinarith only [hCo,mul_nonneg hCi.le hKi]
  have hcO : 192*Co ≤ Cc := by dsimp [Cc];nlinarith only [hCm,mul_nonneg hCi.le hKi]
  have hcI : 12*Ci*Ki ≤ Cc := by dsimp [Cc];nlinarith only [hCm,hCo]
  have hm := height_coefficient_le_envelope hH (by positivity : 0 ≤ 2*Cm) hcM
    (show paidCountDegree K ≤ Jc by dsimp [Jc];omega)
  have ho := height_coefficient_le_envelope hH (by positivity : 0 ≤ 192*Co) hcO
    (show Jo+1 ≤ Jc by dsimp [Jc];omega)
  have hi := height_coefficient_le_envelope hH (by positivity : 0 ≤ 12*Ci*Ki) hcI
    (show Ji+1 ≤ Jc by dsimp [Jc];omega)
  refine ⟨?_,max_le hLE ?_,max_le hLE ?_⟩
  · have hcount := paid_count_coefficient labels bins binCap K (U:=U) hH hb
    calc
      _ ≤ Cm*(1+L)*(1+nativeHeight Z d τ i)^(paidCountDegree K) := hcount
      _ ≤ (2*Cm*(1+nativeHeight Z d τ i)^(paidCountDegree K))*L := by
        have h := mul_le_mul_of_nonneg_left (show 1+L ≤ 2*L by linarith only [hL])
          (mul_nonneg hm0 (show 0 ≤ (1+nativeHeight Z d τ i)^(paidCountDegree K) by positivity))
        nlinarith only [h]
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (by dsimp [L]; positivity)
  · have h := (mul_le_mul_of_nonneg_right ho (show 0 ≤ L by dsimp [L]; positivity))
    have h0 := le_mul_of_one_le_right (show 0 ≤ 192*Co*(1+nativeHeight Z d τ i)^(Jo+1) by positivity) hL
    convert h0.trans h using 1 <;> rw [pow_succ] <;> ring
  · have h := (mul_le_mul_of_nonneg_right hi (show 0 ≤ L by dsimp [L]; positivity))
    have h0 := le_mul_of_one_le_right (show 0 ≤ 12*Ci*Ki*(1+nativeHeight Z d τ i)^(Ji+1) by positivity) hL
    convert h0.trans h using 1 <;> rw [pow_succ] <;> ring

#print axioms height_coefficient_le_envelope
#print axioms native_count_common_envelope
end
end QRH.Cycle092.MixedUpperFinal
