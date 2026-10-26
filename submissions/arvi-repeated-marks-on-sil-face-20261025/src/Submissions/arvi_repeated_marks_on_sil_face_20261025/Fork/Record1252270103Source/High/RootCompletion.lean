/- Repeated marks: fork of Record1252270103Source.High.RootCompletion (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.RootCompletion
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Complete sixth-root sum with the new earlier-source gain. The exact weighted
sixth-frequency identity and ordinary ideal tail are reused without truncation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open LocalMoment HeckeFamily HeckeInverseAmplification ConcretePrimeRowBridge ProbeHighRowFamily ProbePhysical
open Record12518109GainRoot
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

theorem root_dependent_power_rm {ν S F U n capacity lam h : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4)
    (hB0 : 22/23≤capacity) (hB1 : capacity≤1) (hl : 1<lam) (hh0 : 0≤h) (hh1 : h≤1) (hU : 1<U) (hn : 1≤n) :
    U^(rho ν*(F-6*Real.logb U n)+ν*S-QRH.RepeatedMarks.Source.gainC ν capacity lam h S (F-6*Real.logb U n)) ≤
      U^(rho ν*F+ν*S-QRH.RepeatedMarks.Source.gainC ν capacity lam h S F)*n^(-6*(rho ν-cmax ν)) := by
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hlog : 0≤Real.logb U n := Real.logb_nonneg hU hn
  have hg := gain_row_loss_rm (S:=S) (q:=F-6*Real.logb U n) (F:=F) hν0 hν1 hB0 hB1 hl hh0 hh1 (by linarith)
  have hp : n^(-6*(rho ν-cmax ν)) = U^(Real.logb U n*(-6*(rho ν-cmax ν))) := by
    rw [Real.rpow_mul (x:=U) (by linarith),Real.rpow_logb (by linarith) hU.ne' hn0]
  rw [hp,←Real.rpow_add (by linarith : 0<U)]
  exact Real.rpow_le_rpow_of_exponent_le hU.le (by nlinarith)

theorem full_gain_root_completion_rm :
    ∃ D : ℝ, 0<D ∧ ∀ (ν S F U C capacity lam h : ℝ), 1/2≤ν → ν≤3/4 →
      22/23≤capacity → capacity≤1 → 1<lam → 0≤h → h≤1 → 0≤F → 1<U → 0≤C →
      ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency→ℝ),
      (∀ B : NZIdeal, (B.val.absNorm : ℝ)≤U^(F/12) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^(rho ν*(F-6*Real.logb U (B.val.absNorm : ℝ))+ν*S-
            QRH.RepeatedMarks.Source.gainC ν capacity lam h S (F-6*Real.logb U (B.val.absNorm : ℝ)))) →
      (∀ B : NZIdeal, U^(F/12)<(B.val.absNorm : ℝ) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^(rho ν*F+ν*S)*(B.val.absNorm : ℝ)^(-6*rho ν)) →
      (∑h∈R,f h) ≤ C*D*U^(rho ν*F+ν*S-QRH.RepeatedMarks.Source.gainC ν capacity lam h S F) := by
  let w : NZIdeal→ℝ := fun B=>(B.val.absNorm : ℝ)^(-(3/2:ℝ))
  have hw : Summable w := by
    convert ideal_sixth_power_summable (1/4) (by norm_num) using 1
    funext B
    dsimp [w]
    norm_num
  have hw0 (B : NZIdeal) : 0≤w B := by dsimp [w]; positivity
  let D1 := (∑'B:NZIdeal,w B)+1
  have hsum : (0:ℝ)≤∑'B:NZIdeal,w B := tsum_nonneg hw0
  have hD1 : 0<D1 := by dsimp [D1]; linarith
  obtain ⟨D2,hD2,htail⟩ := ideal_sixth_tail_uniform (1/100) (by norm_num)
  refine ⟨D1+D2,by positivity,?_⟩
  intro ν S F U C capacity lam h hν0 hν1 hB0 hB1 hl hh0 hh1 hF hU hC R f hsmall hlarge
  let A := rho ν*F+ν*S-QRH.RepeatedMarks.Source.gainC ν capacity lam h S F
  let roots := (sixthPairs R).image Prod.snd
  let small := roots.filter (fun B => (B.val.absNorm : ℝ)≤U^(F/12))
  let large := roots.filter (fun B => ¬(B.val.absNorm : ℝ)≤U^(F/12))
  let value := fun B : NZIdeal => ∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))
  have hn (B : NZIdeal) : 1≤(B.val.absNorm : ℝ) := by
    have hp : 0<B.val.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  have hsmall' : (∑B∈small,value B) ≤ C*D1*U^A := by
    have hterm (B : NZIdeal) (hB : B∈small) : value B ≤ C*U^A*w B := by
      have hb := (Finset.mem_filter.mp hB).2
      have hh := hsmall B hb
      have hrp := root_dependent_power_rm (S:=S) (F:=F) hν0 hν1 hB0 hB1 hl hh0 hh1 hU (hn B)
      have hweight : (B.val.absNorm : ℝ)^(-6*(rho ν-cmax ν)) ≤ w B :=
        Real.rpow_le_rpow_of_exponent_le (hn B) (by linarith [(root_reserves hν0 hν1).2.1])
      calc
        value B ≤ C*U^A*(B.val.absNorm : ℝ)^(-6*(rho ν-cmax ν)) := by
          exact hh.trans (by simpa only [mul_assoc,A] using mul_le_mul_of_nonneg_left hrp hC)
        _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)
    calc
      _ ≤ ∑B∈small,C*U^A*w B := Finset.sum_le_sum hterm
      _ = C*U^A*(∑B∈small,w B) := by rw [Finset.mul_sum]
      _ ≤ C*U^A*D1 := mul_le_mul_of_nonneg_left
        ((hw.sum_le_tsum _ (fun B _=>hw0 B)).trans (by dsimp [D1]; linarith)) (by positivity)
      _ = _ := by ring
  have hX : 1≤U^(F/12) := Real.one_le_rpow hU.le (by linarith)
  have hcmax : 0≤cmax ν := by
    dsimp [cmax]
    exact mul_nonneg (by linarith) (by linarith [(baseXi_bounds hν0 hν1).2])
  have hrho : 1+1/100≤6*rho ν := by linarith [(root_reserves hν0 hν1).2.1]
  have htail' := htail (rho ν) (U^(F/12)) hrho hX large (fun B hB=>
    (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hB).2)))
  have hlarge' : (∑B∈large,value B) ≤ C*D2*U^A := by
    calc
      _ ≤ ∑B∈large,C*U^(rho ν*F+ν*S)*(B.val.absNorm : ℝ)^(-6*rho ν) := by
        apply Finset.sum_le_sum
        intro B hB
        exact hlarge B (lt_of_not_ge (Finset.mem_filter.mp hB).2)
      _ = C*U^(rho ν*F+ν*S)*(∑B∈large,(B.val.absNorm : ℝ)^(-6*rho ν)) := by rw [Finset.mul_sum]
      _ ≤ C*U^(rho ν*F+ν*S)*(D2*(U^(F/12))^(-(6*rho ν-1-1/100))) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
      _ = C*D2*U^(rho ν*F+ν*S+(F/12)*(-(6*rho ν-1-1/100))) := by
        rw [←Real.rpow_mul (x:=U) (by linarith)]
        calc
          _ = C*D2*(U^(rho ν*F+ν*S)*U^((F/12)*(-(6*rho ν-1-1/100)))) := by ring
          _ = _ := by rw [←Real.rpow_add (by linarith : 0<U)]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤C*D2)
        apply Real.rpow_le_rpow_of_exponent_le hU.le
        have hg := gain_le_cmax_rm (S:=S) hν0 hν1 hB0 hB1 hl hh0 hh1 hF
        have hgap := (root_reserves hν0 hν1).2.2
        have hm := mul_nonneg (show 0≤(rho ν-1/6)/2-cmax ν-1/1200 by linarith) hF
        dsimp [A]
        nlinarith
  rw [raw_sixth_weighted_sum]
  change (∑B∈roots,value B) ≤ _
  rw [←Finset.sum_filter_add_sum_filter_not roots (fun B => (B.val.absNorm : ℝ)≤U^(F/12)) value]
  have hh := add_le_add hsmall' hlarge'
  convert hh using 1 <;> dsimp [A] <;> ring

end
end QRH.Record1252270103Source.High
