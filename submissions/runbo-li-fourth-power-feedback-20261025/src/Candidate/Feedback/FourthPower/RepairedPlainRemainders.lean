/- Copyright (c) 2026 Sil. Apache-2.0.
Generic source-coefficient second zero/tail at ORIGINAL K. These also apply
to the avoided source after the small branch's exact whole-sigma rewrite.
No canonicality or energy estimate is a premise.
-/
import Candidate.Feedback.FourthPower.RepairedRawTail
import Candidate.Feedback.FourthPower.MixedOriginalSecondZero
import Candidate.Feedback.FourthPower.MixedOriginalTailPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedPlainRemainders
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge RayFourExpansion EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal CenteredMomentSupportedTailAggregate
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSectorLocalization
open CenteredMomentSourceRow
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedOriginalTailPower MixedLocalizedDictionary MixedPoissonLocalization
open RepairedRemainderGeometry RepairedRawTail
local notation "Id" => Ideal HeckeFamily.O

theorem uniform_plain_second_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Fintype κ], ∀ a b : ℝ, ∀ s : Source κ a b,
    Fintype.card κ ≤ N → ∀ ha : 0 < a, ∀ (seed : Id) (η : Character) (t Y : ℝ),
      seed ≠ 0 → 1 ≤ Y → sourceNormCap s.P b s.T s.d ≤ Y →
      ‖sourceSecondZero (sourceColumns s) (sourceCoefficient s ha seed) η t‖ ≤
        C * (profileCap s)^2 * Y^(1+ε) / (seed.absNorm : ℝ) := by
  obtain ⟨C0,hC0,hbound⟩ := original_column_bound N (ε/2) (half_pos hε)
  refine ⟨128*C0^2,by positivity,?_⟩
  intro κ instκ a b s hcard ha seed η t Y hseed hY hcap
  have hY0 := zero_lt_one.trans_le hY
  have hsize (I : Id) (hn : sourceCoefficient s ha seed I ≠ 0) := original_coefficient_cap s ha seed I hn
  have hc (I : Id) (_ : I ∈ supportedColumns (sourceColumns s)) (hn : sourceCoefficient s ha seed I ≠ 0) :
      ‖sourceCoefficient s ha seed I‖ ≤ C0 * profileCap s * Y^(ε/2) :=
    hbound κ a b s hcard ha seed I Y (hsize I hn).1 hY ((hsize I hn).2.trans hcap)
  have hh := sourceSecondZero_divisor_bound (sourceColumns s) (sourceCoefficient s ha seed) η t
    (C0*profileCap s*Y^(ε/2)) Y (by have hp := profileCap_nonneg s; positivity) hY0.le seed hseed hc
    (fun I _ hn => source_coefficient_seed s ha seed I hn) (fun I _ hn => (hsize I hn).2.trans hcap)
  have hp : (Y^(ε/2))^2 * Y = Y^(1+ε) := by
    rw [← Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring, Real.rpow_add hY0, Real.rpow_one]
    ring
  apply hh.trans_eq
  calc
    _ = (128*C0^2)*(profileCap s)^2*((Y^(ε/2))^2*Y)/(seed.absNorm:ℝ) := by ring
    _ = _ := by rw [hp]

/-- Sharp support is used literally, including the zero subunit case.
The only character dependence is inside the actual diagonal expression. -/
theorem uniform_plain_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Fintype κ], ∀ a b : ℝ, ∀ s : Source κ a b,
    Fintype.card κ ≤ N → ∀ ha : 0 < a, ∀ (seed : Id) (η : Character) (t K Z B : ℝ),
      seed ≠ 0 → 0 ≤ K → 1 < Z → sourceNormCap s.P b s.T s.d ≤ Z^B →
    ‖(K:ℂ) * paperRadialFourier ballProfile 0 * sourceSecondZero (sourceColumns s) (sourceCoefficient s ha seed) η t‖ ≤
      K * ‖paperRadialFourier ballProfile 0‖ *
        (C * (profileCap s)^2 * sourceNormCap s.P b s.T s.d * Z^(B*ε) / (seed.absNorm:ℝ)) := by
  obtain ⟨C,hC,hzero⟩ := uniform_plain_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro κ instκ a b s hcard ha seed η t K Z B hseed hK hZ hcap
  let Y := sourceNormCap s.P b s.T s.d
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hv := sourceVolume_pos s
  have hY0 : 0 ≤ Y := by dsimp only [Y]; rw [sharp_support_factored]; positivity
  by_cases hY : 1 ≤ Y
  · have hYp := zero_lt_one.trans_le hY
    have he := hzero κ a b s hcard ha seed η t Y hseed hY le_rfl
    have hpow : Y^(1+ε) ≤ Y * Z^(B*ε) := by
      rw [Real.rpow_add hYp, Real.rpow_one]
      apply mul_le_mul_of_nonneg_left _ hYp.le
      apply (Real.rpow_le_rpow hYp.le hcap hε.le).trans_eq
      rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (norm_nonneg _))
    apply he.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    convert mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le (sq_nonneg (profileCap s))) using 1 <;> ring
  · have hz (I : Id) : sourceCoefficient s ha seed I = 0 :=
      coefficient_zero_of_cap_lt_one s ha seed (lt_of_not_ge hY) I
    simp only [sourceSecondZero, secondZeroEnergy, hz, zero_mul, mul_zero, star_zero,
      Finset.sum_const_zero, norm_zero]
    positivity

/-- Original source tail after the same K/16,W=1 specialization. Spend
BU to insert Nu^-1 explicitly; no selected-volume factor is present here. -/
theorem uniform_plain_tail_seed (B BU ζ saving : ℝ) (hB : 0 ≤ B) (hζ : 0 < ζ) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (κ : Type u) [Fintype κ], ∀ a b : ℝ, ∀ s : Source κ a b, ∀ ha : 0 < a, 0 ≤ b →
    ∀ (u seed : Id) (η : Character) (t K X T : ℝ), u ≠ 0 → (u.absNorm:ℝ) ≤ Z^BU →
      0 < K → 0 < X → poolCap s ≤ Z^B → sourceNormCap s.P b s.T s.d ≤ X →
      X ≤ Z^B → K ≤ Z^B → T ≤ Z^B → X^2/K ≤ T →
    ‖secondDiscardedEnergy η t (sourceColumns s) (sourceCoefficient s ha seed) ballProfile K T Z ζ‖ ≤
      Ctail * (profileCap s)^2 * Z^(-saving) / (u.absNorm:ℝ) := by
  obtain ⟨control,C,hC,htail⟩ := original_tail_arbitrary_saving B ζ (saving+BU) hB hζ
  let sem := control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  have hsem : 0 ≤ sem := apply_nonneg _ _
  let Ctail := 1+C*sem
  have hCt : 0 < Ctail := by dsimp only [Ctail]; positivity
  have hCC : C*sem ≤ Ctail := by dsimp only [Ctail]; linarith
  refine ⟨Ctail,hCt,htail.mono ?_⟩
  intro Z hZdata
  refine ⟨hZdata.1,?_⟩
  intro κ instκ a b s ha hb u seed η t K X T hu hUcap hK hX hpool hsupport hXcap hKcap hTcap hcutoff
  have hz := zero_lt_one.trans hZdata.1
  have hone : (1:ℝ) ≤ Z^B := Real.one_le_rpow hZdata.1.le hB
  have hkn : K/16 ≤ Z^B := (show K/16 ≤ K by linarith).trans hKcap
  have hscale : X^2/(16*(K/16)*(1:ℝ)^4) ≤ T := by
    simpa only [show 16*(K/16)*(1:ℝ)^4=K by ring] using hcutoff
  have he := hZdata.2 κ a b s ha hb seed η t (K/16) 1 X T
    (by positivity) (by norm_num) hX hpool hsupport hXcap hkn hone (by simpa using hone) hTcap hscale
  have hid := source_discarded η t (sourceColumns s) (sourceCoefficient s ha seed) (K/16) 1 T Z ζ (by norm_num)
  rw [show 16*(K/16)*(1:ℝ)^4=K by ring, Complex.ofReal_one, div_one] at hid
  rw [← hid]
  have hp := spend_tail 1 (u.absNorm:ℝ) Z 0 BU saving (by norm_num)
    (zero_lt_one.trans_le (ideal_norm_one_le hu)) hZdata.1 (by simp) hUcap
  simp only [one_pow, one_mul, mul_zero, add_zero] at hp
  calc
    _ ≤ C*(profileCap s)^2*sem*Z^(-(saving+BU)) := he
    _ ≤ Ctail*(profileCap s)^2*Z^(-(saving+BU)) := by
      have hh := mul_le_mul_of_nonneg_right hCC
        (mul_nonneg (sq_nonneg (profileCap s)) (Real.rpow_nonneg hz.le (-(saving+BU))))
      convert hh using 1 <;> ring
    _ ≤ (Ctail*(profileCap s)^2)*(Z^(-saving)/(u.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hCt.le (sq_nonneg _))
    _ = _ := by ring

end
end Candidate.Feedback.FourthPower.RepairedPlainRemainders
