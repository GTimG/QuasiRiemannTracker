/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B047
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B053
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B059
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B065
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B073
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B075
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B080
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B081
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B082
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowOriginalEnergy

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowOriginalEnergy ; sha256 fb2388f6a609b0ed7f0c617049eb3d6bf848028ac9d7a6dedfc86804588258eb -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowOriginalEnergy.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_original_completed_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+507*η) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_rows_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hLP (i : σ) (P : Ideal Eis) (hP : P∈lists' i) : IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2 ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hh := he (σ:=σ) Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    hLP hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_actual_puncture_lists lists hprime Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowOriginalEnergy -/

/- BEGIN ORIGINAL MODULE Analytic.JointCompleteBins ; sha256 e2d7ebc807dcd5967665805c06e2eb3c600f2c443b1429244f152cb3e23cbb3a -/
section


/-! A single total finite classifier on reconstructed nonzero rows.
The exceptional class is explicit; all other rows have a common low/high
buffered bin valid for every finite deletion. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckeInverseAmplification HeckePrimeRay
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile LocalMoment ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem exists_complete_common_source_bins
    {Row Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (η η₀ : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : Q ≤ η₀.modulus)
    (w : Row → NonzeroElement) (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (I : ℕ) (hI : 0 < I) (hwidth : (49/100 : ℝ) ≤ I*(e/2))
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ bin : Row → Option (Fin (I+1) × Fin (I+1)),
      (∀ u, bin u = none ↔ FixedInducingRow η Q fixedBadMask 1 (w u).val) ∧
      ∀ u b, bin u = some b →
        1 ≤ b.1.val ∧
        let a : ℝ := 51/100+(e/2)*(b.2.val : ℝ)
        51/100 ≤ a ∧ a ≤ 7/8 ∧
        (a ≤ 167/200 ∨ (67/100 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4)) ∧
        ∀ (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
          (hR : ∀ label,R label ≠ 0),
          jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
            Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀)
              Q hQM (fun _ => hQη₀)) R hR a (a+e)
              ((3*(b.1.val+1) : ℕ)*T) (w u) := by
  let Good := {u : Row // ¬FixedInducingRow η Q fixedBadMask 1 (w u).val}
  obtain ⟨goodBin,hgood⟩ := exists_common_anchor_source_bins (Row := Good) (Slot := Slot)
    M H hH η η₀ Q hQ72 hQM hQη₀ (fun u => w u.val) (fun u => u.property)
    T e hT he I hI hwidth hβupper
  let bin : Row → Option (Fin (I+1) × Fin (I+1)) := fun u =>
    if h : FixedInducingRow η Q fixedBadMask 1 (w u).val then none
    else some (goodBin ⟨u,h⟩)
  refine ⟨bin,?_,?_⟩
  · intro u
    simp only [bin]
    split_ifs <;> simp_all
  · intro u b hb
    by_cases h : FixedInducingRow η Q fixedBadMask 1 (w u).val
    · simp only [bin,dif_pos h] at hb
      cases hb
    · have heq : goodBin ⟨u,h⟩ = b := by
        simpa only [bin,dif_neg h,Option.some.injEq] using hb
      have hh := hgood ⟨u,h⟩
      rw [heq] at hh
      exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

#print axioms exists_complete_common_source_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCompleteBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointExtractedErrorNormalization ; sha256 709f0fc6212787923fb55ca2ba5c3fa74c31261888d84ea0205bbadb6e1a2fa9 -/
section




/-! Literal extracted source powers at the first common reference.
The actual first child volume is compared with its source upper bound
before the four normalized core estimates and the prime average are used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentFirstMixedAllowance CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedDiagonal CenteredMomentAmplifiedRetainedRadius RayFourExpansion
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyCanonicalAmplifiedColumn
local notation "O" => HeckeFamily.O

lemma shortened_error_power_mono (p : O) (hp : p ≠ 0) (k : ℕ)
    (q V C Z allowance Kerror deficit paid eps saving r childV U : ℝ)
    (hq : 0 < q) (hV : 0 < V) (hC : 0 < C) (hZ : 0 < Z)
    (hK : 0 ≤ Kerror) (heps : 0 ≤ eps) (hv : 0 ≤ childV) (hU : 0 ≤ U)
    (hchild : childV ≤ U*(V/C)) (j : Fin 4) :
    (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (childV/(normValue p)^k)^(powers eps j)/reference q V C Z allowance ≤
      U^(powers eps j)*errorCores p k q V C Z allowance Kerror deficit paid eps saving r j := by
  have hpv := pow_pos (normValue_pos p hp) k
  have href : 0 < reference q V C Z allowance := by unfold reference; positivity
  have hbase : childV/(normValue p)^k ≤ U*(V/C/(normValue p)^k) := by
    convert div_le_div_of_nonneg_right hchild hpv.le using 1 <;> ring
  have hpower := Real.rpow_le_rpow (div_nonneg hv hpv.le) hbase (powers_nonneg eps heps j)
  rw [Real.mul_rpow hU (div_nonneg (div_pos hV hC).le hpv.le)] at hpower
  have hcoeff : 0 ≤ (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j :=
    mul_nonneg (mul_nonneg (div_pos hV hC).le (localErrorCost_nonneg _ _))
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZ.le hK j)
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hcoeff) href.le
  rw [error_core_power]
  convert hh using 1 <;> ring

/-- The literal power budget returned by `actual_firstExtractedErrors_power_from_caps`
is transported to the common reference using only the actual child-volume cap. -/
theorem firstExtractedErrors_core_normalization {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (Z d K₀ c delta reserve : ℝ)
    (p : O) (hp : p ≠ 0) (family : Fin 3 → RayCharacter → Character)
    (q V C allowance deficit paid eps saving U : ℝ)
    (r : Fin 3 → RayCharacter → ℝ) (Hcoef : Fin 4 → ℝ)
    (hq : 0 < q) (hV : 0 < V) (hC : 0 < C) (hZ : 0 < Z)
    (heps : 0 ≤ eps) (hU : 0 ≤ U) (hH : ∀ j, 0 ≤ Hcoef j)
    (hvolume : volume s ≤ U*(V/C))
    (hbound : firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family ≤
      mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*localErrorCost p (errorIndex i)*
        ∑ χ : RayCharacter, ∑ j : Fin 4,
          Hcoef j*errorPowers p (errorIndex i+1) q Z
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid saving (r i χ) j*
            (volume s/(normValue p)^(errorIndex i+1))^(powers eps j)) :
    ((V/C)/reference q V C Z allowance)*
      firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family ≤
      mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
        ∑ χ : RayCharacter, ∑ j : Fin 4, Hcoef j*U^(powers eps j)*
          errorCores p (errorIndex i+1) q V C Z allowance
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid eps saving (r i χ) j := by
  have href : 0 < reference q V C Z allowance := by unfold reference; positivity
  have hnorm : 0 ≤ (V/C)/reference q V C Z allowance := (div_pos (div_pos hV hC) href).le
  apply (mul_le_mul_of_nonneg_left hbound hnorm).trans
  calc
    _ = mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
        ∑ χ : RayCharacter, ∑ j : Fin 4, Hcoef j*
          ((V/C)*localErrorCost p (errorIndex i)*errorPowers p (errorIndex i+1) q Z
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid saving (r i χ) j*
            (volume s/(normValue p)^(errorIndex i+1))^(powers eps j)/reference q V C Z allowance) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      apply Finset.sum_le_sum
      intro j hj
      have hh := shortened_error_power_mono p hp (errorIndex i+1) q V C Z allowance
        (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
        (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid eps saving (r i χ)
        (volume s) U hq hV hC hZ (Real.rpow_nonneg hZ.le _) heps (volume_pos s).le hU hvolume j
      simpa only [Nat.add_sub_cancel,mul_assoc] using mul_le_mul_of_nonneg_left hh (hH j)

/-- Fixed valuations and ray characters cost a constant; the source loss
vector remains explicit. This consumes the actual normalized core bound. -/
theorem firstExtractedErrors_of_core_sum {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (Z d K₀ c delta reserve : ℝ)
    (p : O) (family : Fin 3 → RayCharacter → Character)
    (q V C allowance deficit paid eps saving U : ℝ)
    (r : Fin 3 → RayCharacter → ℝ) (Hcoef exponent : Fin 4 → ℝ)
    (hq : 0 < q) (hV : 0 < V) (hC : 0 < C) (hZ : 0 < Z)
    (hU : 0 ≤ U) (hH : ∀ j, 0 ≤ Hcoef j)
    (hnormalized : ((V/C)/reference q V C Z allowance)*
      firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family ≤
      mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
        ∑ χ : RayCharacter, ∑ j : Fin 4, Hcoef j*U^(powers eps j)*
          errorCores p (errorIndex i+1) q V C Z allowance
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid eps saving (r i χ) j)
    (hcores : ∀ i χ j,
          errorCores p (errorIndex i+1) q V C Z allowance
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid eps saving (r i χ) j ≤
          Z^(exponent j)) :
    firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family ≤
      mass s^2*(reference q V C Z allowance/(V/C))*
        (1872*(Fintype.card RayCharacter : ℝ))*(∑ j : Fin 4, Hcoef j*U^(powers eps j)*Z^(exponent j)) := by
  have href : 0 < reference q V C Z allowance := by unfold reference; positivity
  have hx : 0 < V/C := div_pos hV hC
  have hsum : mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
        ∑ χ : RayCharacter, ∑ j : Fin 4, Hcoef j*U^(powers eps j)*
          errorCores p (errorIndex i+1) q V C Z allowance
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid eps saving (r i χ) j ≤
      mass s^2*(1872*(Fintype.card RayCharacter : ℝ))*
        (∑ j : Fin 4, Hcoef j*U^(powers eps j)*Z^(exponent j)) := by
    calc
      _ ≤ mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
          ∑ _χ : RayCharacter, ∑ j : Fin 4, Hcoef j*U^(powers eps j)*Z^(exponent j) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro χ hχ
        exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcores i χ j)
          (mul_nonneg (hH j) (Real.rpow_nonneg hU _)))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        rw [←Finset.sum_mul,actual_valuation_mass]
        ring
  have hh := mul_le_mul_of_nonneg_left (hnormalized.trans hsum) (div_pos href hx).le
  calc
    _ = (reference q V C Z allowance/(V/C))*(((V/C)/reference q V C Z allowance)*
        firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family) := by field_simp
    _ ≤ _ := hh
    _ = _ := by ring

/-- The literal prime average has no cardinality loss. -/
lemma normalized_prime_average_le (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (f : elementPool P → ℝ) (E : ℝ) (hf : ∀ p, f p ≤ E) :
    (56/(P.card : ℝ))*(∑ p : elementPool P, f p) ≤ 56*E := by
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hc : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => hf p))
    (show (0 : ℝ) ≤ 56/(P.card : ℝ) by positivity)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]
  field_simp

#print axioms shortened_error_power_mono
#print axioms firstExtractedErrors_core_normalization
#print axioms firstExtractedErrors_of_core_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExtractedErrorNormalization -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighScalarSector ; sha256 1a50f147116ab8dd3bd78ae4e2c2f6e925dc6c03e484563aeacf0277a6f8d48b -/
section


/-! Actual physical prefactors are bounded on norm sectors. The radius and
three logarithmic costs vary with every label; their tolerances are paid once. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O

theorem secondPrecountFactor_mono_radius (H P : ℝ) (hH : 0 < H) (hP : 0 < P)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (K K' : ℝ) (hK : K ≤ K') (n : Fin 4 → ℤ) :
    secondPrecountFactor H P C D U K n ≤ secondPrecountFactor H P C D U K' n := by
  have hn := (normalizer_pos C D hC U).le
  unfold secondPrecountFactor outerScalar
  gcongr

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

def secondLogCost (s : CommonSecondKernelLabel Slot) (Z : ℝ) : ℝ :=
  Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ)-
    Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ)-
    (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2

/-- Separate sector endpoints pay exactly the sum of their three widths. -/
theorem secondLogCost_le_of_sectors (s : CommonSecondKernelLabel Slot)
    (Z g t b eg et eb : ℝ)
    (hg : Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) ≤ g+eg)
    (ht : t-et ≤ Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ))
    (hb : b-eb ≤ (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2) :
    s.secondLogCost Z ≤ g-t-b+(eg+et+eb) := by
  unfold secondLogCost
  linarith

theorem actualPrecount_le_sector (s : CommonSecondKernelLabel Slot)
    (Z A c d R₁ E₁ omega g₂ t₂ b₂ scalarLoss primeCount K : ℝ) (n : Fin 4 → ℤ)
    (hZ : 1 < Z) (hp : 0 < primeCount)
    (hK : K ≤ Z^(2*A-c-d+R₁+E₁-1+max (d-c) 0+6*(3/500)+(omega-scalarLoss)))
    (hcost : s.secondLogCost Z ≤ g₂-t₂-b₂+scalarLoss) :
    s.actualPrecount Z A c primeCount K n ≤
      (Z^(3/500 : ℝ)/primeCount)*Z^(A-min c d+R₁+E₁-1+5*(3/500)+g₂-t₂-b₂+omega) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  calc
    _ ≤ s.actualPrecount Z A c primeCount
        (Z^(2*A-c-d+R₁+E₁-1+max (d-c) 0+6*(3/500)+(omega-scalarLoss))) n :=
      secondPrecountFactor_mono_radius _ primeCount (Real.rpow_pos_of_pos hz _) hp
        s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.partition _ _ hK n
    _ = (Z^(3/500 : ℝ)/primeCount)*
        Z^(A-min c d+R₁+E₁-1+5*(3/500)+
          Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ)-
          Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ)-
          (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2+
          (omega-scalarLoss)) :=
      s.actualPrecount_eq Z A c d R₁ E₁ (omega-scalarLoss) _ _ _ primeCount _ n hZ hp rfl rfl rfl rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp only [secondLogCost] at hcost; linarith))
      (by positivity)

end CommonSecondKernelLabel

theorem joint_actual_precount_norm_sum_sector
    {α Slot : Type*} [Fintype Slot]
    (S : Finset α) (s : α → CommonSecondKernelLabel Slot) (Ds : α → Finset (Ideal O))
    (t K Radius : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (rayWeight : α → ℂ)
    (Wkernel : SchwartzMap ℝ ℂ) (decay : ℕ)
    (Z A c d R₁ E₁ omega g₂ t₂ b₂ scalarLoss primeCount : ℝ)
    (hZ : 1 < Z) (hp : 0 < primeCount)
    (hK : ∀ v ∈ S, 0 < K v ∧
      K v ≤ Z^(2*A-c-d+R₁+E₁-1+max (d-c) 0+6*(3/500)+(omega-scalarLoss)))
    (hcost : ∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂-b₂+scalarLoss) :
    (∑ v ∈ S, ∑ D ∈ Ds v,
      ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ)*
        ((UniqueFactorizationMonoid.moebius D : ℂ)*
          ((s v).actualPrecount Z A c primeCount (K v) (n v) : ℂ)*rayWeight v)*
        ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
    (Z^(3/500 : ℝ)/primeCount)*
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ)*
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d+R₁+E₁-1+5*(3/500)+g₂-t₂-b₂+omega) : ℝ) : ℂ)*rayWeight v)*
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro D hD
  have hc := (s v).actualPrecount_le_sector Z A c d R₁ E₁ omega g₂ t₂ b₂ scalarLoss
    primeCount (K v) (n v) hZ hp (hK v hv).2 (hcost v hv)
  have hpref : 0 < (s v).actualPrecount Z A c primeCount (K v) (n v) :=
    secondPrecountFactor_pos _ primeCount (Real.rpow_pos_of_pos hz _) hp _ _
      (s v).toKernelLabel.hC (s v).toKernelLabel.hD (s v).partition (K v) (hK v hv).1 (n v)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpref,
    abs_of_pos (Real.rpow_pos_of_pos hz _)]
  have hh := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (mul_nonneg (mul_nonneg
      (abs_nonneg ((1+SecondKernelLabel.kernelScale (n v))^decay))
      (norm_nonneg (UniqueFactorizationMonoid.moebius D : ℂ)))
      (norm_nonneg (rayWeight v)))
      (norm_nonneg (((s v).withProjector D).toKernelLabel.kernelRow
        (t v) (z v) Wkernel (K v) (Radius v) (n v))))
  convert hh using 1 <;> ring

#print axioms CommonSecondKernelLabel.actualPrecount_le_sector
#print axioms joint_actual_precount_norm_sum_sector
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighScalarSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowDeletedGate ; sha256 6a06c62e9997ab3a78e11e4f4285d744d0e01d11768ba6ee08e10d77e1f7fc98 -/
section




/-! The common fixed dictionary upper bin implies the literal low gate
of a source row after exact coefficient transport and finite deletions. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckeFiniteDeletion
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredExceptionalProfile
open HeckeInverseAmplification ConcretePrimeRowBridge LocalMoment
open CenteredMomentSecondHeightFamily ProbeHighRowFamily HeckePrimeRay
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowDeletedGateFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem naturalLowGate_of_deleted_joint_maximum {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (η η₀ : Character)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ : s.fixedModulus = internalQ Q η₀)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)})
    (w : NonzeroElement) (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 w.val)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (R T : Ideal O) (hR : R ≠ 0) (hT : T ≠ 0)
    (z : O) (hz : s.radial.keep z)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff (excluded (excluded (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture) T) I =
        idealCoeff (excluded N.character R) I)
    (d τ e a : ℝ) (k : ℕ)
    (hupper : zeroMaximum
      (fun label => (momentData (jointRelativeParent η
        (relativeSlotTranslate M H hH (fun _ : Unit => η₀)) label)).character w)
      (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right)) w hex)
      (3*(k+1 : ℕ)*Z^τ) < a+2*e)
    (hconductor : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ((excluded
        (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ).modulus.absNorm ≤ Z^d) :
    NaturalLowGate M H hH s η₀ Q hQM hQ d τ e a k z hz := by
  refine ⟨?_,hconductor⟩
  have hnp := jointRelative_ray_nonprincipal M H hH η (fun _ : Unit => η₀)
    (internalQ Q η₀) hQ72 (inf_le_left.trans hQM) (fun _ => inf_le_right)
    w hex parent N () R hR
  have hcompare := jointRelative_ray_zeroMaximum_le M H hH η (fun _ : Unit => η₀)
    (internalQ Q η₀) hQ72 (inf_le_left.trans hQM) (fun _ => inf_le_right)
    w hex parent N () R hR (3*(k+1 : ℕ)*Z^τ)
  have htransfer : zeroMaximum (twistedFamily M H hH ((excluded
      (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse))
      (naturalState_relative_nonprincipal M H hH s η₀ Q hQM hQ z hz)
      (3*(k+1 : ℕ)*Z^τ) ≤
    zeroMaximum (twistedFamily M H hH ((excluded N.character R).product η₀.inverse))
      hnp (3*(k+1 : ℕ)*Z^τ) := by
    apply zeroMaximum_le_of_zero_inclusion
    intro θ
    refine ⟨θ,?_⟩
    intro q hq hzero
    have he : ∀ I : Ideal O,
        idealCoeff (excluded (twistedFamily M H hH ((excluded
          (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ) T) I =
        idealCoeff (twistedFamily M H hH ((excluded N.character R).product η₀.inverse) θ) I := by
      intro I
      simp only [twistedFamily,←excluded_product_ideal _ _ T hT,
        idealCoeff_product,hcoeff I]
    have hnpSource := naturalState_relative_nonprincipal M H hH s η₀ Q hQM hQ z hz θ
    have hdeleted := (excluded_positive_zeros
      (twistedFamily M H hH ((excluded
        (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ)
      T hnpSource hq).mpr hzero
    exact (coefficient_equality_positive_zeros _ _ he (hnp θ) hq).mp hdeleted
  exact (htransfer.trans hcompare).trans_lt hupper


open CenteredMomentEnergyState

theorem eventually_supported_low_gate_of_deleted_common_bin
    {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.width+Bmask+ξ ≤ d →
      ∀ (η : Character) (Q : Ideal O) (hQM : Q ≤ M)
        (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)})
        (w : NonzeroElement) (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
        (R T : Ideal O), R ≠ 0 → T ≠ 0 →
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep z),
      (∀ I : Ideal O,
        idealCoeff (excluded (excluded
          (naturalRow s.character z (s.row_ne_zero z hz.1)).character s.puncture) T) I =
          idealCoeff (excluded N.character R) I) →
      ∀ (τ e a : ℝ) (k : ℕ), 0 < e →
      ∀ (holes : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ label,holes label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right))
        holes hholes a (a+e) (3*(k+1 : ℕ)*Z^τ) w →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k z hz := by
  filter_upwards [eventually_supported_relative_conductor M H hH η₀ radial ξ hξ] with Z hcond
  refine ⟨hcond.1,?_⟩
  intro Bmask d s hd η Q hQM hQ hQ72 w parent N R T hR hT z hz hcoeff τ e a k he holes hholes hbin
  obtain ⟨hex,hupper⟩ := commonAnchor_source_bin_upper M H hH η η₀ (internalQ Q η₀)
    hQ72 (inf_le_left.trans hQM) inf_le_right holes hholes a e (3*(k+1 : ℕ)*Z^τ) he w hbin
  exact naturalLowGate_of_deleted_joint_maximum M H hH (supportedNaturalState s) η η₀ Q hQM hQ
    hQ72 w hex parent N R T hR hT z hz hcoeff d τ e a k hupper
    (hcond.2 Bmask d s hd z hz)

#print axioms naturalLowGate_of_deleted_joint_maximum
#print axioms eventually_supported_low_gate_of_deleted_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowDeletedGate -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSourceBound ; sha256 9c24bbf8f1ed9d6a86aa89c206e743e4714925bc78ab325bf2a5c83cfdeb2d6b -/
section









/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero
open CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentAllocatedNaturalSource
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowSourceBoundFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

theorem actual_live_low_source
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.puncture = 1 → s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b),
      ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      ∀ (C R seed Lproj : Ideal O) (hC : Supported C), R ≠ 0 → seed ∣ C → Squarefree Lproj →
      (C.absNorm : ℝ) ≤ Z^Bcommon → (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ A Mparent nominal pad g allowance geometryLoss clip : ℝ,
      0 ≤ pad → s.width ≤ nominal+pad → 0 ≤ g → g ≤ 1/241 →
      3/500 ≤ allowance → 0 ≤ geometryLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      pad+loss+(67/450)*(geometryLoss+2*clip) ≤ 1/2000000 →
      (∀ B : actualAllocations src.pools C,
        frozenCoefficient B.val C R src.ν src.W src.P ≠ 0 →
        let data := commonData (withHeight src s.character v) C R B
        data.X₁ ≤ Z^L ∧ data.X₂ ≤ Z^L ∧ data.Y₁ ≤ Z^L ∧ data.Y₂ ≤ Z^L ∧
        A+(7/2)*(∑ i : CenteredMomentCommonProfile.liveIndices B.val,w i.val) ≤ Mparent ∧
        Real.logb Z (data.X₁*data.X₂*∏ i : CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-nominal ≤
          A-Mparent+6*(3/500)+g+geometryLoss) →
      sourceEnergy (withHeight src s.character v) (restrictedLowRadial s.radial low) C hC R seed Lproj ≤
        Cbound*((R*C).radical.absNorm : ℝ)^εmask*profileCost src*diagonalControl s.radial.profile*
          (p.control S)^2*(1+|v|+height)^degree *
          Z^(δcommon+(nominal+allowance-1/48000))/((C.absNorm : ℝ)*Lproj.absNorm) := by
  obtain ⟨degree,S,hmain⟩ := actual_common_low_from_parent M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
  obtain ⟨C0,hC0,hsource⟩ := actual_live_common_source_pointwise loInput hiInput Bcommon δcommon hBcommon hδcommon
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C0*Cbound,mul_pos hC0 hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hunit hs low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput C R seed Lproj hC hR hseed hLproj hCcap hLcap
    A Mparent nominal pad g allowance geometryLoss clip
    hpad hwidth hg hgcap hallowance hgeometry hclip hclipCost hbudgetLoss hgeometrySource
  let E := Cbound*((R*C).radical.absNorm : ℝ)^εmask*diagonalControl s.radial.profile*
    (p.control S)^2*(1+|v|+height)^degree*Z^(nominal+allowance-1/48000)
  have hZ : 0 < Z := zero_lt_one.trans hmain.1
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc (B : actualAllocations src.pools C)
      (hB : frozenCoefficient B.val C R src.ν src.W src.P ≠ 0)
      (alloc : Allocation Lproj (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2))) :
      childEnergy (commonData (withHeight src s.character v) C R B) (restrictedLowRadial s.radial low) Lproj alloc ≤ E := by
    obtain ⟨hX₁,hX₂,hY₁,hY₂,hparent,hshift⟩ := hgeometrySource B hB
    exact hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hunit hs low abin k
      habin habinTop hbase hT hlow hfreqGate hheightSource p src hmatch hhi hMs hp₁ hp₂
      C R B Lproj alloc hR hX₁ hX₂ hY₁ hY₂ A Mparent nominal pad g allowance geometryLoss clip
      hparent hshift hpad hwidth hg hgcap hallowance hgeometry hclip hclipCost hbudgetLoss
  have hh := hsource (withHeight src s.character v) hloInput hhiInput
    (restrictedLowRadial s.radial low) C hC R seed Lproj hseed hLproj E Z hE hmain.1 hCcap hLcap
    (fun B hB alloc _ => hc B hB alloc)
  apply hh.trans_eq
  change C0*Z^δcommon*(profileCost src*E)/((C.absNorm : ℝ)*Lproj.absNorm) = _
  dsimp only [E]
  rw [Real.rpow_add hZ]
  ring

#print axioms actual_live_low_source
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSourceBound -/
