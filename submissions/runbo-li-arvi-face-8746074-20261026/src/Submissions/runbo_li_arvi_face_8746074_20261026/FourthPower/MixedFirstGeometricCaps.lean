/- Copyright (c) 2026 Sil. Apache-2.0.
Sharp finite-source geometry for the actual retained first children.
Only exact norm support, character presentation and frequency gates occur;
there is no assumed moment, energy, count or completed source estimate.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstExceptionalNormalization
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstLiveRemainders
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstGeometricCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentFirstPhysicalSource
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization
open CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedFirstLiveRemainders MixedFirstExceptionalNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The sharp cap used by the actual allocated zero coefficient. It is
distinct from the larger support enclosure used solely for tail cutoffs. -/
def sharpSupport (s : Source ι a b) : ℝ :=
  (2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d

def supportConstant (b : ℝ) (N : ℕ) : ℝ := b^2*((2:ℝ)^N)^2

theorem sharp_support_eq (s : Source ι a b) :
    sharpSupport s=supportConstant b (Fintype.card ι)*sourceVolume s/pairNorm s.d := by
  unfold sharpSupport supportConstant
  rw [source_cap_factored]
  unfold sourceVolume
  rw [←s.hpX]
  ring

theorem sharp_support_pos (s : Source ι a b) (hb : 0<b) : 0<sharpSupport s := by
  rw [sharp_support_eq]
  exact div_pos (mul_pos (by unfold supportConstant;positivity) (sourceVolume_pos s))
    (pairNorm_pos s.hd.1 s.hd.2)

/-- Thus no max with 1 is needed in the actual nonzero-source branch. -/
theorem sharp_support_one_le (s : Source ι a b) (ha : 0<a) (seed I : Id)
    (hi : sourceCoefficient s ha seed I≠0) : 1≤sharpSupport s := by
  obtain ⟨hI,hcap⟩ := original_coefficient_cap s ha seed I hi
  have hcap1 : 1≤sourceNormCap s.P b s.T s.d := (ideal_norm_one_le hI).trans hcap
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hcap1

/-- The harmless support constant is paid once for the whole fixed
slot family, uniformly before the source and its moving volume exponent. -/
theorem eventually_sharp_support (N : ℕ) (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(ι : Type u)[Fintype ι] (a : ℝ) (s : Source ι a b),
      Fintype.card ι≤N→∀v : ℝ,sourceVolume s≤Z^v→
      sharpSupport s≤Z^(v+ε)/pairNorm s.d := by
  have hc : ∀ᶠZ : ℝ in atTop,supportConstant b N≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (supportConstant b N)
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι instι a s hcard v hv
  have hz := zero_lt_one.trans hZ
  have hdim : supportConstant b (Fintype.card ι)≤supportConstant b N := by
    unfold supportConstant
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard) 2) (sq_nonneg b)
  rw [sharp_support_eq]
  apply div_le_div_of_nonneg_right _ (pairNorm_pos s.hd.1 s.hd.2).le
  calc
    _≤Z^ε*Z^v := mul_le_mul (hdim.trans hc) hv (sourceVolume_pos s).le
      (Real.rpow_nonneg hz.le _)
    _=Z^(v+ε) := by rw [←Real.rpow_add hz];congr 1;ring

/-- All fixed presentation factors stay in the original input width. -/
def inputWidth (η : Character) (K Z : ℝ) : ℝ :=
  Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost

theorem actual_nominal_log (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z : ℝ) (hK : 0<K) (hV : 0<V) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D}) :
    Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)=
    Real.logb Z (τ.modulus.absNorm:ℝ)+2*Real.logb Z V-inputWidth η K Z-
      Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ) := by
  have hn := nominal_log C D _ (subsetGenerator_supported C D hC E).1 Z K V hK hV
  rw [commonPart_of_equal_support C D hC.1 hCD,
    commonPart_of_equal_support D C hD.1 hCD.symm] at hn
  have hw := actual_reference_width η τ C D hC E K Z hK hZ hmod
  unfold inputWidth
  linarith

/-- The positive-part completion in the actual child scale is charged
before normalization. Either side of the max has the same sharp upper cap. -/
theorem retained_child_log (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z Tfirst Cfirst ξfirst κpad : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hCf : 1≤Cfirst) (hξ : 0≤ξfirst)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hfirst : Tfirst≤Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)
    (n : ℤ) (hn : Retained (frequencyRadius Tfirst Z ξfirst) n) :
    Real.logb Z (nominalChildScale C D E K V Z κpad n)+Real.logb Z (C.absNorm:ℝ)-
      Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z V≤
    Real.logb Z V-inputWidth η K Z+frequencyLoss Z Cfirst ξfirst+κpad := by
  have hnom := actual_nominal_log η τ C D hC hD hCD E K V Z hK hV hZ hmod
  have hret := retained_nominal_frequency C D _ (subsetGenerator_supported C D hC E).1
    Z K V Tfirst Cfirst ξfirst hZ hK hV (zero_lt_one.trans_le hCf) hfirst n hn
  have hc := Real.logb_nonneg hZ (ideal_norm_one_le hC.1)
  have hd := Real.logb_nonneg hZ (ideal_norm_one_le hD.1)
  have hloss := frequencyLoss_nonneg Z Cfirst ξfirst hZ hCf hξ
  rw [nominalChildScale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  by_cases h : 0≤deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)
  · rw [max_eq_left h]
    dsimp only [deficit]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

/-- This is the actual normalized scale needed by the sharp diagonal,
with both full common norms and the original fixed conductor retained. -/
theorem retained_child_ratio (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z Tfirst Cfirst ξfirst κpad : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hCf : 1≤Cfirst) (hξ : 0≤ξfirst)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hfirst : Tfirst≤Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)
    (n : ℤ) (hn : Retained (frequencyRadius Tfirst Z ξfirst) n) :
    nominalChildScale C D E K V Z κpad n*(C.absNorm:ℝ)/((τ.modulus.absNorm:ℝ)*V)≤
      Z^(Real.logb Z V-inputWidth η K Z+frequencyLoss Z Cfirst ξfirst+κpad) := by
  have hz := zero_lt_one.trans hZ
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hτ : 0<(τ.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hchild : 0<nominalChildScale C D E K V Z κpad n := Real.rpow_pos_of_pos hz _
  have hh := retained_child_log η τ C D hC hD hCD E K V Z Tfirst Cfirst ξfirst κpad
    hK hV hZ hCf hξ hmod hfirst n hn
  have hlog : Real.logb Z
      (nominalChildScale C D E K V Z κpad n*(C.absNorm:ℝ)/((τ.modulus.absNorm:ℝ)*V))≤
      Real.logb Z V-inputWidth η K Z+frequencyLoss Z Cfirst ξfirst+κpad := by
    rw [Real.logb_div (mul_pos hchild hc).ne' (mul_pos hτ hV).ne',
      Real.logb_mul hchild.ne' hc.ne',Real.logb_mul hτ.ne' hV.ne']
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hlog
  rwa [Real.rpow_logb hz hZ.ne' (div_pos (mul_pos hchild hc) (mul_pos hτ hV))] at hp

/-- The exact geometric part of FullBudget.zeroCost/reference, including
the artificial divisor and the original ordinary-prefix denominator.
The profile and fixed constants multiply this inequality unchanged. -/
theorem actual_diagonal_ratio (s : Source ι a b) (hb : 0<b)
    (η τ : Character) (C D Dart : Id) (hDart : Dart≠0)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K Z Tfirst Cfirst ξfirst κpad W ε : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hCf : 1≤Cfirst) (hξ : 0≤ξfirst) (hW : 0<W)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hfirst : Tfirst≤Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s))
    (n : ℤ) (hn : Retained (frequencyRadius Tfirst Z ξfirst) n) :
    (nominalChildScale C D E K (sourceVolume s) Z κpad n*W^3*(sharpSupport s)^(1+ε)/
      ((C.absNorm:ℝ)*(Dart.absNorm:ℝ)))/reference τ C D (sourceVolume s) Z≤
    (supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*(sharpSupport s)^ε*
      Z^(Real.logb Z (sourceVolume s)-inputWidth η K Z+3*Real.logb Z W+
        frequencyLoss Z Cfirst ξfirst+κpad) := by
  have hz := zero_lt_one.trans hZ
  have hv := sourceVolume_pos s
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hd : 0<(Dart.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDart)
  have hτ : 0<(τ.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hx := sharp_support_pos s hb
  have hk : 0<nominalChildScale C D E K (sourceVolume s) Z κpad n := Real.rpow_pos_of_pos hz _
  have hpow : 0<Z^(allowance C D Z) := Real.rpow_pos_of_pos hz _
  have hallow : 1≤Z^(allowance C D Z) :=
    Real.one_le_rpow hZ.le (allowance_nonneg C D Z)
  have hr := retained_child_ratio η τ C D hC hD hCD E K (sourceVolume s) Z
    Tfirst Cfirst ξfirst κpad hK hv hZ hCf hξ hmod hfirst n hn
  have hWpow : W^3=Z^(3*Real.logb Z W) := by
    rw [mul_comm (3:ℝ),Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hW]
    norm_num
  have hidentity :
      (nominalChildScale C D E K (sourceVolume s) Z κpad n*W^3*(sharpSupport s)^(1+ε)/
        ((C.absNorm:ℝ)*(Dart.absNorm:ℝ)))/reference τ C D (sourceVolume s) Z=
      (supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*(sharpSupport s)^ε*
        (nominalChildScale C D E K (sourceVolume s) Z κpad n*(C.absNorm:ℝ)/
          ((τ.modulus.absNorm:ℝ)*sourceVolume s))*W^3/Z^(allowance C D Z) := by
    rw [Real.rpow_add hx,Real.rpow_one,sharp_support_eq]
    unfold reference
    field_simp [hc.ne',hd.ne',hτ.ne',hv.ne',hp.ne',hpow.ne']
    <;> ring
  rw [hidentity]
  calc
    _≤(supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*(sharpSupport s)^ε*
        (nominalChildScale C D E K (sourceVolume s) Z κpad n*(C.absNorm:ℝ)/
          ((τ.modulus.absNorm:ℝ)*sourceVolume s))*W^3 :=
      div_le_self (by unfold supportConstant;positivity) hallow
    _≤(supportConstant b (Fintype.card ι)/(pairNorm s.d*(Dart.absNorm:ℝ)))*(sharpSupport s)^ε*
        Z^(Real.logb Z (sourceVolume s)-inputWidth η K Z+frequencyLoss Z Cfirst ξfirst+κpad)*W^3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr (by unfold supportConstant;positivity)) (pow_nonneg hW.le _)
    _=_ := by
      rw [hWpow,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring

/-- A strict reserve left by the original actual second-diagonal gate. -/
def diagonalSlack (R P s d : ℝ) : ℝ := (R-P-s-3*d)/2

theorem diagonal_slack_pos {R P s d : ℝ} (hs : 0≤s) (hd : 0≤d)
    (hbudget : P+2*s+4*d<R) : 0<diagonalSlack R P s d := by
  have hh := MixedLedger.second_diagonal_gate hs hd hbudget
  unfold diagonalSlack
  linarith

/-- The small logarithmic losses are charged once, after the exact
common-norm cancellation. This is a gate for the preceding actual ratio. -/
theorem diagonal_exponent_saved {v width w loss pad R P s d : ℝ}
    (hv : v≤P+s) (hwidth : R≤width) (hw : w≤d)
    (hloss : loss+pad≤diagonalSlack R P s d) :
    v-width+3*w+loss+pad≤-diagonalSlack R P s d := by
  unfold diagonalSlack at hloss ⊢
  linarith

end
end Candidate.FourthPower.MixedFirstGeometricCaps
