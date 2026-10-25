/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform actual first/second cutoff construction. The coarse exponents
below pay only support and tail admissibility; sharpSupport remains the
literal zero-mode cap used in the saving ledger. Parent checks Lean.
-/
import Candidate.SilPrior.FourthPower.MixedFirstGeometricCaps
import Candidate.SilPrior.FourthPower.MixedFirstExceptionalWindow
import Candidate.SilPrior.FourthPower.MixedFirstAvoidance
import Candidate.SilPrior.FourthPower.MixedOriginalTailCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstCutoffs
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstMixedRightTransport CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedOriginalTailCaps MixedFirstExceptionalNormalization
open MixedFirstExceptionalWindow MixedFirstGeometricCaps MixedFirstAvoidance
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def sourceExponent (B : ℝ) : ℝ := 3*B+1
def childExponent (B ξ κ : ℝ) : ℝ := 8*B+1+ξ/2+κ
def secondExponent (B : ℝ) : ℝ := 17*B+2
def geometryExponent (B ξsecond : ℝ) : ℝ := secondExponent B+ξsecond
def tailExponent (B ξfirst κ : ℝ) : ℝ := secondExponent B+childExponent B ξfirst κ

def firstCutoff (C D : Id) (E : Finset (CommonIndex C D)) (K V : ℝ) : ℝ :=
  firstNominalScale C D
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V

def secondCutoff (B Z : ℝ) : ℝ := Z^(secondExponent B)

theorem firstCutoff_swap (C D : Id) (E : Finset (CommonIndex C D)) (K V : ℝ) :
    firstCutoff D C (swapSubset C D E) K V=firstCutoff C D E K V := by
  unfold firstCutoff
  rw [swapSubset_generator,nominal_swap]

theorem firstCutoff_pos (C D : Id) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (K V : ℝ) (hK : 0<K) (hV : 0<V) :
    0<firstCutoff C D E K V :=
  firstNominalScale_pos C D _ (subsetGenerator_supported C D hC E).1 K V hK hV

theorem firstCutoff_upper (C D : Id) (E : Finset (CommonIndex C D))
    (K V : ℝ) (hK : 0<K) : firstCutoff C D E K V≤V^2/K := by
  simpa only [firstCutoff,primeSubsetGenerator,span_idealGenerator] using
    first_nominal_scale_le C D E K V hK

/-- Full common norms, not their radicals, give the needed lower
floor. The two finite numerator ideals are nonzero integral ideals. -/
theorem firstCutoff_lower (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V : ℝ) (hK : 0<K) :
    V^2/(K*(C.absNorm:ℝ)*(D.absNorm:ℝ))≤firstCutoff C D E K V := by
  have he : (1:ℝ)≤(Ideal.absNorm
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}):ℝ) :=
    ideal_norm_one_le (subsetGenerator_supported C D hC E).1
  have hr : (1:ℝ)≤(Ideal.absNorm (Ideal.span {activeConductor C D}):ℝ) :=
    ideal_norm_one_le (activeConductor_supported C D hC).1
  unfold firstCutoff firstNominalScale
  rw [commonPart_of_equal_support C D hC.1 hCD,
    commonPart_of_equal_support D C hD.1 hCD.symm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (one_le_mul_of_one_le_of_one_le he hr) (sq_nonneg V)

/-- The positive-part completion retains a polynomial floor even at
arbitrarily small dyadic scales. This prevents a hidden lower-cutoff
assumption on n. -/
theorem child_floor (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z κ : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hκ : 0≤κ) (n : ℤ) :
    V^2/(K*(C.absNorm:ℝ)^2)≤nominalChildScale C D E K V Z κ n := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hd : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.1)
  have ht := firstCutoff_pos C D hC E K V hK hV
  have hn := firstCutoff_lower C D hC hD hCD E K V hK
  have hbase : V^2/(K*(C.absNorm:ℝ)^2)≤
      (D.absNorm:ℝ)*firstCutoff C D E K V/(C.absNorm:ℝ) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn hd.le) hc.le
    convert hh using 1 <;> field_simp [hK.ne',hc.ne',hd.ne'] <;> ring
  apply hbase.trans
  have hlog : Real.logb Z ((D.absNorm:ℝ)*firstCutoff C D E K V/(C.absNorm:ℝ))≤
      Real.logb Z (dyadicScale n)+
        max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ := by
    rw [Real.logb_div (mul_pos hd ht).ne' hc.ne',Real.logb_mul hd.ne' ht.ne']
    have hm := le_max_left (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) (0:ℝ)
    dsimp only [deficit,firstCutoff] at hm ⊢
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hlog
  rwa [Real.rpow_logb hz hZ.ne' (div_pos (mul_pos hd ht) hc)] at hp

/-- Original scales alone control both volume and its reciprocal.
The lower assumption concerns the actual ordinary minimum; for a fixed
positive comparison minimum it holds eventually, as proved below. -/
theorem source_volume_caps (s : Source ι a b) (Z B : ℝ) (hZ : 1<Z)
    (hmin : Z^(-B)≤s.L) (hX₁ : s.X₁≤Z^B) (hX₂ : s.X₂≤Z^B)
    (hP : (∏i,s.P i)≤Z^B) :
    sourceVolume s≤Z^(3*B) ∧ (sourceVolume s)⁻¹≤Z^(2*B) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp1 : (1:ℝ)≤∏i,s.P i := Finset.one_le_prod₀ (fun i _=>s.hP i)
  have hv := sourceVolume_pos s
  have hupper : sourceVolume s≤Z^B*Z^B*Z^B := by
    unfold sourceVolume
    exact mul_le_mul (mul_le_mul hX₁ hX₂ (s.hL.trans_le s.hX₂).le
      (Real.rpow_nonneg hz.le _)) hP (zero_le_one.trans hp1) (by positivity)
  have hlower : Z^(-B)*Z^(-B)≤sourceVolume s := by
    unfold sourceVolume
    calc
      _≤s.X₁*s.X₂ := mul_le_mul (hmin.trans s.hX₁) (hmin.trans s.hX₂)
        (Real.rpow_nonneg hz.le _) (s.hL.trans_le s.hX₁).le
      _≤s.X₁*s.X₂*(∏i,s.P i) := le_mul_of_one_le_right
        (mul_nonneg (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hX₂).le) hp1
  constructor
  · apply hupper.trans_eq
    rw [←Real.rpow_add hz,←Real.rpow_add hz]
    congr 1
    ring
  · have hh := (inv_le_inv₀ hv (mul_pos (Real.rpow_pos_of_pos hz _)
      (Real.rpow_pos_of_pos hz _))).mpr hlower
    apply hh.trans_eq
    rw [←Real.rpow_add hz,←Real.rpow_neg hz.le]
    congr 1
    ring

theorem eventually_original_minimum (L B : ℝ) (hL : 0<L) (hB : 0<B) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ Z^(-B)≤L := by
  have hc : ∀ᶠZ : ℝ in atTop,L⁻¹≤Z^B :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hB)) (L⁻¹)
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
  have hh := (inv_le_inv₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) B)
    (inv_pos.mpr hL)).mpr hc
  simpa only [inv_inv] using hh

/-- Only finite geometry is used in these caps; no physical block or
analytic source estimate is a hypothesis. -/
theorem actual_child_caps (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z B ξ κ : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hZ4 : 4≤Z) (hB : 0≤B)
    (hξ : 0≤ξ) (hκ : 0≤κ)
    (hKcap : K≤Z^B) (hKinv : K⁻¹≤Z^B)
    (hVcap : V≤Z^(3*B)) (hVinv : V⁻¹≤Z^(2*B))
    (hCcap : (C.absNorm:ℝ)≤Z^B) (hDcap : (D.absNorm:ℝ)≤Z^B)
    (n : ℤ) (hn : Retained (frequencyRadius (firstCutoff C D E K V) Z ξ) n) :
    0<nominalChildScale C D E K V Z κ n ∧
      nominalChildScale C D E K V Z κ n≤Z^(childExponent B ξ κ) ∧
      (nominalChildScale C D E K V Z κ n)⁻¹≤Z^(7*B) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have hd : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.1)
  have hchild : 0<nominalChildScale C D E K V Z κ n := Real.rpow_pos_of_pos hz _
  have ht := firstCutoff_pos C D hC E K V hK hV
  have htcap : firstCutoff C D E K V≤Z^(7*B) := by
    apply (firstCutoff_upper C D E K V hK).trans
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hKinv
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hncap : dyadicScale n≤Z^(7*B+1+ξ/2) := by
    apply (retained_scale_le _ n hn).trans
    unfold frequencyRadius
    calc
      _≤Z*(Z^(7*B)*Z^(ξ/2)) := by
        exact mul_le_mul hZ4 (mul_le_mul_of_nonneg_right htcap
          (Real.rpow_nonneg hz.le _)) (by positivity) hz.le
      _=Z^(7*B+1+ξ/2) := by
        nth_rw 1 [←Real.rpow_one Z]
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  have hlogn : Real.logb Z (dyadicScale n)≤7*B+1+ξ/2 := by
    have hh := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) hncap
    rwa [Real.logb_rpow hz hZ.ne'] at hh
  have hlogt : Real.logb Z (firstCutoff C D E K V)≤7*B := by
    have hh := Real.logb_le_logb_of_le hZ ht htcap
    rwa [Real.logb_rpow hz hZ.ne'] at hh
  have hlogd : Real.logb Z (D.absNorm:ℝ)≤B := by
    have hh := Real.logb_le_logb_of_le hZ hd hDcap
    rwa [Real.logb_rpow hz hZ.ne'] at hh
  have hlogc : 0≤Real.logb Z (C.absNorm:ℝ) := Real.logb_nonneg hZ (ideal_norm_one_le hC.1)
  refine ⟨hchild,?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold childExponent
    by_cases h : 0≤deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)
    · rw [max_eq_left h]
      dsimp only [deficit,firstCutoff] at hlogt ⊢
      linarith
    · rw [max_eq_right (le_of_not_ge h)]
      linarith
  · have hfloor := child_floor C D hC hD hCD E K V Z κ hK hV hZ hκ n
    have hinv := (inv_le_inv₀ hchild (div_pos (sq_pos_of_pos hV)
      (mul_pos hK (sq_pos_of_pos hc)))).mpr hfloor
    calc
      _≤(V^2/(K*(C.absNorm:ℝ)^2))⁻¹ := hinv
      _=K*(C.absNorm:ℝ)^2*(V⁻¹)^2 := by field_simp [hK.ne',hc.ne',hV.ne']
      _≤Z^B*(Z^B)^2*(Z^(2*B))^2 := by
        exact mul_le_mul (mul_le_mul hKcap (pow_le_pow_left₀ hc.le hCcap 2)
          (sq_nonneg _) (Real.rpow_nonneg hz.le _))
          (pow_le_pow_left₀ (inv_nonneg.mpr hV.le) hVinv 2) (sq_nonneg _) (by positivity)
      _=Z^(7*B) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
          ←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        norm_num only [Nat.cast_ofNat]
        ring

theorem fourth_cutoff_cap (Z B X K W : ℝ) (hZ : 1<Z)
    (hX : 0≤X) (hK : 0<K) (hW : 0<W)
    (hXcap : X≤Z^(sourceExponent B)) (hKinv : K⁻¹≤Z^(7*B))
    (hWinv : W⁻¹≤Z^B) : X^2/(16*K*W^4)≤secondCutoff B Z := by
  have hz := zero_lt_one.trans hZ
  calc
    _=(X^2*K⁻¹*(W⁻¹)^4)/16 := by field_simp [hK.ne',hW.ne']
    _≤X^2*K⁻¹*(W⁻¹)^4 := div_le_self (by positivity) (by norm_num)
    _≤(Z^(sourceExponent B))^2*Z^(7*B)*(Z^B)^4 := by
      exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ hX hXcap 2) hKinv
        (inv_nonneg.mpr hK.le) (sq_nonneg _))
        (pow_le_pow_left₀ (inv_nonneg.mpr hW.le) hWinv 4) (by positivity) (by positivity)
    _=secondCutoff B Z := by
      unfold sourceExponent secondCutoff secondExponent
      rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring

/-- Nonzero support may come from the actual avoided source. There
is no invalid inference to a nonzero unavoided coefficient. -/
theorem actual_support_one_le (s : Source ι a b) (ha : 0<a) (u seed I : Id)
    (hi : sourceCoefficient (avoidSource s u) ha seed I≠0) : 1≤sharpSupport s := by
  exact sharp_support_one_le (avoidSource s u) ha seed I hi

/-- One explicit choice handles every original source, common label,
artificial divisor and both children after the same threshold. The
first cutoff is its exact nominal recipe; the second is independent
even of the labels. All remaining inputs are original numeric scales.

No assumption that a suitable cutoff exists occurs in this statement.
The displayed sourceExponent is deliberately coarse and is not used
in place of sharpSupport in the diagonal saving. -/
theorem uniform_actual_cutoffs (N : ℕ) (b B ξfirst ξsecond κ : ℝ)
    (hb : 0<b) (hB : 1≤B) (hξfirst : 0≤ξfirst) (hξsecond : 0<ξsecond) (hκ : 0<κ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→Z^(-B)≤s.L→
      s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀(K W : ℝ),0<K→0<W→K≤Z^B→K⁻¹≤Z^B→W≤Z^B→W⁻¹≤Z^B→
    ∀(C D Dart : Id)(hC : Supported C)(hD : Supported D),
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D→
      (C.absNorm:ℝ)≤Z^B→(D.absNorm:ℝ)≤Z^B→(Dart.absNorm:ℝ)≤Z^B→
    ∀E : Finset (CommonIndex C D),
    let X:=sharpSupport s
    let Tfirst:=firstCutoff C D E K (sourceVolume s)
    let Tsecond:=secondCutoff B Z
    let Btail:=tailExponent B ξfirst κ
    poolCap s≤Z^Btail ∧ sourceNormCap s.P b s.T s.d≤Z^(sourceExponent B) ∧
    0<X ∧ X≤Z^(sourceExponent B) ∧ X≤Z^Btail ∧
    0<Tfirst ∧ Tfirst≤Z^Btail ∧ 0<Tsecond ∧
    Tsecond≤Z^(geometryExponent B ξsecond-ξsecond) ∧ Tsecond≤Z^Btail ∧
    W≤Z^Btail ∧ W⁻¹≤Z^Btail ∧ (Dart.absNorm:ℝ)≤Z^Btail ∧
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
      let KL:=nominalChildScale C D E K (sourceVolume s) Z κ n
      let KR:=nominalChildScale D C (swapSubset C D E) K (sourceVolume s) Z κ n
      0<KL ∧ 0<KR ∧ KL≤Z^Btail ∧ KR≤Z^Btail ∧
      KL⁻¹≤Z^(7*B) ∧ KR⁻¹≤Z^(7*B) ∧
      X^2/(16*KL*W^4)≤Tsecond ∧ X^2/(16*KR*W^4)≤Tsecond ∧
      ∀z∈annularRows n,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤KL ∧
        (Ideal.absNorm (Ideal.span {z}):ℝ)≤KR := by
  filter_upwards [eventually_source_caps N b B B 1 (by norm_num),
    eventually_sharp_support N b 1 (by norm_num),eventually_padding κ hκ,
    Filter.eventually_ge_atTop (4:ℝ)] with Z hsource hsharp hpad hZ4
  have hZ := hsource.1
  have hz := zero_lt_one.trans hZ
  have hB0 : 0≤B := zero_le_one.trans hB
  have hSB : sourceExponent B≤tailExponent B ξfirst κ := by
    unfold sourceExponent tailExponent secondExponent childExponent
    linarith
  have hCB : childExponent B ξfirst κ≤tailExponent B ξfirst κ := by
    unfold tailExponent secondExponent
    linarith
  have hTB : secondExponent B≤tailExponent B ξfirst κ := by
    unfold tailExponent childExponent
    linarith
  have hBB : B≤tailExponent B ξfirst κ := by
    unfold tailExponent secondExponent childExponent
    linarith
  have h7B : 7*B≤tailExponent B ξfirst κ := by
    unfold tailExponent secondExponent childExponent
    linarith
  refine ⟨hZ,?_⟩
  intro ι instι a s hcard hmin hX₁ hX₂ hY₁ hY₂ hP
    K W hK hW hKcap hKinv hWcap hWinv C D Dart hC hD hCD hCcap hDcap hDart E
  dsimp only
  have hvc := source_volume_caps s Z B hZ hmin hX₁ hX₂ hP
  have hsc := hsource.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hnorm : sourceNormCap s.P b s.T s.d≤Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hsc.2
  have hpool : poolCap s≤Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hsc.1
  have hp1 : (1:ℝ)≤pairNorm s.d := by
    exact one_le_mul_of_one_le_of_one_le (ideal_norm_one_le s.hd.1) (ideal_norm_one_le s.hd.2)
  have hxcap : sharpSupport s≤Z^(sourceExponent B) :=
    (hsharp.2 ι a s hcard (3*B) hvc.1).trans
      (div_le_self (Real.rpow_nonneg hz.le _) hp1)
  have hx := sharp_support_pos s hb
  have ht := firstCutoff_pos C D hC E K (sourceVolume s) hK (sourceVolume_pos s)
  have htcap : firstCutoff C D E K (sourceVolume s)≤Z^(7*B) := by
    apply (firstCutoff_upper C D E K (sourceVolume s) hK).trans
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ (sourceVolume_pos s).le hvc.1 2) hKinv
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  refine ⟨hpool.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hSB),hnorm,hx,hxcap,
    hxcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hSB),ht,
    htcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le h7B),
    Real.rpow_pos_of_pos hz _,?_,
    Real.rpow_le_rpow_of_exponent_le hZ.le hTB,
    hWcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBB),
    hWinv.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBB),
    hDart.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBB),?_⟩
  · unfold secondCutoff geometryExponent
    simp only [add_sub_cancel_right,le_refl]
  · intro n hn
    have hl := actual_child_caps C D hC hD hCD E K (sourceVolume s) Z B ξfirst κ
      hK (sourceVolume_pos s) hZ hZ4 hB0 hξfirst hκ.le hKcap hKinv hvc.1 hvc.2 hCcap hDcap n hn
    have hnr : Retained (frequencyRadius
        (firstCutoff D C (swapSubset C D E) K (sourceVolume s)) Z ξfirst) n := by
      rwa [firstCutoff_swap]
    have hr := actual_child_caps D C hD hC hCD.symm (swapSubset C D E) K (sourceVolume s)
      Z B ξfirst κ hK (sourceVolume_pos s) hZ hZ4 hB0 hξfirst hκ.le
      hKcap hKinv hvc.1 hvc.2 hDcap hCcap n hnr
    refine ⟨hl.1,hr.1,hl.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hCB),
      hr.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hCB),hl.2.2,hr.2.2,
      fourth_cutoff_cap Z B _ _ W hZ hx.le hl.1 hW hxcap hl.2.2 hWinv,
      fourth_cutoff_cap Z B _ _ W hZ hx.le hr.1 hW hxcap hr.2.2 hWinv,?_⟩
    intro z hzrow
    have hlrow := actual_annular_inputs C D E K (sourceVolume s) Z κ hZ hpad n z hzrow
    have hrrow := actual_annular_inputs D C (swapSubset C D E) K (sourceVolume s)
      Z κ hZ hpad n z hzrow
    exact ⟨hlrow.1,hlrow.2.2.2,hrrow.2.2.2⟩

end
end Candidate.SilPrior.FourthPower.MixedFirstCutoffs
