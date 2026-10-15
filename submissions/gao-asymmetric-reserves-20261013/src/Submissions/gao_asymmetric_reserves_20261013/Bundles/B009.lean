/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B002
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B003
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PhysicalEntry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.WidthRanges
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.SourceData ; sha256 0e328009308adda7bf0345d415ae604181bcfd8c0e022af29ae84516a8d8c3d7 -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure WeightedSourceData (D : Cycle25.Weighted.MomentData) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0 ≤ w x ∧ w x ≤ 1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0 ≤ (W x).re

theorem weighted_exists_source_data (D : Cycle25.Weighted.MomentData) : Nonempty (WeightedSourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def WeightedSourceData.modulus {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : Ideal O := ∏P∈F.S,P

instance {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem weighted_source_count_parameters {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI

/- Actual source data adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The legacy count-parameter existence helper is not a Cycle25 count estimate. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.SourceData -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.KappaGeometry ; sha256 4c8fee4f42c350a7ad8c40b2af819277d6f3c5005808edaee6dd10f1e0b672b6 -/
section



namespace Cycle25.Energy

open OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

lemma comparison_denominator_pos (κ : ℝ) (hκ : 7 / 10 ≤ κ) :
    0 < 2 * (6 * κ - 1) := by linarith

lemma comparison_margin (κ : ℝ) (hκ : 7 / 10 ≤ κ) :
    1 / 16 ≤ (2 * κ - 1) / (2 * (6 * κ - 1)) := by
  apply (le_div_iff₀ (comparison_denominator_pos κ hκ)).mpr
  linarith

lemma compact_mesh_le (M B L κ ε : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hε : 0 < ε) (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) :
    fineMesh M B L (3 / 4) ε ≤ fineMesh M B L κ ε := by
  have hcap := sourceCap_nonneg M B L hM hB (count M ε)
  have hr := (bounds M (finalSourceCap M B L ε) 0 ε hM hcap
    (by norm_num) hε).2.2.2.1
  unfold fineMesh mesh
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

end Cycle25.Energy
end
/- END ORIGINAL MODULE Cycle25.Energy.KappaGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceState ; sha256 0c89639bc5b9b258653308da376c5b004951596d230f49dc7dcc68a7bf9bb587 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceState.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=> HeckeFamily.O

export CenteredMomentEnergyReferenceState
  (effectiveRadial radialEnergy_effective effectiveState effective_row_norm
    effective_character_nonprincipal effective_character_cap comparisonFirst comparisonSecond
    comparison_positive comparison_same_product comparison_second_power)

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ M):
    ell≤5*M/96 ∧
    1≤ comparisonFirst Z M ∧
    comparisonFirst Z M≤ comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤ M:=by
  have hkell:16/5*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤5*M/96:=by linarith
  have hlen:M/2≤ Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤ M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:7/10≤κ)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ M)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤37*M/48+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤15*M/16+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=Cycle25CenteredMomentReflectionRetainedLength.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.Cycle25CenteredMomentEnergyReferenceState

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceState -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.AmplitudeHolder ; sha256 11a7b2343e9ee26019a9346cc02fd816c79e1ccf3556a046a03b4c5c7c8823f8 -/
section




/-! Exact amplitude-bin exponent extracted from the weighted fourth moment. -/
noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator

theorem rpow_fourth (U e : ℝ) (hU : 0 ≤ U) : (U^e)^4 = U^(4*e) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hU]
  congr 1
  ring

theorem weighted_amplitude_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (U R total selected epsilon Ccount Cmoment : ℝ)
    (hU : 0 < U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^selected ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^total)
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(total-selected/2+(3*R+1+epsilon)/4) := by
  have hL : 0 < U^selected := Real.rpow_pos_of_pos hU _
  have hh := weighted_row_holder_with_full s S Q P (U^selected) (U^total)
    hL.le (Real.rpow_nonneg hU.le _) hselected hfull
  have hpow (e : ℝ) (n : ℕ) : (U^e)^n = U^(e*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
  have hcomb : (U^total)^4 * (Ccount * U^R)^3 * (Cmoment * U^(1+epsilon)) =
      Ccount^3 * Cmoment * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,hpow,hpow]
    rw [show total*(4:ℕ) = 4*total by ring,show R*(3:ℕ) = 3*R by ring]
    calc
      _ = Ccount^3 * Cmoment * ((U^(4*total) * U^(3*R))*U^(1+epsilon)) := by ring
      _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU]; congr 2; ring
  have htarget : (U^selected)^2 *
      (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 =
      Ccount^4 * Cmoment^4 * U^(4*total+3*R+1+epsilon) := by
    rw [mul_pow,mul_pow,hpow,hpow]
    calc
      _ = Ccount^4 * Cmoment^4 *
          (U^(selected*2) * U^((total-selected/2+(3*R+1+epsilon)/4)*4)) := by ring
      _ = _ := by rw [←Real.rpow_add hU]; congr 2; ring
  have hconst : Ccount^3 * Cmoment ≤ Ccount^4 * Cmoment^4 := by
    have hc0 : 0 ≤ Ccount := le_trans zero_le_one hc
    have hm0 : 0 ≤ Cmoment := le_trans zero_le_one hm
    have hc' : Ccount^3 ≤ Ccount^4 := pow_le_pow_right₀ hc (by norm_num)
    have hm' : Cmoment ≤ Cmoment^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm (show 1 ≤ 4 by norm_num)
    exact mul_le_mul hc' hm' hm0 (by positivity)
  have hh' : (U^selected)^2 * (∑ i ∈ s, ‖S i * P i‖)^4 ≤
      (U^selected)^2 * (Ccount*Cmoment*U^(total-selected/2+(3*R+1+epsilon)/4))^4 := by
    calc
      _ ≤ (U^total)^4 * (s.card : ℝ)^3 * (Cmoment * U^(1+epsilon)) :=
        hh.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
      _ ≤ (U^total)^4 * (Ccount*U^R)^3 * (Cmoment * U^(1+epsilon)) := by
        gcongr
      _ = Ccount^3*Cmoment*U^(4*total+3*R+1+epsilon) := hcomb
      _ ≤ Ccount^4*Cmoment^4*U^(4*total+3*R+1+epsilon) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hU.le _)
      _ = _ := htarget.symm
  have hf := (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp hh'
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
    (by norm_num : (4 : ℕ) ≠ 0)).mp hf

/-- A bounded dilation box pays for the lost selected-prime capacity.  The
box width xi appears only as the explicit small exponent loss delta*xi/4. -/
theorem weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (κ U R q L z v xi delta loss epsilon Ccount Cmoment : ℝ)
    (hκ : 7 / 10 ≤ κ)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*selectedCapacity κ z (v+xi)-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/4) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*z/2+(3*R+1+epsilon)/4+loss/2+delta*xi/4-
        11*delta*(v+xi)/84) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*selectedCapacity κ z (v+xi)-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hd := capacity_damping_uniform hκ hq hqdelta (add_nonneg hv hxi) (z := z)
  calc
    _ ≤ U^(-delta*v/4) *
        (Ccount*Cmoment*U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/4) *
        U^(q*L-(q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/4+q*L-
        (q*selectedCapacity κ z (v+xi)-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.AmplitudeHolder -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.FullWTransport ; sha256 34fbb2de36aa8d35a0a7e02a18598d79c97cd37a506c7145a751084e3fe0c400 -/
section


/-! Transport from the original physical row integral to the complete numerator
integral over w, retaining a bounded rectangle in s and z only. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem centralFullWIntegral_cube_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_w_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E := fullWSlab H
  let T : Set HeightSpace := {t | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hsub : T⊆E := fun _ ht=>⟨⟨ht.1.1,ht.2⟩,Set.mem_univ _⟩
  have hi0 : IntegrableOn f {t : HeightSpace | |t.1.1|≤ H} heightMeasure :=
    continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
      S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hi : IntegrableOn f E heightMeasure := hi0.mono_set (fun _ ht=> ht.1.1)
  have heq : centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)-
      centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H =
      n*(∫t in E\T,f t ∂heightMeasure) := by
    rw [setIntegral_sdiff hT hi hsub]
    dsimp [centralFullWIntegral,centralCubeIntegral,n,E,T,f]
    ring
  have htail : (∫t in E\T,‖f t‖ ∂heightMeasure)≤
      C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply le_trans _ (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
      (a+16*e) ⟨le_rfl,by linarith⟩)
    apply setIntegral_mono_set ((show IntegrableOn (fun t=>‖f t‖) {t : HeightSpace | |t.1.1|≤ H} heightMeasure from hi0.norm).mono_set (fun _ ht=> ht.1))
      (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
    apply Filter.Eventually.of_forall
    intro t ht
    refine ⟨ht.1.1.1,?_⟩
    by_contra hh
    exact ht.2 ⟨⟨ht.1.1.1,le_of_not_gt hh⟩,ht.1.1.2⟩
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in E\T,‖f t‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

/-- The physical row equals the full-w central expression up to a rapidly
vanishing tail. This theorem refers to the actual upstream rowIntegral. -/
theorem uniform_original_row_fullW_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0< X → 0< Y → 1≤ Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1/2)‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := centralFullWIntegral_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hZp : 0< Z := by linarith
  have heq := centralFullWIntegral_transport e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZp (1-a-6*e) (1/2) le_rfl (by linarith)
  rw [←heq]
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY hZp a B H i ha haTop hB hH0 hH hbin
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤ Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1-a-6*e)‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    rw [norm_sub_rev]
    apply h1'.trans
    gcongr
    · exact pow_nonneg (height_pos _).le _
    · exact mul_nonneg hC1 (contourArithmeticCost_nonneg η u P)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.FullWTransport -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPolynomialMass ; sha256 5283db55bb578f8ff55621f5ad642c5be4de438ea1ff46bd2af1e1e2161f6ed2 -/
section




/-! A finite Fourier extraction of coefficient mass from a uniform local bound.
Unlike a pointwise estimate at a single `w`, the four evaluations below determine
all coefficients of the local quadratic polynomial. -/
noncomputable section
namespace Cycle25.Weighted.Numerator

private theorem average_four_norm_le (a b c d : ℂ) (B : ℝ)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B) (hd : ‖d‖ ≤ B) :
    ‖(a + b + c + d) / 4‖ ≤ B := by
  rw [norm_div]
  rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h := (norm_add_le (a + b + c) d).trans
    (add_le_add ((norm_add_le (a + b) c).trans
      (add_le_add (norm_add_le a b) le_rfl)) le_rfl)
  linarith

theorem quadratic_coefficients_of_four_bounds (a b c : ℂ) (B : ℝ)
    (h₁ : ‖quadratic a b c 1‖ ≤ B) (h₂ : ‖quadratic a b c (-1)‖ ≤ B)
    (h₃ : ‖quadratic a b c Complex.I‖ ≤ B)
    (h₄ : ‖quadratic a b c (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B := by
  have ha : a = (quadratic a b c 1 + quadratic a b c (-1) +
      quadratic a b c Complex.I + quadratic a b c (-Complex.I)) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  have hb : b = (quadratic a b c 1 + -(quadratic a b c (-1)) +
      (-Complex.I * quadratic a b c Complex.I) +
      (Complex.I * quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hc : c = (quadratic a b c 1 + quadratic a b c (-1) +
      -(quadratic a b c Complex.I) + -(quadratic a b c (-Complex.I))) / 4 := by
    simp [quadratic, Complex.I_sq]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)

def quadraticMass (a b c : ℂ) (r : ℝ) : ℝ := ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2

theorem quadraticMass_le_of_circle_bound (a b c : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖quadratic a b c T‖ ≤ B) :
    quadraticMass a b c r ≤ 3 * B := by
  have he (T : ℂ) : quadratic a (b * r) (c * (r : ℂ) ^ 2) T =
      quadratic a b c ((r : ℂ) * T) := by unfold quadratic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := quadratic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold quadraticMass
  linarith [hh.1, hh.2.1, hh.2.2]

theorem quadraticMass_mono (a b c : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    quadraticMass a b c r ≤ quadraticMass a b c s := by
  unfold quadraticMass
  gcongr

/-- The complete vertical line visits the complete circle in the local variable.
This is why a bound uniform in the imaginary part really does control every local
coefficient, once the finite degree is known. -/
theorem vertical_cpow_surjective (Q sigma : ℝ) (hQ : 1 < Q) (T : ℂ)
    (hT : ‖T‖ = Q ^ (-sigma)) :
    ∃ w : ℂ, w.re = sigma ∧ (Q : ℂ) ^ (-w) = T := by
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
  have hlog : Real.log Q ≠ 0 := ne_of_gt (Real.log_pos hQ)
  have hT0 : T ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hT
    exact (Real.rpow_pos_of_pos hQ0 (-sigma)).ne' hT.symm
  refine ⟨-Complex.log T / (Real.log Q : ℂ), ?_, ?_⟩
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, hT,
      Real.rpow_def_of_pos hQ0, Real.log_exp]
    field_simp
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hQ0.ne'),
      ← Complex.ofReal_log hQ0.le]
    have hlogC : (Real.log Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    have he : (Real.log Q : ℂ) * -(-Complex.log T / (Real.log Q : ℂ)) =
        Complex.log T := by field_simp
    rw [he, Complex.exp_log hT0]

/-- A uniform bound on one vertical line controls the absolute quadratic
coefficient mass, and all lines to its right. -/
theorem quadraticMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖quadratic a b c ((Q : ℂ) ^ (-w))‖ ≤ B) :
    quadraticMass a b c (Q ^ (-tau)) ≤ 3 * B := by
  apply (quadraticMass_mono a b c (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply quadraticMass_le_of_circle_bound a b c _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

theorem cubic_coefficients_of_four_bounds (a b c d : ℂ) (B : ℝ)
    (h₁ : ‖cubic a b c d 1‖ ≤ B) (h₂ : ‖cubic a b c d (-1)‖ ≤ B)
    (h₃ : ‖cubic a b c d Complex.I‖ ≤ B)
    (h₄ : ‖cubic a b c d (-Complex.I)‖ ≤ B) :
    ‖a‖ ≤ B ∧ ‖b‖ ≤ B ∧ ‖c‖ ≤ B ∧ ‖d‖ ≤ B := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]; norm_num
  have ha : a = (cubic a b c d 1 + cubic a b c d (-1) +
      cubic a b c d Complex.I + cubic a b c d (-Complex.I)) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hb : b = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (-Complex.I * cubic a b c d Complex.I) +
      (Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  have hc : c = (cubic a b c d 1 + cubic a b c d (-1) +
      -(cubic a b c d Complex.I) + -(cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [hI3]
  have hd : d = (cubic a b c d 1 + -(cubic a b c d (-1)) +
      (Complex.I * cubic a b c d Complex.I) +
      (-Complex.I * cubic a b c d (-Complex.I))) / 4 := by
    simp [cubic, Complex.I_sq, hI3]
    ring_nf
    simp [Complex.I_sq, hI3, hI4]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact average_four_norm_le _ _ _ _ B h₁ h₂ h₃ h₄
  · rw [hb]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₄
  · rw [hc]
    exact average_four_norm_le _ _ _ _ B h₁ h₂
      (by simpa only [norm_neg] using h₃) (by simpa only [norm_neg] using h₄)
  · rw [hd]
    apply average_four_norm_le _ _ _ _ B h₁
    · simpa only [norm_neg] using h₂
    · simpa only [norm_mul, Complex.norm_I, one_mul] using h₃
    · simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using h₄

def cubicMass (a b c d : ℂ) (r : ℝ) : ℝ :=
  ‖a‖ + ‖b‖ * r + ‖c‖ * r ^ 2 + ‖d‖ * r ^ 3

theorem cubicMass_le_of_circle_bound (a b c d : ℂ) (r B : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ T : ℂ, ‖T‖ = r → ‖cubic a b c d T‖ ≤ B) :
    cubicMass a b c d r ≤ 4 * B := by
  have he (T : ℂ) : cubic a (b * r) (c * (r : ℂ) ^ 2) (d * (r : ℂ) ^ 3) T =
      cubic a b c d ((r : ℂ) * T) := by unfold cubic; ring
  have hn (T : ℂ) (hT : ‖T‖ = 1) : ‖(r : ℂ) * T‖ = r := by
    rw [norm_mul, hT, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hh := cubic_coefficients_of_four_bounds a (b * r) (c * (r : ℂ) ^ 2)
    (d * (r : ℂ) ^ 3) B
    (by rw [he]; exact hbound _ (hn 1 (by simp)))
    (by rw [he]; exact hbound _ (hn (-1) (by simp)))
    (by rw [he]; exact hbound _ (hn Complex.I (by simp)))
    (by rw [he]; exact hbound _ (hn (-Complex.I) (by simp)))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hh
  unfold cubicMass
  linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]

theorem cubicMass_mono (a b c d : ℂ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
    cubicMass a b c d r ≤ cubicMass a b c d s := by
  unfold cubicMass
  gcongr

theorem cubicMass_le_of_vertical_bound (Q sigma tau B : ℝ) (a b c d : ℂ)
    (hQ : 1 < Q) (hst : sigma ≤ tau)
    (hbound : ∀ w : ℂ, w.re = sigma →
      ‖cubic a b c d ((Q : ℂ) ^ (-w))‖ ≤ B) :
    cubicMass a b c d (Q ^ (-tau)) ≤ 4 * B := by
  apply (cubicMass_mono a b c d (Q ^ (-tau)) (Q ^ (-sigma))
    (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith))).trans
  apply cubicMass_le_of_circle_bound a b c d _ B (Real.rpow_nonneg (by linarith) _)
  intro T hT
  obtain ⟨w, hw, he⟩ := vertical_cpow_surjective Q sigma hQ T hT
  rw [← he]
  exact hbound w hw

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPolynomialMass -/
