/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B088
import Candidate.Bundles.B096
import Candidate.Bundles.B103
import Candidate.Bundles.B110
import Candidate.Bundles.B117
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass

/- BEGIN ORIGINAL Cycle61.Physical.HighFrequency; sha256 ea6e4bd96d9a5bf8457d9a472aa6cccbccdf56ad8c937d11badbb1e97aed0347 -/
section
                                           
                                        
                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61HighFrequency
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedWidth CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource Cycle61Moment Cycle61FinalRadius
local notation "O" => HeckeFamily.O

/-- Canonical label units leave only the fixed first factor in the norm. -/
theorem fixed_unit_norm (u₀ u : O) (hu : IsUnit u) : normValue (u₀*u)=normValue u₀ := by
  unfold normValue
  rw [Ideal.span_singleton_mul_right_unit hu]

/-- Literal first modulus contains the inactive subset and active conductor.
The two fixed presentation ideals only increase its norm. -/
theorem first_modulus_log_lower (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (normValue (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E))+
      Real.logb Z (normValue (activeConductor C D))≤ Real.logb Z (τ.modulus.absNorm:ℝ) := by
  let S := primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  have hS : 0< normValue S := by
    change 0<((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (subsetGenerator_supported C D hC E).1)
  have hA : 0< normValue (activeConductor C D) := by exact active_norm_pos C D
  have hη : 0<(η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have ht : 0<(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have he : (τ.modulus.absNorm:ℝ)=(η.modulus.absNorm:ℝ)*
      ((Ideal.span {fixedBadMask}).absNorm:ℝ)*((Ideal.span {(72:O)}).absNorm:ℝ)*
      (normValue S*normValue (activeConductor C D)) := by
    rw [hmod]
    simp only [map_mul,Nat.cast_mul,←normValue_mul]
    rfl
  have hf : 0<((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
    by_contra h; have hn := (show (0:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ) by positivity)
    have hz : ((Ideal.span {fixedBadMask}).absNorm:ℝ)=0 := by linarith
    rw [hz] at he; simp only [mul_zero,zero_mul] at he; linarith
  have h72 : 0<((Ideal.span {(72:O)}).absNorm:ℝ) := by
    by_contra h; have hn := (show (0:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) by positivity)
    have hz : ((Ideal.span {(72:O)}).absNorm:ℝ)=0 := by linarith
    rw [hz] at he; simp only [mul_zero,zero_mul] at he; linarith
  have hf1 : (1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
    exact_mod_cast (show 1≤(Ideal.span {fixedBadMask}).absNorm from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hf.ne'))
  have h721 : (1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) := by
    exact_mod_cast (show 1≤(Ideal.span {(72:O)}).absNorm from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h72.ne'))
  have hh : (η.modulus.absNorm:ℝ)*(normValue S*normValue (activeConductor C D))≤(τ.modulus.absNorm:ℝ) := by
    rw [he]; nlinarith [mul_pos hη (mul_pos hS hA),mul_le_mul hf1 h721 (by norm_num) hf.le]
  have hl := Real.logb_le_logb_of_le hZ (mul_pos hη (mul_pos hS hA)) hh
  rw [Real.logb_mul hη.ne' (mul_pos hS hA).ne',Real.logb_mul hS.ne' hA.ne'] at hl
  simpa only [S,add_assoc] using hl

/-- The real nonzero retained second Fourier weight bounds the full literal
joint frequency, with its first inactive and signed numerator factors intact. -/
theorem actual_joint_frequency_log (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (l : NonzeroJointSourceLabel left u₀ unit) (η τ : Character)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex l.val.1.1.1 l.val.1.1.2=>P.val)
        l.val.1.2.val*activeConductor l.val.1.1.1 l.val.1.1.2}) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
      0≤ Real.logb Z (normValue (jointSourceRow left u₀ unit l.val)) ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤
        Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+Real.logb Z fixedPresentationCost+
          2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z 4 := by
  dsimp only
  intro hret
  let C := l.val.1.1.1
  let D := l.val.1.1.2
  let E := l.val.1.2.val
  let S := primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let F := firstSourceNumerator left l.val.1
  let T := u₀*unit l.val.1
  let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
    nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
  have hfactor : jointSourceRow left u₀ unit l.val=((T*S)*F)*A := joint_source_row_factorization left u₀ unit l.val
  have hn : ((T*S)*F)*A≠0 := hfactor.symm ▸ l.property
  have hT : T≠0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hS : S≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hF : F≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul hn)
  have hA : A≠0 := right_ne_zero_of_mul hn
  have hlog : Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))=
      Real.logb Z (normValue T)+Real.logb Z (normValue S)+Real.logb Z (normValue F)+Real.logb Z (normValue A) := by
    rw [hfactor,normValue_mul,normValue_mul,normValue_mul]
    simp only [Real.logb_mul (normValue_pos _ hT).ne' (normValue_pos _ hS).ne',
      Real.logb_mul (mul_pos (normValue_pos _ hT) (normValue_pos _ hS)).ne' (normValue_pos _ hF).ne',
      Real.logb_mul (mul_pos (mul_pos (normValue_pos _ hT) (normValue_pos _ hS)) (normValue_pos _ hF)).ne' (normValue_pos _ hA).ne']
  have hR := (retained_geometry _ _ _ _ hret).1
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos A hA) (retainedWeight_enclosure _ _ hret).2
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne'] at hh
  have hi := main_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N hK hV hZ hb hmod
  have hm := first_modulus_log_lower η τ C D hC E Z hZ hmod
  dsimp only at hi hm
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one _ l.property),?_⟩
  dsimp only [T,S,F,A,C,D,E] at hlog
  linarith

/-- Completed high-count scale for the actual supported frequency. A
negative proposed scale cannot have a nonzero retained physical row. -/
theorem actual_joint_frequency_bound (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (l : NonzeroJointSourceLabel left u₀ unit) (η τ : Character)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex l.val.1.1.1 l.val.1.1.2=>P.val)
        l.val.1.2.val*activeConductor l.val.1.1.1 l.val.1.1.2}) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
    let q := Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+Real.logb Z fixedPresentationCost+
          2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z 4
    0≤ q ∧ normValue (jointSourceRow left u₀ unit l.val)≤ Z^q ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤ q := by
  dsimp only
  intro hret
  have h := actual_joint_frequency_log left u₀ unit l η τ hC hD heq K V Z a δ reserve ξ b N
    hK hV hZ hb hmod hret
  exact ⟨h.1.trans h.2,(Real.logb_le_iff_le_rpow hZ (normValue_pos _ l.property)).mp h.2,h.2⟩

#print axioms actual_joint_frequency_bound
#print axioms fixed_unit_norm
#print axioms first_modulus_log_lower
#print axioms actual_joint_frequency_log
end
end OAI.SevenEighths.Cycle61HighFrequency

end
/- END ORIGINAL Cycle61.Physical.HighFrequency -/

/- BEGIN ORIGINAL Cycle61.Physical.NonexceptionalLedger; sha256 e96fc22c6538c9c175da24140cb13c93fa899f50c26d5b547952694d6f885071 -/
section
                                       
                                  

namespace Cycle61.Physical

noncomputable section
open Cycle61.Arithmetic
open OAI.SevenEighths.LocalMoment

/-- The high-bin reserve before the common-part and projector savings. -/
def highMainReserve (b δ : ℝ) : ℝ :=
  1-unmarkedDensity δ-δ*totalA b-amp b*(5-6*unmarkedDensity δ)

theorem high_density_bounds {δ : ℝ} (hd : q0 ≤ δ ∧ δ ≤ 3/4) :
    2/7 ≤ unmarkedDensity δ ∧ unmarkedDensity δ ≤ rho0 ∧
    1/28 ≤ unmarkedDensity δ+δ-1 ∧
    3/7 ≤ 5*unmarkedDensity δ-1 ∧ 1/7 ≤ 4*unmarkedDensity δ-1 ∧
    4*unmarkedDensity δ-1-δ ≤ -1166/6825 := by
  have hlo := unmarkedDensity_ge_two_sevenths hd.2
  have hd0 : 17/25 ≤ δ := hd.1
  have hden : 0 < 3*(5-2*δ) := by linarith [hd.2]
  have hquot : 1-rho0 ≤ 10*δ/(3*(5-2*δ)) := by
    apply (le_div_iff₀ hden).mpr
    norm_num [rho0]
    linarith
  have hhi : unmarkedDensity δ ≤ rho0 := by
    unfold unmarkedDensity
    linarith
  have hsum : 1/28 ≤ unmarkedDensity δ+δ-1 := by
    have hm := mul_nonneg (show 0 ≤ 3/4-δ by linarith [hd.2])
      (show 0 ≤ 168*δ-20 by linarith)
    have hq : 10*δ/(3*(5-2*δ)) ≤ δ-1/28 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    unfold unmarkedDensity
    linarith
  refine ⟨hlo,hhi,hsum,by linarith,by linarith,?_⟩
  norm_num [rho0] at hhi
  linarith

/-- Algebraic difference formula gives monotonicity on the whole interval;
there is no sampled-bin argument. -/
theorem high_main_reserve_bound {b δ : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q0 ≤ δ ∧ δ ≤ 3/4) :
    720486667/30493190000000 ≤ highMainReserve b δ := by
  have hδ : 0 < 5-2*δ := by linarith [hd.2]
  have hq : 0 < 5-2*q0 := by norm_num [q0]
  have hden : 0 < 3*(5-2*δ)*(5-2*q0) := by positivity
  have hn : 0 ≤ 50*(1-6*amp b) := by
    have ha := (amp_bounds hb).2
    linarith
  have hprod : 3*(5-2*δ)*(5-2*q0) ≤ 3*(5-2*q0)^2 := by
    nlinarith [hd.1]
  have hfrac := div_le_div_of_nonneg_left hn hden hprod
  have hbase := high_derivative_reserve hb
  have hpos : 0 ≤ 50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b := by
    linarith
  have heq : highMainReserve b δ-highMainReserve b q0 =
      (δ-q0)*(50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b) := by
    unfold highMainReserve unmarkedDensity
    field_simp [ne_of_gt hδ, ne_of_gt hq, show 5-δ*2 ≠ 0 by linarith]
    ring
  have hm : 0 ≤ highMainReserve b δ-highMainReserve b q0 := by
    rw [heq]
    exact mul_nonneg (sub_nonneg.mpr hd.1) hpos
  have hr : highMainReserve b q0 = 720486667/30493190000000 := by
    have hρ : unmarkedDensity q0 = rho0 := by norm_num [unmarkedDensity,q0,rho0]
    simpa only [highMainReserve,hρ] using high_reserve b
  linarith

/-- All first common labels are already included in the joint row count.
The remaining common-part exponent is nonpositive. -/
theorem high_common_part_bound (ρ δ c d p R E Bc Lc R₀ : ℝ)
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hρδ : 1 ≤ ρ+δ)
    (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀ ≤
      (4*ρ-1-δ)*p-E-Bc := by
  have hfirst : (1-ρ)*max (c-d) 0-δ*c ≤ -δ*p := by
    by_cases hcd : d ≤ c
    · rw [max_eq_left (sub_nonneg.mpr hcd)]
      nlinarith [mul_nonneg (show 0 ≤ ρ+δ-1 by linarith)
        (sub_nonneg.mpr hcd),mul_nonneg hδ (sub_nonneg.mpr hpD)]
    · rw [max_eq_right (show c-d ≤ 0 by linarith)]
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hpC)]
  have hnum := mul_le_mul_of_nonneg_left hLc hρ
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hrad := mul_le_mul_of_nonneg_left hRp (show 0 ≤ 4*ρ-1 by linarith)
  nlinarith

theorem high_common_part_nonpos {δ c d p R E Bc Lc R₀ : ℝ}
    (hd : q0 ≤ δ ∧ δ ≤ 3/4) (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) :
    (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀ ≤ 0 := by
  obtain ⟨hlo,hhi,hsum,hfive,hfour,hlast⟩ := high_density_bounds hd
  have hδ : 0 ≤ δ := by have := hd.1; norm_num [q0] at this; linarith
  have hb := high_common_part_bound (unmarkedDensity δ) δ c d p R E Bc Lc R₀
    (by linarith) hδ (by linarith) (by linarith) (by linarith)
    hpC hpD hRp hR₀ hLc
  have hm := mul_nonpos_of_nonpos_of_nonneg (show 4*unmarkedDensity δ-1-δ ≤ 0 by linarith) hp
  linarith

theorem high_second_part_nonpos {δ b₂ g₂ t₂ : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b₂) (ht : 0 ≤ t₂) (hg : g₂ ≤ b₂) :
    g₂-t₂-(1+δ)*b₂ ≤ 0 := by
  nlinarith [mul_nonneg hδ hb]

/-- The full exponent in (2.20), including the joint source count and both
common-part savings, has the same strict reserve throughout each cell. -/
theorem high_joint_excess_bound {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q0 ≤ δ ∧ δ ≤ 3/4)
    (hM : 0 ≤ M) (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (ht₂ : 0 ≤ t₂) (hg₂ : g₂ ≤ b₂) :
    M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
      (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*(720486667/30493190000000) := by
  have hδ : 0 ≤ δ := by have := hd.1; norm_num [q0] at this; linarith
  have hρ := (high_density_bounds hd).2.1
  have hcoef : 0 ≤ 5-6*unmarkedDensity δ := by norm_num [rho0] at hρ; linarith
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  have hA' := mul_le_mul_of_nonneg_left hA hδ
  have hcommon := high_common_part_nonpos hd hp hE hB hpC hpD hRp hR₀ hLc
  have hsecond := high_second_part_nonpos hδ hb₂ ht₂ hg₂
  have hreserve := mul_le_mul_of_nonneg_left (high_main_reserve_bound hb hd) hM
  unfold highMainReserve at hreserve
  nlinarith

end
end Cycle61.Physical

#print axioms Cycle61.Physical.high_main_reserve_bound
#print axioms Cycle61.Physical.high_joint_excess_bound

end
/- END ORIGINAL Cycle61.Physical.NonexceptionalLedger -/

/- BEGIN ORIGINAL Cycle61.Physical.HighLedgerGeometry; sha256 f54bcaa7510790d423cea0c0570946ca6b7438783733f2d5e936c2a6fa91880e -/
section
                                     
                                            
                                              
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61HighGeometry
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle61Moment Cycle61FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

def cancelledRadical (left : Bool) (C D : Ideal O) : Ideal O :=
  if left then firstLeftCancelledRadical C D else firstRightCancelledRadical C D

lemma cancelled_pos (left : Bool) (C D : Ideal O) (hC : Supported C) :
    0 < (cancelledRadical left C D).absNorm := by
  cases left <;> exact firstSubsetNorm_pos C D hC _

/-- Every common-part gate used by the high reserve follows from the actual
first canonical pair, its inactive subset, and its signed numerator. -/
theorem actual_first_gates (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2) (Z : ℝ) (hZ : 1< Z) :
    let c := Real.logb Z (l.1.1.absNorm:ℝ)
    let d := Real.logb Z (l.1.2.absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    0≤ p ∧ 0≤ E ∧ 0≤ R₀ ∧ p≤ c ∧ p≤ d ∧ R≤ p ∧ Lc≤5*(R-R₀) := by
  dsimp only
  have hp : 0 < (commonRadical l.1.1 l.1.2).absNorm := by
    rw [first_common_radical_product]
    exact firstCommonSubsetNorm_pos _ _ hC Finset.univ
  have hp1 : (1:ℝ)≤((commonRadical l.1.1 l.1.2).absNorm:ℝ) := by exact_mod_cast hp
  have hE : (1:ℝ)≤((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ) := by
    exact_mod_cast firstCommonSubsetNorm_pos _ _ hC l.2.val
  have hR₀ : (1:ℝ)≤((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ) := by
    exact_mod_cast cancelled_pos left _ _ hC
  have hpcd := commonRadical_norm_le _ _ hC.1 hD.1
  have hpc := Real.logb_le_logb_of_le hZ (by exact_mod_cast hp) (hpcd.trans (min_le_left _ _))
  have hpd := Real.logb_le_logb_of_le hZ (by exact_mod_cast hp) (hpcd.trans (min_le_right _ _))
  have hdiv : Ideal.span {activeConductor l.1.1 l.1.2} ∣ commonRadical l.1.1 l.1.2 := by
    rw [commonRadical_active_principal]
    exact dvd_mul_right _ _
  have hr := Real.logb_le_logb_of_le hZ (active_norm_pos _ _)
    (show ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)≤
      ((commonRadical l.1.1 l.1.2).absNorm:ℝ) by
      exact_mod_cast Nat.le_of_dvd hp (map_dvd Ideal.absNorm hdiv))
  refine ⟨Real.logb_nonneg hZ hp1,Real.logb_nonneg hZ hE,
    Real.logb_nonneg hZ hR₀,hpc,hpd,hr,?_⟩
  cases left
  · exact actual_first_right_log_bound _ _ hC Z hZ
  · exact actual_first_left_log_bound _ _ hC Z hZ

/-- The density fiber's counted missing radical is exactly the inactive
complement plus the cancelled signed part, not an independent label cost. -/
theorem actual_missing_log (left : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (Z : ℝ) :
    Real.logb Z ((firstSourceMissing left l).absNorm:ℝ) =
      Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)-
      Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)+
      Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ) := by
  cases left
  · exact actual_first_right_missing_width _ _ hC _ l.2.property Z
  · exact actual_first_left_missing_width _ _ hC _ l.2.property Z

/-- Literal common ideals on both sides of the second canonical transform
supply all of the final common-part inequalities in the high-bin ledger. -/
theorem actual_high_joint_excess (left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1< Z) (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)
    (ha : a≤ M*Cycle61.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z (l.1.1.absNorm:ℝ)
    let d := Real.logb Z (l.1.2.absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*(720486667/30493190000000) := by
  dsimp only
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hb₂ : 0≤ Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hg₂ : Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  exact Cycle61.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
    (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
    hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂

end
end OAI.SevenEighths.Cycle61HighGeometry
#print axioms OAI.SevenEighths.Cycle61HighGeometry.actual_first_gates
#print axioms OAI.SevenEighths.Cycle61HighGeometry.actual_missing_log
#print axioms OAI.SevenEighths.Cycle61HighGeometry.actual_high_joint_excess

end
/- END ORIGINAL Cycle61.Physical.HighLedgerGeometry -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondOrientedHigh; sha256 67d6bb83c160ed6fd3652eed8fb4c2ed8f300a5dc400426f551b9ad9b20cce0d -/
section
                                          
                                            
                                              
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle61Moment Cycle61FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

open Cycle61HighGeometry

/-- Literal common ideals on both sides of the second canonical transform
supply all of the final common-part inequalities in the high-bin ledger. -/
theorem actual_high_joint_excess_oriented (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1< Z) (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)
    (ha : a≤ M*Cycle61.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*(720486667/30493190000000) := by
  dsimp only
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hb₂ : 0≤ Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hg₂ : Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  cases reflected
  · exact Cycle61.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂
  · exact Cycle61.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpd hpc hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_joint_excess_oriented

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondOrientedHigh -/
