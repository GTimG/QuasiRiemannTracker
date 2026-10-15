/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B088
import Submissions.gao_cycle61_plane_20261013.Bundles.B103
import Submissions.gao_cycle61_plane_20261013.Bundles.B117
import Submissions.gao_cycle61_plane_20261013.Bundles.B118
import Submissions.gao_cycle61_plane_20261013.Bundles.B119

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondFrequency; sha256 688327df7aa7e5790d848694d9e53fe3711a71dbabd38eb1adcab9255d28cb09 -/
section
                                                   
                                     
                                        
                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedWidth CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource Cycle61Moment Cycle61FinalRadius
open Cycle61HighFrequency
local notation "O" => HeckeFamily.O

/-- The real nonzero retained second Fourier weight bounds the full literal
joint frequency, with its first inactive and signed numerator factors intact. -/
theorem actual_joint_frequency_log_oriented (reflected left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (l : NonzeroJointSourceLabel left u₀ unit)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0< K) (hV : 0< V) (hZ : 1< Z) (hb : 0< b) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
      0≤ Real.logb Z (normValue (jointSourceRow left u₀ unit l.val)) ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤
        Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+
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
  have hSspan : Ideal.span {S}≠0 := Ideal.span_singleton_eq_bot.not.mpr hS
  have hi := main_fourier_frequency_log reflected C D (Ideal.span {S}) hC.1 hD.1
    hSspan heq K V Z (3*a) δ reserve ξ b N hK hV hZ hb
  dsimp only at hi
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one _ l.property),?_⟩
  dsimp only [T,S,F,A,C,D,E,normValue] at hlog hh hi ⊢
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_frequency_log_oriented

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondFrequency -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondFrequencyBudget; sha256 3a92b1c3ce3342b9785a689bcc243167ec5370b461d0dad35302d825ba337716 -/
section
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplifiedRetainedRadius
open Cycle61Moment Cycle61HighFrequency
local notation "O" => HeckeFamily.O

/-- Fixed units and fixed presentation constants have uniformly vanishing
logarithmic cost. The threshold precedes every arithmetic label and unit
choice. -/
theorem eventual_joint_fixed_frequency_cost (u₀ : O)(b ε : ℝ)(N : ℕ)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀u : Oˣ,
      Real.logb Z (normValue (u₀*(u:O)))+2*(N:ℝ)*Real.logb Z b+Real.logb Z 4≤ε := by
  let c := Real.log (normValue u₀)+2*(N:ℝ)*Real.log b+Real.log 4
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (c/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro u
  rw [fixed_unit_norm u₀ (u:O) u.isUnit]
  have he : Real.logb Z (normValue u₀)+2*(N:ℝ)*Real.logb Z b+Real.logb Z 4=c/Real.log Z := by
    dsimp only [Real.logb,c]
    ring
  rw [he]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr (by nlinarith [(div_le_iff₀ hε).mp hc])

/-- The literal retained weight supplies the sharp joint frequency
budget with all fixed costs absorbed before any moving source is chosen. -/
theorem eventual_actual_joint_frequency_budget (u₀ : O)(b ε : ℝ)(N : ℕ)
    (hb : 0< b)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀(reflected left : Bool)(unit : FirstSourceLabel→ Oˣ)
      (l : NonzeroJointSourceLabel left u₀ (fun k=>(unit k:O)))
      (hC : Supported l.val.1.1.1)(hD : Supported l.val.1.1.2),
      primeSupport l.val.1.1.1=primeSupport l.val.1.1.2 →
      ∀(K V a δ reserve ξ : ℝ),0< K → 0< V → ξ≤ε →
      let C := l.val.1.1.1
      let D := l.val.1.1.2
      let E := l.val.1.2.val
      let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
      let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
      let Kmain := mainCommonRadius Z d
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun p:CommonIndex C D=>p.val) E}) K V Z)
        c (3*a) δ reserve
      let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ
      let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
        nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
      retainedWeight R (normValue A)≠0 →
      let q := Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
        Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+ε
      0≤ q ∧ normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val)≤ Z^q := by
  filter_upwards [eventual_joint_fixed_frequency_cost u₀ b (ε/2) N (by positivity)] with Z h
  refine ⟨h.1,?_⟩
  intro reflected left unit l hC hD heq K V a δ reserve ξ hK hV hξ C D E c d Kmain R A hret q
  have hf := actual_joint_frequency_log_oriented reflected left u₀ (fun k=>(unit k:O)) l
    hC hD heq K V Z a δ reserve ξ b N hK hV h.1 hb hret
  have hp := h.2 (unit l.val.1)
  have hlog : Real.logb Z (normValue (jointSourceRow left u₀ (fun k=>(unit k:O)) l.val))≤ q := by
    dsimp only [q,c,d,C,D]
    linarith
  exact ⟨hf.1.trans hlog,(Real.logb_le_iff_le_rpow h.1 (normValue_pos _ l.property)).mp hlog⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_joint_fixed_frequency_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_joint_frequency_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondFrequencyBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseSupport; sha256 80653b61f2ac3434c18b56fb459d30744d6f53ace02fb7dcaad923cb4491f297 -/
section
                                                         
                                          

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily Cycle61Moment Cycle61HighGeometry
open CenteredMomentRankinRadical CenteredMomentSectorLocalization CenteredMomentCommonHarmonicMass
local notation "O" => HeckeFamily.O

/-- The counted missing radical is a divisor of the actual first common
radical, so its coarse norm never incurs an additional arbitrary parameter. -/
theorem first_missing_norm_le (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1)(hD : Supported l.1.2) :
    0<(firstSourceMissing left l).absNorm ∧
      (firstSourceMissing left l).absNorm≤ l.1.1.absNorm ∧
      (firstSourceMissing left l).absNorm≤ l.1.2.absNorm := by
  have hp := firstCommonSubsetNorm_pos l.1.1 l.1.2 hC
    (firstMissingCommon l.1.1 l.1.2 l.2.val left)
  have hr : 0<(commonRadical l.1.1 l.1.2).absNorm := by
    rw [first_common_radical_product]
    exact firstCommonSubsetNorm_pos _ _ hC Finset.univ
  have hd : firstSourceMissing left l∣commonRadical l.1.1 l.1.2 := by
    rw [first_common_radical_product]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  have hn := Nat.le_of_dvd hr (map_dvd Ideal.absNorm hd)
  have hb := commonRadical_norm_le l.1.1 l.1.2 hC.1 hD.1
  exact ⟨hp,hn.trans (by exact_mod_cast (le_min_iff.mp hb).1),hn.trans (by exact_mod_cast (le_min_iff.mp hb).2)⟩

/-- A polynomial bound for the actual signed first numerator follows from
its exact cancellation ledger, independently of the row or ray choices. -/
theorem first_numerator_log_le (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1)(hD : Supported l.1.2)(Z : ℝ)(hZ : 1< Z) :
    Real.logb Z (normValue (firstSourceNumerator left l))≤5*Real.logb Z (l.1.1.absNorm:ℝ) := by
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  change Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)≤ _
  linarith

/-- The fixed-row support cap in the joint reconstruction theorem follows
from the actual row cap and the first common-ideal cap. -/
theorem joint_missing_support_cap (left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
    (l : NonzeroJointSourceLabel left u₀ unit)(hC : Supported l.val.1.1.1)
    (hD : Supported l.val.1.1.2)(Z q A : ℝ)(hZ : 0< Z)
    (hrow : normValue (jointSourceRow left u₀ unit l.val)≤ Z^q)
    (hfirst : (l.val.1.1.1.absNorm:ℝ)≤ Z^A) :
    ((firstSourceMissing left l.val.1).absNorm:ℝ)≤ Z^A ∧
      ((Ideal.span {jointSourceRow left u₀ unit l.val}*firstSourceMissing left l.val.1).absNorm:ℝ)≤ Z^(q+A) := by
  have hm : ((firstSourceMissing left l.val.1).absNorm:ℝ)≤ Z^A :=
    (Nat.cast_le.mpr (first_missing_norm_le left l.val.1 hC hD).2.1).trans hfirst
  refine ⟨hm,?_⟩
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hrow hm (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_missing_norm_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_numerator_log_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.joint_missing_support_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondCoarseSupport -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondHighBins; sha256 322bb18dc9b13a8683aa91f28e5e2bccbcd8b00a7163677eeb63d1c2ed2aa6d1 -/
section
                                                     

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators

/-- Fixed-width exponent bins. Their width is chosen from the strict
reserve before the moving source, and their number is independent of Z. -/
def exponentBin {n : ℕ} (width : ℝ) (x : Fin n→ℝ) : Fin n→ℤ :=
  fun i=>⌊x i/width⌋

def exponentBinUpper {n : ℕ} (width : ℝ) (key : Fin n→ℤ) : Fin n→ℝ :=
  fun i=>((key i:ℝ)+1)*width

theorem exponent_bin_enclosure {n : ℕ} (width : ℝ) (hw : 0< width) (x : Fin n→ℝ) (i : Fin n) :
    x i≤ exponentBinUpper width (exponentBin width x) i ∧
      exponentBinUpper width (exponentBin width x) i≤ x i+width := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x i/width)) hw.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x i/width)) hw
  rw [div_mul_cancel₀ _ hw.ne'] at hlo hhi
  dsimp [exponentBinUpper,exponentBin]
  constructor <;> linarith

/-- A uniform finite bin count from a fixed box of exponent coordinates. -/
theorem exponent_bins_card {κ : Type*} {n : ℕ} (rows : Finset κ)
    (x : κ→ Fin n→ℝ) (width B : ℝ) (hw : 0< width)
    (hx : ∀k∈rows,∀i,-B≤ x k i ∧ x k i≤ B) :
    (rows.image (fun k=>exponentBin width (x k))).card≤
      (Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^n := by
  let box := Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋
  let Box := Fin n→↥box
  have hsub : rows.image (fun k=>exponentBin width (x k))⊆
      Finset.univ.image (fun b : Box=>fun i=>(b i).val) := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    let b : Box := fun i=>⟨exponentBin width (x k) i,Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (hx k hk i).1 hw.le),
       Int.floor_mono (div_le_div_of_nonneg_right (hx k hk i).2 hw.le)⟩⟩
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  have hc : (rows.image (fun k=>exponentBin width (x k))).card≤ Fintype.card Box :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  simpa only [Box,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,box] using hc

def highExponentValue (δ : ℝ) (x : Fin 4→ℝ) : ℝ :=
  x 0+x 1+OAI.SevenEighths.LocalMoment.unmarkedDensity δ*x 2+δ*x 3

/-- Rounding the scalar, missing radical, frequency and raw-volume
coordinates upward costs at most four bin widths throughout the high range. -/
theorem high_exponent_bin_payment (width δ : ℝ) (hw : 0< width)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (x : Fin 4→ℝ) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x))≤
      highExponentValue δ x+4*width := by
  have hρ := Cycle61.Physical.high_density_bounds hδ
  have hρ0 : 0≤ LocalMoment.unmarkedDensity δ := by linarith [hρ.1]
  have hρ1 : LocalMoment.unmarkedDensity δ≤1 := by
    have hh:=hρ.2.1
    norm_num [Cycle61.Arithmetic.rho0] at hh
    linarith
  have hd0 : 0≤δ := by have hh:=hδ.1; norm_num [Cycle61.Arithmetic.q0] at hh; linarith
  have h0 := (exponent_bin_enclosure width hw x 0).2
  have h1 := (exponent_bin_enclosure width hw x 1).2
  have h2 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 2).2 hρ0
  have h3 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 3).2 hd0
  have hρw := mul_le_mul_of_nonneg_right hρ1 hw.le
  have hdw := mul_le_mul_of_nonneg_right hδ.2 hw.le
  unfold highExponentValue
  nlinarith

theorem high_bin_reserve_transfer (width δ target reserve : ℝ) (hw : 0< width)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (x : Fin 4→ℝ)
    (hbound : highExponentValue δ x≤ target-reserve) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x))≤
      target-reserve+4*width := (high_exponent_bin_payment width δ hw hδ x).trans (by linarith)

/-- Sum estimates proved on fixed exponent bins, charging only the fixed
number of bins. No additional count of the source rows appears. -/
theorem high_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→ Fin 4→ℝ)
    (energy : κ→ℝ) (width B δ Z C target reserve : ℝ)
    (hw : 0< width) (hZ : 1≤ Z) (hC : 0≤ C)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4)
    (hx : ∀k∈rows,∀i,-B≤ x k i ∧ x k i≤ B)
    (hpoint : ∀k∈rows,highExponentValue δ (x k)≤ target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k)≤
        C*Z^(highExponentValue δ (exponentBinUpper width key))) :
    (∑k∈rows,energy k)≤
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  let keys := rows.image (fun k=>exponentBin width (x k))
  have hsplit : (∑k∈rows,energy k)=
      ∑key∈keys,∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k := by
    exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
  have hcard := exponent_bins_card rows x width B hw hx
  rw [hsplit]
  calc
    _≤∑_key∈keys,C*Z^(target-reserve+4*width) := by
      apply Finset.sum_le_sum
      intro key hk
      have hh := hbin key hk
      obtain ⟨k,hrow,rfl⟩ := Finset.mem_image.mp hk
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ
          (high_bin_reserve_transfer width δ target reserve hw hδ (x k) (hpoint k hrow))) hC)
    _=(keys.card:ℝ)*(C*Z^(target-reserve+4*width)) := by simp
    _≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.exponent_bin_enclosure
#print axioms OAI.SevenEighths.Cycle61InitialMass.exponent_bins_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_exponent_bin_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_bin_reserve_transfer
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_binned_sum

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondHighBins -/
