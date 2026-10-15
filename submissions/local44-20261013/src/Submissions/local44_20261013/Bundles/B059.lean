/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B023
import Submissions.local44_20261013.Bundles.B028
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B050
import Submissions.local44_20261013.Bundles.B056
import Submissions.local44_20261013.Bundles.B057
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderPhysical ; sha256 e4a6a492a8d41d30fca9d2bed70ac2e166a6b62125528f501923b52cba73b331 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/



noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Submission20261012.Global.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
open Submission20261012.Global.Transport.PrincipalFiniteProduct Submission20261012.Global.Transport.PrincipalFiniteProductX Submission20261012.Global.Transport.PrincipalContours Submission20261012.Global.Transport.PrincipalTransport
local notation "Id" => Ideal HeckeFamily.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=> b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=> b i p*localMultiplier η p s w z)).symm

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply Submission20261012.Global.Transport.PrincipalContours.source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds])) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=> hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : theta < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e ≤ 11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact Submission20261012.Global.Transport.PrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=> hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end Submission20261012.Global.Transport.PrincipalPhysical
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderPhysical -/

/- BEGIN ORIGINAL MODULE Analytic.AllocatedBufferedLength ; sha256 4aec18fe08c3bfab78037835e948882e2a3a8e5fc6465f55e448f51f76ab5f74 -/
section



/-! Actual support and length gates for allocated rows. Subunit clipping
costs only a fixed profile tolerance; the formal projector reduction is
retained explicitly in the length identity. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CenteredMomentNaturalRowSource
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy CenteredMomentHeckeHeight
open CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorRetained CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O

lemma clipped_log_le (Z S b : ℝ) (hZ : 1 < Z) (hS : 0 < S) (hret : 1 ≤ S*b) :
    Real.logb Z (clippedScale S) ≤ Real.logb Z S+Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : clippedScale S ≤ S*max 1 b := by
    apply max_le
    · exact hret.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hS.le)
    · exact (mul_one S).symm.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) hS.le)
  have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (clippedScale_ge_one S)) hc
  rwa [Real.logb_mul hS.ne' hB.ne'] at hh

lemma mul_logb_rpow_base (Z d X : ℝ) (hZ : 1 < Z) (hd : d ≠ 0) :
    d*Real.logb (Z^d) X = Real.logb Z X := by
  rw [Real.logb, Real.log_rpow (zero_lt_one.trans hZ), Real.logb]
  field_simp [hd, (Real.log_pos hZ).ne']

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem retained_positive_support (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t S₁ S₂ b₁ b₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Iic b₁) (hs₂ : Function.support W₂ ⊆ Iic b₂)
    (hn : retainedPositiveRow η m A z W₁ W₂ pool β P t S₁ S₂ ≠ 0) :
    1 ≤ S₁*b₁ ∧ 1 ≤ S₂*b₂ := by
  unfold retainedPositiveRow positiveSlotRow at hn
  rw [← clipped_rowTwistedSum η m A z W₁ t S₁ hS₁,
    ← clipped_rowTwistedSum η m A z W₂ t S₂ hS₂] at hn
  constructor
  · by_contra hh
    have hz := strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t S₁ hS₁ hs₁ (lt_of_not_ge hh)
    simp only [hz, zero_mul, mul_zero, ne_eq, not_true_eq_false] at hn
  · by_contra hh
    have hz := strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t S₂ hS₂ hs₂ (lt_of_not_ge hh)
    simp only [hz, zero_mul, mul_zero, ne_eq, not_true_eq_false] at hn

lemma selectedPlain_norm_pos (D : Ideal O)
    (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) :
    0 < (Ideal.absNorm (selectedPlain D allocation j) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ allocation (Sum.inr j)))

theorem allocated_positive_support (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (t X₁ X₂ b₁ b₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Iic b₁) (hs₂ : Function.support W₂ ⊆ Iic b₂)
    (hn : allocatedPositiveRow η m A z t pool β P D allocation W₁ W₂ X₁ X₂ ≠ 0) :
    1 ≤ (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))*b₁ ∧
    1 ≤ (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))*b₂ := by
  exact retained_positive_support η m A z W₁ W₂ _ _ _ t _ _ b₁ b₂
    (div_pos hX₁ (selectedPlain_norm_pos D allocation 0))
    (div_pos hX₂ (selectedPlain_norm_pos D allocation 1)) hs₁ hs₂ hn

theorem allocated_clipped_length (Z X₁ X₂ b₁ b₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (P : ι → ℝ) (hP : ∀ i, 0 < P i)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (hret₁ : 1 ≤ (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))*b₁)
    (hret₂ : 1 ≤ (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))*b₂) :
    Real.logb Z (clippedScale (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)))+
      Real.logb Z (clippedScale (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)))+
      ∑ i ∈ liveIndices D allocation, Real.logb Z (P i) ≤
    Real.logb Z (X₁*X₂*∏ i, P i)-Real.logb Z (formalReductionFactor D allocation P)+
      Real.logb Z (max 1 b₁*max 1 b₂) := by
  have h₁ := selectedPlain_norm_pos D allocation 0
  have h₂ := selectedPlain_norm_pos D allocation 1
  have hpL : 0 < ∏ i ∈ liveIndices D allocation, P i :=
    Finset.prod_pos (fun i _ => hP i)
  have hpF : 0 < ∏ i ∈ frozenIndices D allocation, P i :=
    Finset.prod_pos (fun i _ => hP i)
  have hraw : 0 < rawRemaining D allocation (X₁*X₂) P :=
    mul_pos (div_pos (mul_pos hX₁ hX₂) (selectedNorm_pos D allocation)) hpL
  have hred : 0 < formalReductionFactor D allocation P :=
    mul_pos (selectedNorm_pos D allocation) hpF
  have hid := congrArg (Real.logb Z) (raw_scale_identity D allocation (X₁*X₂) P)
  rw [Real.logb_mul hraw.ne' hred.ne'] at hid
  have hrawlog : Real.logb Z (rawRemaining D allocation (X₁*X₂) P) =
      Real.logb Z (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))+
      Real.logb Z (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))+
      ∑ i ∈ liveIndices D allocation, Real.logb Z (P i) := by
    unfold rawRemaining selectedNorm
    rw [Real.logb_mul (div_pos (mul_pos hX₁ hX₂) (mul_pos h₁ h₂)).ne' hpL.ne',
      Real.logb_div (mul_pos hX₁ hX₂).ne' (mul_pos h₁ h₂).ne',
      Real.logb_mul hX₁.ne' hX₂.ne', Real.logb_mul h₁.ne' h₂.ne',
      Real.logb_prod _ _ (fun i _ => (hP i).ne'),
      Real.logb_div hX₁.ne' h₁.ne', Real.logb_div hX₂.ne' h₂.ne']
    ring
  rw [hrawlog] at hid
  have hc₁ := clipped_log_le Z _ b₁ hZ (div_pos hX₁ h₁) hret₁
  have hc₂ := clipped_log_le Z _ b₂ hZ (div_pos hX₂ h₂) hret₂
  rw [Real.logb_mul (zero_lt_one.trans_le (le_max_left _ _)).ne'
    (zero_lt_one.trans_le (le_max_left _ _)).ne']
  linarith

theorem allocatedBufferedData_length_bound
    {η : Character} {w : NonzeroElement} {n : ℕ} {profileBound : ℕ → ℝ} {edge e : ℝ}
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (puncture : Ideal O) (hpuncture : puncture ≠ 0)
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P₁ P₂ : BufferedPlainProfile n profileBound edge e) (Z d X₁ X₂ b₁ b₂ : ℝ)
    (P : ι → ℝ) (t : ℝ) (bin : ℕ) (hZ : 1 < Z) (hd : d ≠ 0)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (hret₁ : 1 ≤ (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))*b₁)
    (hret₂ : 1 ≤ (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))*b₂) :
    d*(allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).length ≤
      Real.logb Z (X₁*X₂*∏ i, P i)-Real.logb Z (formalReductionFactor D allocation P)+
        Real.logb Z (max 1 b₁*max 1 b₂) := by
  rw [allocatedBufferedData_length]
  simp only [mul_add, Finset.mul_sum, mul_logb_rpow_base Z d _ hZ hd]
  exact allocated_clipped_length Z X₁ X₂ b₁ b₂ hZ hX₁ hX₂ P hP D allocation hret₁ hret₂

/-- The projector reductions can only shorten the product. The fixed
clipping error is made small uniformly before the live allocations. -/
theorem eventually_allocated_length_tolerance (b₁ b₂ ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (X₁ X₂ : ℝ) (P : ι → ℝ), 0 < X₁ → 0 < X₂ → (∀ i, 1 ≤ P i) →
      ∀ (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))),
      1 ≤ (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))*b₁ →
      1 ≤ (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))*b₂ →
      Real.logb Z (clippedScale (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ)))+
        Real.logb Z (clippedScale (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ)))+
        ∑ i ∈ liveIndices D allocation, Real.logb Z (P i) ≤
      Real.logb Z (X₁*X₂*∏ i, P i)+ξ := by
  filter_upwards [CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost b₁ b₂ ξ hξ]
    with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro X₁ X₂ P hX₁ hX₂ hP D allocation hret₁ hret₂
  have hN (j : Fin 2) : 1 ≤ (Ideal.absNorm (selectedPlain D allocation j) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ allocation (Sum.inr j)))
  have hred : 1 ≤ formalReductionFactor D allocation P :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hN 0) (hN 1))
      (Finset.one_le_prod₀ (fun i _ => hP i))
  have hb := allocated_clipped_length Z X₁ X₂ b₁ b₂ hZ.1 hX₁ hX₂ P
    (fun i => zero_lt_one.trans_le (hP i)) D allocation hret₁ hret₂
  have hr := Real.logb_nonneg hZ.1 hred
  linarith [hZ.2]

#print axioms allocated_positive_support
#print axioms allocated_clipped_length
#print axioms allocatedBufferedData_length_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.AllocatedBufferedLength -/

/- BEGIN ORIGINAL MODULE Analytic.AllocatedBufferedProfiles ; sha256 4db7e5fbcd3ff10dd4f8afc59ab6849cb1862bccada668d47945a3ad975eb5dd -/
section



/-! Actual profile records for allocated source products. Their Mellin
fields are proved uniformly before the live allocation or tail order. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentHeckeVolume CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRetained
open CenteredMomentAllocatedNaturalSource CenteredMomentPrimeSlot ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

/-- The common Mellin constants are selected before the slot subset, tail
order, parent, row, allocation, scale and both independent plain lengths.
No Mellin or pointwise estimate is supplied by the caller. -/
theorem actual_allocated_buffered_profiles
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (n : ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
        (Z d X₁ X₂ : ℝ) (η₀ : ι → Character) (V : ι → ℝ → ℂ) (b P : ι → ℝ)
        (t : ℝ) (bin : ℕ),
      1 < Z^d → 0 < X₁ → 0 < X₂ → (∀ i, 0 < P i) →
      1 ≤ (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))*b₁ →
      1 ≤ (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))*b₂ →
      ∃ P₁ P₂ : BufferedPlainProfile n C edge e,
        P₁.W = dilated W₁ (clipDilation (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))) ∧
        P₂.W = dilated W₂ (clipDilation (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))) ∧
        P₁.σ = 0 ∧ P₂.σ = 0 ∧ P₁.freq = t ∧ P₂.freq = t ∧
        ‖allocatedPositiveRow parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t
          (fun i => primePool M H (b i) (P i))
          (fun i I => idealCoeff (η₀ i).inverse I*V i ((I.absNorm : ℝ)/P i)) P
          D allocation W₁ W₂ X₁ X₂‖^2 =
        ‖(allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin).value
          M H (fun i : liveIndices D allocation => η₀ i.val)
          (fun i : liveIndices D allocation => V i.val) (fun i : liveIndices D allocation => b i.val) Z d‖^2 := by
  obtain ⟨C,hC,hm₁,hm₂⟩ := dilated_mellin_pair_uniform W₁ W₂
    a₁ b₁ (max 1 b₁) a₂ b₂ (max 1 b₂) (-1) 2
    ha₁ (le_max_left _ _) ha₂ (le_max_left _ _) hs₁ hW₁ hs₂ hW₂
  refine ⟨C,hC,?_⟩
  intro n edge e hedge he ι _ _ M _ H η w parent N puncture hpuncture D allocation
    Z d X₁ X₂ η₀ V b P t bin hbase hX₁ hX₂ hP hret₁ hret₂
  have hu₁ : 0 < X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ) :=
    rawScale_pos D allocation X₁ hX₁ 0
  have hu₂ : 0 < X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ) :=
    rawScale_pos D allocation X₂ hX₂ 1
  let P₁ := bufferedDilatedProfile W₁ a₁ b₁ (max 1 b₁) 0 0 ha₁ (le_max_left _ _)
    hs₁ hW₁ C (by simpa only [sub_zero] using hm₁) n edge e 0 t
    (clipDilation (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))) hedge he le_rfl le_rfl
    (clipDilation_ge_one _ hu₁) (clipDilation_le b₁ _ hu₁ hret₁)
  let P₂ := bufferedDilatedProfile W₂ a₂ b₂ (max 1 b₂) 0 0 ha₂ (le_max_left _ _)
    hs₂ hW₂ C (by simpa only [sub_zero] using hm₂) n edge e 0 t
    (clipDilation (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))) hedge he le_rfl le_rfl
    (clipDilation_ge_one _ hu₂) (clipDilation_le b₂ _ hu₂ hret₂)
  refine ⟨P₁,P₂,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact allocatedBufferedData_source_norm_sq M H parent N puncture hpuncture D allocation
    P₁ P₂ Z d X₁ X₂ η₀ V b P W₁ W₂ t bin hbase hP rfl rfl rfl rfl rfl rfl

#print axioms actual_allocated_buffered_profiles
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.AllocatedBufferedProfiles -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedHeight ; sha256 c6a29b89ece352baa206eeddcde1f90e3484c7f5cc18e4aaba77c1356d0a0bbf -/
section






set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckeDetectorDyadicGeometry
open HeckeInverseAmplification HeckePrimeRay HeckePrimeAnnular HeckeFiniteDeletion
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open ConcretePrimeRowBridge LocalMoment ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-- The two literal Fourier separations, retaining the original slot shift.
The right column uses the same formula with the two kernel variables negated. -/
def twoStageFrequency (t v w₁ θ₁ w₂ θ₂ : ℝ) : ℝ :=
  t+v+2*Real.pi*(w₁-θ₁)+2*Real.pi*(w₂-θ₂)

lemma twoStageFrequency_bound (t v w₁ θ₁ w₂ θ₂ X : ℝ)
    (ht : |t| ≤ X) (hv : |v| ≤ X) (hw₁ : |w₁| ≤ X) (hθ₁ : |θ₁| ≤ X)
    (hw₂ : |w₂| ≤ X) (hθ₂ : |θ₂| ≤ X) :
    |twoStageFrequency t v w₁ θ₁ w₂ θ₂| ≤ (2+8*Real.pi)*X := by
  have hp : 0 ≤ 2*Real.pi := by positivity
  have h₁ : |w₁-θ₁| ≤ 2*X := (abs_sub w₁ θ₁).trans (by linarith)
  have h₂ : |w₂-θ₂| ≤ 2*X := (abs_sub w₂ θ₂).trans (by linarith)
  have htv : |t+v| ≤ 2*X := (abs_add_le t v).trans (by linarith)
  have hb₁ := abs_add_le (t+v) (2*Real.pi*(w₁-θ₁))
  have hb₂ := abs_add_le (t+v+2*Real.pi*(w₁-θ₁)) (2*Real.pi*(w₂-θ₂))
  rw [abs_mul, abs_of_nonneg hp] at hb₁ hb₂
  dsimp [twoStageFrequency]
  nlinarith [mul_le_mul_of_nonneg_left h₁ hp, mul_le_mul_of_nonneg_left h₂ hp]

/-- Both the detector parameter and the resulting density degree are inputs:
this external choice therefore cannot feed back into the detector proof. -/
theorem exists_external_height_exponents (τdetector dmin ηaux loss : ℝ) (J : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin)
    (hηaux : 0 < ηaux) (hloss : 0 < loss) :
    ∃ τ ν : ℝ, 0 < ν ∧ ν < τ ∧ τ < τdetector ∧
      4*τ < dmin*ηaux ∧ τ*(J : ℝ) < loss := by
  let τ := min τdetector (min (dmin*ηaux/4) (loss/(J+1)))/2
  have hmin : 0 < min τdetector (min (dmin*ηaux/4) (loss/(J+1))) := by
    apply lt_min hτdetector
    apply lt_min <;> positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτd : τ < τdetector := by
    have hh := min_le_left τdetector (min (dmin*ηaux/4) (loss/(J+1)))
    dsimp [τ] at *; linarith
  have hτη : 4*τ < dmin*ηaux := by
    have hh := (min_le_right τdetector _).trans (min_le_left (dmin*ηaux/4) (loss/(J+1)))
    dsimp [τ] at *; linarith
  have hτJ : τ*(J : ℝ) < loss := by
    have hh := (min_le_right τdetector _).trans (min_le_right (dmin*ηaux/4) (loss/(J+1)))
    have hJ : (0 : ℝ) < J+1 := by positivity
    have he : τ < loss/(J+1) := by dsimp [τ] at *; linarith
    have hm := (lt_div_iff₀ hJ).mp he
    nlinarith
  exact ⟨τ,τ/2,by linarith,by linarith,hτd,hτη,hτJ⟩

/-- One threshold works for every original input height and both Fourier
variables in the smaller cube. -/
theorem twoStageFrequency_uniform (τ ν : ℝ) (hgap : ν < τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ t v w₁ θ₁ w₂ θ₂ : ℝ,
      |t| ≤ Z^ν → |v| ≤ Z^ν → |w₁| ≤ Z^ν → |θ₁| ≤ Z^ν →
      |w₂| ≤ Z^ν → |θ₂| ≤ Z^ν →
      |twoStageFrequency t v w₁ θ₁ w₂ θ₂| ≤ Z^τ := by
  have hh := uniform_power_allowance (2+8*Real.pi) ν τ 1
    zero_le_one (by simpa using hgap)
  filter_upwards [hh] with Z hZ t v w₁ θ₁ w₂ θ₂ ht hv hw₁ hθ₁ hw₂ hθ₂
  exact (twoStageFrequency_bound t v w₁ θ₁ w₂ θ₂ (Z^ν) ht hv hw₁ hθ₁ hw₂ hθ₂).trans
    (by simpa using hZ τ le_rfl)

namespace JointBufferedProductData
variable {η : Character} {w : NonzeroElement} {Slot : Type*} [Fintype Slot]
  {n : ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

/-- Bin selection does not change the literal arithmetic product. -/
def rebin (D : JointBufferedProductData η w Slot n profileBound a e) (i : ℕ) :=
  {D with bin := i}

lemma value_rebin (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (B : Slot → ℝ)
    (Z d : ℝ) (D : JointBufferedProductData η w Slot n profileBound a e) (i : ℕ) :
    (D.rebin i).value M H η₀ V B Z d = D.value M H η₀ V B Z d := rfl

omit [Fintype Slot] in
/-- The four frequency/height conditions in `Admissible` are consequences of
literal shifted frequencies in the smaller Fourier cube. Only the unrelated
conductor, width and prime scale hypotheses remain as premises. -/
theorem admissible_rebin_of_two_stage
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character) (A B : Slot → ℝ)
    (Rwidth τ ν ηaux σmin σmax dmin : ℝ) (I : ℕ)
    (hτ : 0 < τ) (hgap : ν < τ) (hηaux : 0 ≤ ηaux)
    (hheight : 4*τ < dmin*ηaux) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → ∀ i : ℕ, i ≤ I →
    ∀ D : JointBufferedProductData η w Slot n profileBound a e,
    ∀ t v₁ v₂ w₁ θ₁ w₂ θ₂ : ℝ, ∀ v : Slot → ℝ,
    |t| ≤ Z^ν → |v₁| ≤ Z^ν → |v₂| ≤ Z^ν → (∀ j, |v j| ≤ Z^ν) →
    |w₁| ≤ Z^ν → |θ₁| ≤ Z^ν → |w₂| ≤ Z^ν → |θ₂| ≤ Z^ν →
    D.plain₁.freq = twoStageFrequency t v₁ w₁ θ₁ w₂ θ₂ →
    D.plain₂.freq = twoStageFrequency t v₂ w₁ θ₁ w₂ θ₂ →
    (∀ j, D.t+D.v j = twoStageFrequency t (v j) w₁ θ₁ w₂ θ₂) →
    0 ≤ D.r₁ → D.r₁ ≤ Rwidth → 0 ≤ D.r₂ → D.r₂ ≤ Rwidth →
    (∀ j, 0 ≤ D.r j ∧ D.r j ≤ Rwidth ∧ σmin ≤ D.σ j ∧ D.σ j ≤ σmax) →
    (∀ label, (bufferedProductFamily M H hH η₀
      (excluded D.natural.character D.puncture) label).modulus.absNorm ≤ Z^d) →
    (∀ j, 2*(|Real.log (A j)|+|Real.log (B j)|)+1 ≤ Real.log ((Z^d)^(D.r j))) →
    (D.rebin i).Admissible M H hH η₀ A B Rwidth τ ηaux σmin σmax
      Z d (3*(i+1 : ℕ)*Z^τ) := by
  filter_upwards [twoStageFrequency_uniform τ ν hgap,
    uniform_height_budget dmin τ ηaux I hτ.le hηaux hheight,
    eventually_ge_atTop (1 : ℝ)] with Z hfreq hbudget hZ
  intro d hd i hi D t v₁ v₂ w₁ θ₁ w₂ θ₂ v ht hv₁ hv₂ hv hw₁ hθ₁ hw₂ hθ₂
    hplain₁ hplain₂ hslots hr₁ hr₁' hr₂ hr₂' hrs hcond hlog
  have hT : 0 ≤ Z^τ := Real.rpow_nonneg (by linarith) _
  have hiR : (2 : ℝ) ≤ (3*i+2 : ℕ) := by exact_mod_cast (show 2 ≤ 3*i+2 by omega)
  have hgate (x : ℝ) (hx : |x| ≤ Z^τ) : |x|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
    nlinarith [mul_le_mul_of_nonneg_right hiR hT]
  have hfour := hbudget d hd i hi
  refine ⟨hr₁,hr₁',hr₂,hr₂',hrs,hcond,?_,?_,?_,hfour,?_,hlog,le_rfl⟩
  · change |D.plain₁.freq|+Z^τ/2 ≤ _
    rw [hplain₁]
    exact hgate _ (hfreq t v₁ w₁ θ₁ w₂ θ₂ ht hv₁ hw₁ hθ₁ hw₂ hθ₂)
  · change |D.plain₂.freq|+Z^τ/2 ≤ _
    rw [hplain₂]
    exact hgate _ (hfreq t v₂ w₁ θ₁ w₂ θ₂ ht hv₂ hw₁ hθ₁ hw₂ hθ₂)
  · intro j
    change |D.t+D.v j|+Z^τ/2 ≤ _
    rw [hslots]
    exact hgate _ (hfreq t (v j) w₁ θ₁ w₂ θ₂ ht (hv j) hw₁ hθ₁ hw₂ hθ₂)
  · have hbase : 1 ≤ 3+(3*i+2 : ℕ)*Z^τ := by
      have hh : 0 ≤ (3*i+2 : ℕ)*Z^τ := mul_nonneg (Nat.cast_nonneg _) hT
      linarith
    exact (pow_le_pow_right₀ hbase (by omega : 2 ≤ 4)).trans hfour

end JointBufferedProductData

/-- Halving the mesh supplies a strict upper edge for the existing product
API, uniformly over every row in the complete dictionary. -/
theorem exists_strict_buffered_bins {Row Label : Type*} [Fintype Label]
    (χ : Row → Label → Character) (hχ : ∀ u j, (χ u j).residue ≠ 1)
    (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (I : ℕ) (hI : 0 < I) (hwidth : (49/100 : ℝ) ≤ I*(e/2)) :
    ∃ bin : Row → Fin (I+1) × Fin (I+1), ∀ u,
      1 ≤ (bin u).1.val ∧
      let a : ℝ := 51/100+(e/2)*((bin u).2.val : ℝ)
      a ≤ zeroMaximum (χ u) (hχ u) ((3*((bin u).1.val+1) : ℕ)*T) ∧
      zeroMaximum (χ u) (hχ u) ((3*((bin u).1.val+1) : ℕ)*T) < a+e ∧
      a+e < a+2*e := by
  obtain ⟨bin,hbin⟩ := exists_bounded_buffered_bins χ hχ T (e/2) hT
    (by positivity) I hI hwidth
  refine ⟨bin,?_⟩
  intro u
  obtain ⟨hi,ha,hlo,hmid,hhi⟩ := hbin u
  refine ⟨hi,?_,?_,by linarith⟩
  · apply hlo.trans (zeroMaximum_mono _ _ ?_)
    have hcast : ((3*(bin u).1.val : ℕ) : ℝ) ≤ (3*((bin u).1.val+1) : ℕ) := by
      exact_mod_cast (show 3*(bin u).1.val ≤ 3*((bin u).1.val+1) by omega)
    exact mul_le_mul_of_nonneg_right hcast (by linarith)
  · convert hhi using 1
    ring


/-- One bin choice for the fixed joint moment dictionary works for every
literal puncture/mask family. Thus punctures are never counted again. -/
theorem exists_joint_source_buffered_bins {Row SlotLabel : Type*} [Fintype SlotLabel]
    (η : Character) (ν : SlotLabel → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQν : ∀ j, Q ≤ (ν j).modulus)
    (w : Row → NonzeroElement)
    (hex : ∀ u, ¬FixedInducingRow η Q fixedBadMask 1 (w u).val)
    (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (I : ℕ) (hI : 0 < I) (hwidth : (49/100 : ℝ) ≤ I*(e/2))
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ bin : Row → Fin (I+1) × Fin (I+1), ∀ u,
      1 ≤ (bin u).1.val ∧
      let a : ℝ := 51/100+(e/2)*((bin u).2.val : ℝ)
      a ≤ 7/8 ∧ ∀ (R : JointRelativeLabel η SlotLabel → Ideal O)
        (hR : ∀ label, R label ≠ 0),
        jointRelativeSourceZeroBin η ν Q hQ72 hQν R hR a (a+e)
          ((3*((bin u).1.val+1) : ℕ)*T) (w u) := by
  let χ := fun u label => (momentData (jointRelativeParent η ν label)).character (w u)
  have hn := fun u => jointRelativeMoment_nonprincipal η ν Q hQ72 hQν (w u) (hex u)
  obtain ⟨bin,hbin⟩ := exists_strict_buffered_bins χ hn T e hT he I hI hwidth
  refine ⟨bin,?_⟩
  intro u
  obtain ⟨hi,hlo,hhi,hgap⟩ := hbin u
  refine ⟨hi,?_,?_⟩
  · exact hlo.trans (zeroMaximum_le_seven_eighths (χ u) (hn u) _ hβupper)
  · intro R hR
    refine ⟨hex u,?_,?_⟩ <;>
      rw [jointRelativeSource_zeroMaximum η ν Q hQ72 hQν (w u) (hex u) R hR]
    · exact hlo
    · exact hhi.le

/-- The density polynomial is paid only after its degree has been fixed. -/
theorem buffered_density_height_bound (Z τ loss : ℝ) (J I i : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hi : i ≤ I) (hloss : τ*(J : ℝ) ≤ loss) :
    (1+|3*(i+1 : ℕ)*Z^τ|)^J ≤ (1+3*(I+1 : ℕ))^J*Z^loss := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hT : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ
  have hcoef : ((3*(i+1) : ℕ) : ℝ) ≤ (3*(I+1) : ℕ) := by
    exact_mod_cast (show 3*(i+1) ≤ 3*(I+1) by omega)
  have hbase : 1+|3*(i+1 : ℕ)*Z^τ| ≤ (1+3*(I+1 : ℕ))*Z^τ := by
    rw [abs_of_nonneg (by positivity)]
    push_cast at hcoef ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ Z^τ)]
  calc
    _ ≤ ((1+3*(I+1 : ℕ))*Z^τ)^J := pow_le_pow_left₀ (by positivity) hbase J
    _ = (1+3*(I+1 : ℕ))^J*Z^(τ*(J : ℝ)) := by
      rw [mul_pow, Real.rpow_mul hZpos.le, Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hloss) (by positivity)

/-- A fixed extra height degree absorbs any polynomial scale loss outside
the small input-height strip. The bound premise is the elementary source
bound, not the proposed joint local moment estimate. -/
theorem large_input_height_polynomial (ν B target : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∀ (Z t C : ℝ) (J : ℕ) (x : ℂ),
      1 ≤ Z → 0 ≤ C → Z^ν < |t| →
      ‖x‖ ≤ C*Z^B*(1+|t|)^J →
      ‖x‖ ≤ C*Z^target*(1+|t|)^(J+N) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((B-target)/ν)
  have hbudget : B ≤ target+ν*(N : ℝ) := by
    have hh := (div_lt_iff₀ hν).mp hN
    nlinarith
  refine ⟨N,?_⟩
  intro Z t C J x hZ hC ht hx
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hbase : Z^ν ≤ 1+|t| := by linarith
  have hpower : Z^B ≤ Z^target*(1+|t|)^N := by
    calc
      _ ≤ Z^(target+ν*(N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hbudget
      _ = Z^target*(Z^ν)^N := by
        rw [Real.rpow_add hZpos, Real.rpow_mul hZpos.le, Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase N) (by positivity)
  apply hx.trans
  calc
    C*Z^B*(1+|t|)^J ≤ C*(Z^target*(1+|t|)^N)*(1+|t|)^J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hC) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- A literal canonical prime slot at bounded scale has one constant uniform
in every row, character, input height and Fourier shift. -/
theorem normalized_prime_slot_bounded_scale
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W : ℝ → ℂ) (a b lo hi P₀ : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : Continuous W) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (η ν : Character) (m A z : O) (P σ v t : ℝ),
      1 ≤ P → P ≤ P₀ → lo ≤ σ → σ ≤ hi →
      ‖normalizedSlot η m A z (primePool M H b P)
        (fun I => idealCoeff ν I*annularWeight W P σ v I) t P‖ ≤ C := by
  obtain ⟨K,hK,hbound⟩ := CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    W a b lo hi ha hWs hW
  let C : ℝ := max 1 (128*K*(max 1 b*max 1 P₀))
  refine ⟨C,le_max_left _ _,?_⟩
  intro η ν m A z P σ v t hP hP₀ hσlo hσhi
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hs (I : Ideal O) (hI : I ∈ primePool M H b P) : I ≠ 0 :=
    (Finset.mem_filter.mp hI).2.1.ne_zero
  have hcoeff (I : Ideal O) (hI : I ∈ primePool M H b P) :
      ‖idealCoeff ν I*annularWeight W P σ v I‖ ≤ K := by
    have hh := (hbound ν P σ v 0 hPpos hσlo hσhi I (hs I hI)).1
    simpa [CenteredMomentCommonMaskEnergy.heightCoefficient] using hh
  have hnorm (I : Ideal O) (hI : I ∈ primePool M H b P)
      (hn : idealCoeff ν I*annularWeight W P σ v I ≠ 0) :
      (I.absNorm : ℝ) ≤ max 1 b*max 1 P₀ := by
    have hh := (hbound ν P σ v 0 hPpos hσlo hσhi I (hs I hI)).2
    have hIP : (I.absNorm : ℝ) ≤ b*P :=
      hh (by simpa [CenteredMomentCommonMaskEnergy.heightCoefficient] using hn)
    apply hIP.trans
    apply (mul_le_mul_of_nonneg_right (le_max_right 1 b) hPpos.le).trans
    exact mul_le_mul_of_nonneg_left (hP₀.trans (le_max_right 1 P₀))
      (zero_le_one.trans (le_max_left _ _))
  have hr := rowSlot_bound η m A z (primePool M H b P)
    (fun I => idealCoeff ν I*annularWeight W P σ v I) t
    (max 1 b*max 1 P₀) K (by positivity) hK.le hcoeff hnorm
  have hinv : (Real.sqrt P)⁻¹ ≤ 1 := by
    have hsqrt : 1 ≤ Real.sqrt P := (Real.one_le_sqrt).mpr hP
    exact inv_le_one_of_one_le₀ hsqrt
  rw [normalizedSlot,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg P)]
  apply le_trans _ (le_max_right _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) hinv).trans hr

/-- The large-slot set is a subset of the original fixed system. Its complement
has a fixed scale cap, even if the original logarithmic width is zero. -/
def largePrimeSlots {Slot : Type*} [Fintype Slot] (A B P : Slot → ℝ) : Finset Slot :=
  Finset.univ.filter (fun j => 2*(|Real.log (A j)|+|Real.log (B j)|)+1 ≤ Real.log (P j))

lemma largePrimeSlots_log_scale {Slot : Type*} [Fintype Slot] (A B P : Slot → ℝ)
    (j : Slot) (hj : j ∈ largePrimeSlots A B P) :
    2*(|Real.log (A j)|+|Real.log (B j)|)+1 ≤ Real.log (P j) :=
  (Finset.mem_filter.mp hj).2

lemma smallPrimeSlots_scale_cap {Slot : Type*} [Fintype Slot] (A B P : Slot → ℝ)
    (j : Slot) (hP : 0 < P j) (hj : j ∉ largePrimeSlots A B P) :
    P j ≤ Real.exp (2*(|Real.log (A j)|+|Real.log (B j)|)+1) := by
  have hlog : Real.log (P j) < 2*(|Real.log (A j)|+|Real.log (B j)|)+1 := by
    simpa [largePrimeSlots] using hj
  rw [← Real.exp_log hP]
  exact Real.exp_le_exp.mpr hlog.le


lemma prod_norm_remove_bounded {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (S T : Finset Slot) (hTS : T ⊆ S) (x : Slot → ℂ) (C : Slot → ℝ)
    (hC : ∀ j, 1 ≤ C j) (hsmall : ∀ j ∈ S \ T, ‖x j‖ ≤ C j) :
    ‖∏ j ∈ S, x j‖ ≤ (∏ j, C j)*‖∏ j ∈ T, x j‖ := by
  have hmass : (∏ j ∈ S \ T, C j) ≤ ∏ j, C j := by
    have hone : 1 ≤ ∏ j ∈ Finset.univ \ (S \ T), C j :=
      Finset.one_le_prod₀ (fun j _ => hC j)
    calc
      _ ≤ (∏ j ∈ Finset.univ \ (S \ T), C j)*(∏ j ∈ S \ T, C j) :=
        le_mul_of_one_le_left (Finset.prod_nonneg (fun j _ => zero_le_one.trans (hC j))) hone
      _ = _ := Finset.prod_sdiff (Finset.subset_univ _)
  rw [← Finset.prod_sdiff hTS, norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hsmall).trans hmass

/-- Small prime slots may be removed from any surviving subset with a single
constant fixed on the original slot system. -/
theorem normalized_prime_slots_remove_small {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W : Slot → ℝ → ℂ) (A B : Slot → ℝ) (lo hi : ℝ)
    (hA : ∀ j, 0 < A j) (hWs : ∀ j, Function.support (W j) ⊆ Icc (A j) (B j))
    (hW : ∀ j, Continuous (W j)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset Slot) (η : Character) (ν : Slot → Character)
      (m Arow z : O) (P σ v : Slot → ℝ) (t : ℝ),
      (∀ j ∈ S, 1 ≤ P j) → (∀ j ∈ S, lo ≤ σ j ∧ σ j ≤ hi) →
      let x := fun j => normalizedSlot η m Arow z (primePool M H (B j) (P j))
        (fun I => idealCoeff (ν j) I*annularWeight (W j) (P j) (σ j) (v j) I) t (P j)
      ‖∏ j ∈ S, x j‖ ≤ C*‖∏ j ∈ S ∩ largePrimeSlots A B P, x j‖ := by
  have hb (j : Slot) := normalized_prime_slot_bounded_scale M H (W j) (A j) (B j) lo hi
    (Real.exp (2*(|Real.log (A j)|+|Real.log (B j)|)+1)) (hA j) (hWs j) (hW j)
  choose C hC hbound using hb
  refine ⟨∏ j, C j,Finset.one_le_prod₀ (fun j _ => hC j),?_⟩
  intro S η ν m Arow z P σ v t hP hσ
  dsimp only
  apply prod_norm_remove_bounded S (S ∩ largePrimeSlots A B P) Finset.inter_subset_left _ C hC
  intro j hj
  have hjS : j ∈ S := (Finset.mem_sdiff.mp hj).1
  have hjlarge : j ∉ largePrimeSlots A B P := by
    intro hmem
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mpr ⟨hjS,hmem⟩)
  exact hbound j η (ν j) m Arow z (P j) (σ j) (v j) t (hP j hjS)
    (smallPrimeSlots_scale_cap A B P j (zero_lt_one.trans_le (hP j hjS)) hjlarge)
    (hσ j hjS).1 (hσ j hjS).2

#print axioms normalized_prime_slots_remove_small
#print axioms normalized_prime_slot_bounded_scale
#print axioms JointBufferedProductData.admissible_rebin_of_two_stage
#print axioms exists_strict_buffered_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedHeight -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonFiberMass ; sha256 a57690ca9766e0f4e16d518a8dcb6294cb4ece468293cd9bfc595547b8886b17 -/
section




/-! The common-allocation fiber mass at the actual physical column
normalization. The source lower-dyad gate pays its volume ratio exactly. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair CenteredMomentCommonRawCost
open CanonicalQuadraticSieve CompletedGauss CenteredMomentCanonicalFirst
open CenteredMomentSourceBlockWindows CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonSourceProfile (s : Input ι) : ℝ :=
  (∏ i,s.M i)^2*(max 1 s.upper)^Fintype.card ι

lemma commonSourceProfile_nonneg (s : Input ι) : 0 ≤ commonSourceProfile s := by
  unfold commonSourceProfile
  positivity

lemma secondCommonVolume_identity (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) :
    secondCommonVolume s C B*rawReduction B.val s.P = volume s.toData := by
  change volume (commonData s C R B)*rawReduction B.val s.P = _
  rw [common_volume]
  exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

lemma secondCommonWeightAt_sq (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (H : ℝ) (hH : 0 < H) :
    ‖secondCommonWeightAt s C R B H‖^2 =
      (volume s.toData/H)*‖commonScalar s C R B‖^2 := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hv := secondCommonVolume_pos s C B
  have hiden := secondCommonVolume_identity s C R B
  rw [commonScalar_sq]
  simp only [secondCommonWeightAt,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),mul_pow,div_pow,
    Real.sq_sqrt hv.le,Real.sq_sqrt hH.le]
  field_simp
  nlinarith

theorem secondCommonWeightAt_sq_bound (s : Input ι) (C R : Ideal O) (hC : C ≠ 0)
    (B : actualAllocations s.pools C) (a H : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hlower : a*volume s.toData/(C.absNorm : ℝ) ≤ H) :
    ‖secondCommonWeightAt s C R B H‖^2 ≤ commonSourceProfile s/a := by
  have hNC : (0 : ℝ) < C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hv := volume_pos s.toData
  have hprofile := commonSourceProfile_nonneg s
  rw [secondCommonWeightAt_sq s C R B H hH]
  apply (mul_le_mul_of_nonneg_left (commonScalar_sq_bound s C R hC B) (div_nonneg hv.le hH.le)).trans
  change (volume s.toData/H)*(commonSourceProfile s/(C.absNorm : ℝ)) ≤ _
  have hratio : volume s.toData/(H*(C.absNorm : ℝ)) ≤ 1/a := by
    apply (div_le_div_iff₀ (mul_pos hH hNC) ha).mpr
    have hh := (div_le_iff₀ hNC).mp hlower
    nlinarith
  calc
    _ = commonSourceProfile s*(volume s.toData/(H*(C.absNorm : ℝ))) := by ring
    _ ≤ commonSourceProfile s*(1/a) := mul_le_mul_of_nonneg_left hratio hprofile
    _ = _ := by ring

theorem secondCommonWeightAt_norm_bound (s : Input ι) (C R : Ideal O) (hC : C ≠ 0)
    (B : actualAllocations s.pools C) (a H : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hlower : a*volume s.toData/(C.absNorm : ℝ) ≤ H) :
    ‖secondCommonWeightAt s C R B H‖ ≤ Real.sqrt (commonSourceProfile s/a) := by
  have hh := secondCommonWeightAt_sq_bound s C R hC B a H ha hH hlower
  have hs := Real.sq_sqrt (div_nonneg (commonSourceProfile_nonneg s) ha.le)
  nlinarith [norm_nonneg (secondCommonWeightAt s C R B H),Real.sqrt_nonneg (commonSourceProfile s/a)]

theorem actual_common_fiber_mass (Bcap ε : ℝ) (hBcap : 0 ≤ Bcap) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ (Z : ℝ),1 ≤ Z →
      ∀ (s : Input ι) (C R : Ideal O),C ≠ 0 → (C.absNorm : ℝ) ≤ Z^Bcap →
      ∀ (a H : ℝ),0 < a → 0 < H → a*volume s.toData/(C.absNorm : ℝ) ≤ H →
      (∑ B : actualAllocations s.pools C,‖secondCommonWeightAt s C R B H‖) ≤
        K*Z^ε*Real.sqrt (commonSourceProfile s/a) := by
  obtain ⟨K,hK,hcard⟩ := actualAllocations_small_power (ι := ι ⊕ Fin 2)
    (ε/(Bcap+1)) (div_pos hε (by linarith))
  refine ⟨K,hK,?_⟩
  intro Z hZ s C R hC hCcap a H ha hH hlower
  have hpow : (C.absNorm : ℝ)^(ε/(Bcap+1)) ≤ Z^ε := by
    calc
      _ ≤ (Z^Bcap)^(ε/(Bcap+1)) := Real.rpow_le_rpow (Nat.cast_nonneg _) hCcap (by positivity)
      _ = Z^(Bcap*(ε/(Bcap+1))) := (Real.rpow_mul (by linarith : 0 ≤ Z) _ _).symm
      _ ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ (by
        have ht : Bcap*(ε/(Bcap+1)) ≤ ε := by
          rw [←mul_div_assoc]
          apply (div_le_iff₀ (by linarith : 0 < Bcap+1)).mpr
          nlinarith
        exact ht)
  calc
    _ ≤ ∑ B : actualAllocations s.pools C,Real.sqrt (commonSourceProfile s/a) :=
      Finset.sum_le_sum (fun B _ => secondCommonWeightAt_norm_bound s C R hC B a H ha hH hlower)
    _ = ((actualAllocations s.pools C).card : ℝ)*Real.sqrt (commonSourceProfile s/a) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ ≤ (K*(C.absNorm : ℝ)^(ε/(Bcap+1)))*Real.sqrt (commonSourceProfile s/a) :=
      mul_le_mul_of_nonneg_right (hcard s.pools C hC) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK.le) (Real.sqrt_nonneg _)

/-- The physical lower-column window supplies the required normalization
for both actual second common ideals C0*C and C0*D. -/
theorem actual_common_physical_fiber_mass (Bcap ε : ℝ) (hBcap : 0 ≤ Bcap) (hε : 0 < ε) :
    ∃ Kbound : ℝ,0 < Kbound ∧ ∀ (Z : ℝ),1 ≤ Z →
    ∀ (s : Input ι) (C0 Rmask : Ideal O),C0 ≠ 0 →
    ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D)
      (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
      (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) (a : ℝ),
    0 < a → (∀ I : Ideal O,β I ≠ 0 → a*(volume s.toData/(C0.absNorm : ℝ)) ≤ (I.absNorm : ℝ)) →
    physicalBlock η t S β C D hC hD U R rows W K n ≠ 0 →
    ((C0*C).absNorm : ℝ) ≤ Z^Bcap → ((C0*D).absNorm : ℝ) ≤ Z^Bcap →
    (∑ B : actualAllocations s.pools (C0*C),
      ‖secondCommonWeightAt s (C0*C) Rmask B (dyadicScale (n 2))‖) ≤
      Kbound*Z^ε*Real.sqrt (commonSourceProfile s/a) ∧
    (∑ B : actualAllocations s.pools (C0*D),
      ‖secondCommonWeightAt s (C0*D) Rmask B (dyadicScale (n 3))‖) ≤
      Kbound*Z^ε*Real.sqrt (commonSourceProfile s/a) := by
  obtain ⟨Kbound,hKbound,hbound⟩ := actual_common_fiber_mass (ι := ι) Bcap ε hBcap hε
  refine ⟨Kbound,hKbound,?_⟩
  intro Z hZ s C0 Rmask hC0 η t S β C D hC hD U R rows W K n a ha hlower hne hc hd
  have hwin := physicalBlock_scale_lower η t S β C D hC hD U R rows W K n
    a (volume s.toData/(C0.absNorm : ℝ)) ha hlower hne
  have hleft : a*volume s.toData/((C0*C).absNorm : ℝ) ≤ dyadicScale (n 2) := by
    have hh := (le_div_iff₀ ha).mp hwin.1
    convert hh using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp
    <;> ring
  have hright : a*volume s.toData/((C0*D).absNorm : ℝ) ≤ dyadicScale (n 3) := by
    have hh := (le_div_iff₀ ha).mp hwin.2
    convert hh using 1
    simp only [map_mul,Nat.cast_mul]
    field_simp
    <;> ring
  exact ⟨hbound Z hZ s (C0*C) Rmask (mul_ne_zero hC0 hC.1) hc a _ ha
    (dyadicScale_pos _) hleft,
    hbound Z hZ s (C0*D) Rmask (mul_ne_zero hC0 hD.1) hd a _ ha
    (dyadicScale_pos _) hright⟩

#print axioms actual_common_physical_fiber_mass
#print axioms secondCommonWeightAt_sq
#print axioms actual_common_fiber_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonFiberMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalAllocated ; sha256 d5fc5619c7c17fbe67b7e335ccc0f9fb604af95625e10708533267f665797858 -/
section



/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalAllocatedDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalAllocatedDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFirstAllocationGaussEnergy

/-- The literal first-allocation mass pays all frozen and surviving slot
controls. No number of first labels enters this estimate. -/
theorem allocated_exceptional_control (N : ℕ) (b ε : ℝ) (hb : 1 ≤ b) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
    ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (C R : Ideal O), C ≠ 0 → ∀ (τ : Character) (t L : ℝ), 0 ≤ L →
    ∀ energy : actualAllocations s.pools C → ℝ,
    (∀ B, frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
      energy B ≤ L*mass (child s C R B τ t)^2) →
    ((max 1 b)^N*((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ)) *
      (∑ B : actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
          (frozenControl B.val s.M)^2*energy B else 0) ≤
      D*(C.absNorm : ℝ)^(ε-1)*mass s^2*L := by
  obtain ⟨D,hD,halloc⟩ := allocated_control_mass N ε hε
  refine ⟨b^N*D,mul_pos (pow_pos (zero_lt_one.trans_le hb) _) hD,?_⟩
  intro ι _ hn s C R hC τ t L hL energy he
  have hsum : (∑ B : actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
        (frozenControl B.val s.M)^2*energy B else 0) ≤
      L*∑ B : actualAllocations s.pools C,
        (frozenControl B.val s.M)^2*mass (child s C R B τ t)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B _
    split_ifs with hne
    · convert mul_le_mul_of_nonneg_left (he B hne) (sq_nonneg (frozenControl B.val s.M)) using 1 <;> ring
    · positivity
  have ha := halloc hn s C R hC τ t
  change ((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ)*
      (∑ B : actualAllocations s.pools C, (frozenControl B.val s.M)^2*mass (child s C R B τ t)^2) ≤
      D*(C.absNorm : ℝ)^(ε-1)*mass s^2 at ha
  rw [max_eq_right hb]
  calc
    _ ≤ (b^N*((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ))*
        (L*∑ B : actualAllocations s.pools C,
          (frozenControl B.val s.M)^2*mass (child s C R B τ t)^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (b^N*L)*(((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ)*
        ∑ B : actualAllocations s.pools C,
          (frozenControl B.val s.M)^2*mass (child s C R B τ t)^2) := by ring
    _ ≤ (b^N*L)*(D*(C.absNorm : ℝ)^(ε-1)*mass s^2) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hL)
    _ = _ := by ring

/-- The exceptional portion of the actual first common-allocation sum,
with its physical child volume and the prime amplification scale. -/
def allocatedMainExceptionalEnergy {Slot : Type*} [Fintype Slot]
    (s : Input Slot) (C Rmask seed : Ideal O) (τ : Character) (t b Z : ℝ)
    (Q : Ideal O) (ray : RayCharacter) (m : O) (Rmain Tsec ξ : ℝ) : ℝ :=
  ((max 1 b)^(Fintype.card Slot)*((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ)) *
    ∑ B : actualAllocations s.pools C,
      if frozenCoefficient B.val C Rmask s.ν s.W s.P ≠ 0 then
        let d := child s C Rmask B τ t
        (frozenControl B.val s.M)^2*
          (‖partEnergy true τ ray Q m t (finiteColumns (Fintype.piFinset d.pools))
            (coefficient d (Rmask*C) seed) ballProfile Rmain Tsec Z ξ (sourceRadius d)‖ /
            (CenteredMomentAmplificationChildInput.volume d*Z^(3/500 : ℝ))) else 0

theorem actual_local_main_exceptional_allocated
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (b : ℝ) (hb : 1 ≤ b) (ε δ θ Bcap εalloc : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hBcap : 0 ≤ Bcap) (hεalloc : 0 < εalloc) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Cfixed : ℝ, 0 < Cfixed ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
      ∀ (η τ : Character) (C D E : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C = primeSupport D →
      ∀ U : Finset (CommonIndex C D),
      E = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U} →
      ∀ (K omega M : ℝ), 0 < K →
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D} →
      ∀ (Rmask seed : Ideal O) (t : ℝ),
      s.upper ≤ b →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      Rmask ≠ 0 → Squarefree seed → seed ≠ 0 →
      let V := CenteredMomentAmplificationChildInput.volume s
      let Rmain := mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D E K V Z) (Real.logb Z (C.absNorm : ℝ)) (9/500) omega 0
      (∀ B : actualAllocations s.pools (commonPart C D),
        frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0 →
        let d := child s (commonPart C D) Rmask B τ t
        (∀ i, 1 ≤ d.P i) ∧ 0 ≤ sourceRadius d ∧ sourceRadius d ≤ Z^Bcap) →
      (τ.modulus.absNorm : ℝ) ≤ Z^Bcap → ((Rmask*commonPart C D).absNorm : ℝ) ≤ Z^Bcap →
      ∀ (ray : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
      ∀ Tsec ξ : ℝ, 0 < frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ ≤ Z^Bcap →
      allocatedMainExceptionalEnergy s (commonPart C D) Rmask seed τ t b Z Q ray m Rmain Tsec ξ ≤
        Cfixed*p.control S^2*(1+‖t‖)^(2*J)*mass s^6*
          (C.absNorm : ℝ)^(εalloc-1)*
          ((τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z))*
          Z^(2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6)/(seed.absNorm : ℝ) := by
  obtain ⟨J,S,hS,hsource⟩ := actual_local_main_exceptional_child_uniform
    wlo whi hwlo hwhi lo hi b hb ε δ θ Bcap hε hδ hθ hBcap
  obtain ⟨Dalloc,hDalloc,halloc⟩ := allocated_exceptional_control (Fintype.card Slot) b εalloc hb hεalloc
  refine ⟨J,S,hS,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Cfixed,hCfixed,hsource⟩ := hsource Q hQ hQt hQ72
  refine ⟨Dalloc*Cfixed,mul_pos hDalloc hCfixed,?_⟩
  filter_upwards [hsource] with Z hsource
  refine ⟨hsource.1,?_⟩
  intro s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
    Rmask seed t hupper hM hwidth hvolume hX₁ hX₂ hY₁ hY₂
    hRmask hseed hseed0 V Rmain hcaps hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
  have hZ : 0 < Z := zero_lt_one.trans hsource.1
  have hq : 0 < (τ.modulus.absNorm : ℝ) := norm_pos _ τ.modulus_ne_bot
  have hNC : 0 < (C.absNorm : ℝ) := norm_pos _ hC.1
  have hV : 0 < V := CenteredMomentAmplificationChildInput.volume_pos s
  let ref := (τ.modulus.absNorm : ℝ)*(V/(C.absNorm : ℝ))*Z^(allowance C D Z)
  have href : 0 < ref := by dsimp [ref]; positivity
  let L := Cfixed*p.control S^2*(1+‖t‖)^(2*J)*mass s^4*
      Z^(2*ε+2*δ+2*(5*Bcap+1)*θ-93/1000+5*omega/6)/(seed.absNorm : ℝ)*ref
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let energy := fun B : actualAllocations s.pools (commonPart C D) =>
    let d := child s (commonPart C D) Rmask B τ t
    ‖partEnergy true τ ray Q m t (finiteColumns (Fintype.piFinset d.pools))
      (coefficient d (Rmask*commonPart C D) seed) ballProfile Rmain Tsec Z ξ (sourceRadius d)‖ /
      (CenteredMomentAmplificationChildInput.volume d*Z^(3/500 : ℝ))
  have he (B : actualAllocations s.pools (commonPart C D))
      (hne : frozenCoefficient B.val (commonPart C D) Rmask s.ν s.W s.P ≠ 0) :
      energy B ≤ L*mass (child s (commonPart C D) Rmask B τ t)^2 := by
    obtain ⟨hP,hH0,hH⟩ := hcaps B hne
    have hh := hsource.2 s p hlo hhi hW₁ hW₂ η τ C D E hC hD hCD U hE K omega M hK hmod
      Rmask seed B t hupper hne hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ hRmask hseed hseed0
      hP hH0 hH hτ hRnorm ray m hm hml hm2 Tsec ξ hfreq hfreqcap
    rw [← div_div] at hh
    change energy B/ref ≤ _ at hh
    have hh' := (div_le_iff₀ href).mp hh
    convert hh' using 1 <;> simp only [L] <;> ring
  have ha := halloc le_rfl s (commonPart C D) Rmask (commonPart_ne_zero C D) τ t L hL energy he
  change allocatedMainExceptionalEnergy s (commonPart C D) Rmask seed τ t b Z Q ray m Rmain Tsec ξ ≤ _ at ha
  apply ha.trans_eq
  rw [commonPart_of_equal_support C D hC.1 hCD]
  dsimp only [L,ref]
  ring

#print axioms actual_local_main_exceptional_allocated
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalAllocated -/
