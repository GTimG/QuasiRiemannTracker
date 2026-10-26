/- Copyright (c) 2026 Sil. Apache-2.0.
Identify the inherited extracted live profile with the already bounded
centered natural row. Use its actual finite pools, without imposing a
new vanishing condition outside them. A nonzero common puncture need
not be squarefree: its radical gives exactly the same character.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedCenteredEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedLiveRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open IdealMobiusDivisorSum (support_prime)
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles KernelRowExpansion
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation
open MixedTupleRows MixedCompletedRows MixedCenteredEnergy
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation
open CenteredMomentCommonProfile CenteredMomentRemainingBox CenteredMomentSourceRectangle
open CenteredMomentFirstSectors CenteredMomentNaturalPrimitive
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem radical_character_mask (χ : Character) (R : Id) (hR : R≠0) (I : Id) :
    (if IsCoprime I R then (1:ℂ) else 0)*idealCoeff χ I=
      idealCoeff (χ.excludePrimes (primeSupport R) (fun _ h=>support_prime h)) I := by
  rw [idealCoeff_excludePrimes,coprime_support_iff I R hR]
  split_ifs <;> simp only [one_mul,zero_mul]

/-- Centralization on the original pools. Missing marked primes are
removed by slotWeight only after this equality, before taking norms. -/
theorem punctured_pool_profile (χ : Character) (S H : Finset PrimeIdeal)
    (R : Id) (hR : R≠0) (pool : ι→Finset Id) (hpool : ∀i,pool i⊆primeValues S)
    (A B : Finset Id) (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id) :
    ((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹)*
      (∑v∈Fintype.piFinset (pools pool A B),tupleWeight (punctureProduct S H) v*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v*
        idealCoeff χ (finiteTupleProduct v))=
      ∑v∈Fintype.piFinset (pools (fun _ : ι=>primeValues S) A B),
        tupleWeight (punctureProduct S H) v*
          centeredCoefficient pool (fun i I=>ν i I*Wslot i (I.absNorm/P i)) P
            W₁ W₂ X₁ X₂ Y₁ Y₂ d v*
          idealCoeff (χ.excludePrimes (primeSupport R) (fun _ h=>support_prime h))
            (finiteTupleProduct v) := by
  rw [←centered_pool_completion _ S H pool hpool A B]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have he := profile_centralization pool ν Wslot P R W₁ W₂ X₁ X₂ Y₁ Y₂ d v
    (fun i hi=>False.elim (hi (Fintype.mem_piFinset.mp hv (Sum.inl i))))
  rw [←radical_character_mask χ R hR]
  calc
    _ = tupleWeight (punctureProduct S H) v*
        (((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹)*
          profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v)*
        idealCoeff χ (finiteTupleProduct v) := by ring
    _ = _ := by rw [he];ring

theorem live_box (T : (ι⊕Fin 2)→Finset Id) (B : Tuple ι) (hB : ∀j,B j≠0) :
    liveBox T B hB=Fintype.piFinset (pools (fun i : liveIndices B=>T (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (T (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (T (Sum.inr 1)))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]
  unfold tuplePool
  ext v
  simp only [Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i=>exact h (Sum.inl i)
    | inr j=>fin_cases j;exact h (Sum.inr 0);exact h (Sum.inr 1)

theorem residual_pool_twice (d e : Id) (hd : d≠0) (he : e≠0) (A : Finset Id) :
    residualPool e he (residualPool d hd A)=residualPool (d*e) (mul_ne_zero hd he) A := by
  ext I
  simp only [mem_residualPool,mul_assoc]

/-- The ordinary source already has its original prefixes extracted.
A later live allocation multiplies those prefixes, rather than dropping
or duplicating them; the marked live pools are literally unchanged. -/
theorem source_live_box (pool : ι→Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (A₁ A₂ : Finset Id) (B : Tuple ι) (hB : ∀j,B j≠0) :
    liveBox (pools pool (residualPool d.1 hd.1 A₁) (residualPool d.2 hd.2 A₂)) B hB=
      Fintype.piFinset (pools (fun i : liveIndices B=>pool i.val)
        (residualPool (d.1*B (Sum.inr 0)) (mul_ne_zero hd.1 (hB _)) A₁)
        (residualPool (d.2*B (Sum.inr 1)) (mul_ne_zero hd.2 (hB _)) A₂)) := by
  rw [live_box]
  simp only [pools,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [residual_pool_twice]

/-- Full equality for the actual inherited live profile. All finite
domain and support premises are geometric; no child energy is assumed. -/
theorem source_live_profile (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι→Finset Id) (hpool : ∀i,pool i⊆primeValues S)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (B : Tuple ι) (hB : ∀j,B j≠0)
    (F R : Id) (hF : F≠0) (hR : R≠0)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0)
    (hS : ∀I,Supported I→
      (((I.absNorm:ℝ)≤b*(X₁/(d.1*B (Sum.inr 0)).absNorm) ∨
        (I.absNorm:ℝ)≤b*(X₂/(d.2*B (Sum.inr 1)).absNorm)) ∨
       ((I.absNorm:ℝ)≤b*(Y₁/(d.1*B (Sum.inr 0)).absNorm) ∨
        (I.absNorm:ℝ)≤b*(Y₂/(d.2*B (Sum.inr 1)).absNorm)))→primeSupport I⊆primeValues S) :
    ((Real.sqrt (X₁*X₂):ℂ)⁻¹*∏i : liveIndices B,(Real.sqrt (P i.val):ℂ)⁻¹)*
      (∑v∈liveBox (pools pool
          (residualPool d.1 hd.1 (plainSupportPool b X₁ Y₁))
          (residualPool d.2 hd.2 (plainSupportPool b X₂ Y₂))) B hB,
        tupleWeight (punctureProduct S H) v*
          liveProfile B F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v*
          idealCoeff χ (finiteTupleProduct v))=
      centeredRow (χ.excludePrimes (primeSupport (R*F)) (fun _ h=>support_prime h)) S H
        (fun i : liveIndices B=>pool i.val)
        (fun i I=>ν i.val I*Wslot i.val (I.absNorm/P i.val)) (fun i=>P i.val)
        W₁ W₂ b X₁ X₂ Y₁ Y₂ (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
  rw [source_live_box pool d hd (plainSupportPool b X₁ Y₁) (plainSupportPool b X₂ Y₂) B hB]
  unfold liveProfile
  rw [punctured_pool_profile χ S H (R*F) (mul_ne_zero hR hF)
    (fun i : liveIndices B=>pool i.val) (fun i=>hpool i.val)
    (residualPool (d.1*B (Sum.inr 0)) (mul_ne_zero hd.1 (hB _)) (plainSupportPool b X₁ Y₁))
    (residualPool (d.2*B (Sum.inr 1)) (mul_ne_zero hd.2 (hB _)) (plainSupportPool b X₂ Y₂))
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))]
  have he : (d.1*B (Sum.inr 0))≠0 ∧ (d.2*B (Sum.inr 1))≠0 :=
    ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩
  have hc := source_pool_rectangles (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) he b X₁ X₂ Y₁ Y₂
  apply centered_tuple_complete _ S H _ _ _ _ _ W₁ W₂ b X₁ X₂ Y₁ Y₂ _
    hX₁ hX₂ hY₁ hY₂ hXY he hs₁ hs₂ hc.1 hc.2 _ hS
  intro I hI
  rw [idealCoeff_excludePrimes,hoff I hI]
  split_ifs <;> rfl

end
end Candidate.FourthPower.MixedLiveRows
