/- Copyright (c) 2026 Sil. Apache-2.0.
Exact original-column masks for the structured first physical family.
The tuple restriction is retained. Character conversion uses the generic
baseline masked-family identity, not an unrestricted OriginalData source.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedHeightEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceCommonMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedOriginalCoprimality
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceCommonMask
open CenteredMomentFirstMaskedFamily CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildAssembly
open CenteredMomentSecondHeightFamily
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentCompleteCommon
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

variable (S H : Finset PrimeIdeal) (pool : α→Finset Id)
  (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id)
  (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
  (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)

local notation "βoriginal" =>
  originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂

/-- Nonzero weighted columns retain both masks of the original profile.
The weight may cause cancellations; a nonzero sum supplies one nonzero
weighted summand, which is all the existing profile theorem needs. -/
theorem original_nonzero_masks (I : Id) (hne : βoriginal I≠0) :
    IsCoprime I R ∧ seed∣I := by
  obtain ⟨u,hu,hune,huI⟩ := finiteColumnCoefficient_witness
    (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    (fun u=>tupleWeight (punctureProduct S H) u*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) I hne
  have hm := profile_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed u
    (mul_ne_zero_iff.mp hune).2
  rwa [huI] at hm

/-- The original squarefree seed survives both genuine common extractions
for each actual active source pair. -/
theorem active_common_seed (Q : Finset Id) (beta : Id → ℂ) (s : Id)
    (hs : Squarefree s) (hbeta : ∀ I : Id, beta I ≠ 0 → s ∣ I)
    (p : ActiveLabel Q beta) : s ∣ p.val.1 ∧ s ∣ p.val.2 := by
  obtain ⟨I, _hIQ, J, _hJQ, hI, hJ, hbetaI, hbetaJ, hleft, hright⟩ :=
    commonLabel_witnesses Q beta p.val.1 p.val.2 p.property
  have hm := squarefree_mask_survives s I J hs hI.1 hJ.1
    (hbeta I hbetaI) (hbeta J hbetaJ)
  rw [← hleft, ← hright]
  exact ⟨hm.2.1, hm.2.2.1⟩

/-- The actual tuple-weighted original column has the required seed support. -/
theorem original_active_common_seed (Q : Finset Id) (hs : Squarefree seed)
    (p : ActiveLabel Q βoriginal) : seed ∣ p.val.1 ∧ seed ∣ p.val.2 := by
  exact active_common_seed Q βoriginal seed hs
    (fun I hi => (original_nonzero_masks S H pool d hd R seed ν Wslot P W₁ W₂
      b X₁ X₂ Y₁ Y₂ I hi).2) p

/-- A scalar, character, or height multiplier cannot introduce a column
violating the old seed. This is only a support statement. -/
theorem original_phase_active_common_seed (Q : Finset Id) (mu : Id → ℂ)
    (hs : Squarefree seed) (p : ActiveLabel Q (fun I => βoriginal I * mu I)) :
    seed ∣ p.val.1 ∧ seed ∣ p.val.2 := by
  apply active_common_seed Q (fun I => βoriginal I * mu I) seed hs _ p
  intro I hi
  exact (original_nonzero_masks S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ I (mul_ne_zero_iff.mp hi).1).2

/-- This only removes a redundant copy of the ORIGINAL seed mask.
It makes no claim that the same seed divides an arbitrary residual. -/
theorem original_seed_mask (I : Id) :
    (if seed∣I then βoriginal I else 0)=βoriginal I := by
  by_cases hn : βoriginal I=0
  · simp only [hn,ite_self]
  · exact if_pos (original_nonzero_masks S H pool d hd R seed ν Wslot P W₁ W₂
      b X₁ X₂ Y₁ Y₂ I hn).2

/-- Removing the profile seed is legal at a whole column divisible by
that seed. In common extraction use seed|G, hence seed|G*I. -/
theorem original_seed_eq_one (I : Id) (hs : seed∣I) :
    βoriginal I=
      originalColumn S H pool d hd R 1 ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ I := by
  unfold originalColumn finiteColumnCoefficient
  apply Finset.sum_congr rfl
  intro u hu
  have he := (Finset.mem_filter.mp hu).2
  have hsu : seed∣finiteTupleProduct u := he.symm ▸ hs
  simp only [profileCoefficient,if_pos hsu,one_dvd,ite_true]

/-- The original puncture is already present in a nonzero extracted
coefficient, so inserting its idealMask changes no residual coefficient. -/
theorem extracted_puncture_redundant (G : Id) :
    maskedSource (idealGenerator R) (fun I=>βoriginal (G*I))=(fun I=>βoriginal (G*I)) := by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (original_nonzero_masks S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ (G*I) hI).1.of_mul_left_right

/-- The same redundancy with the literal genuine/common and artificial
divisibility restrictions still inside the coefficient. -/
theorem residual_puncture_redundant (G D : Id) :
    maskedSource (idealGenerator R)
      (fun I=>if IsCoprime G I ∧ D∣I then βoriginal (G*I) else 0)=
      (fun I=>if IsCoprime G I ∧ D∣I then βoriginal (G*I) else 0) := by
  apply maskedSource_eq_of_live
  intro I hI
  have hm : IsCoprime G I ∧ D∣I := by
    by_contra hn
    exact hI (by rw [if_neg hn])
  have hb : βoriginal (G*I)≠0 := by simpa only [if_pos hm] using hI
  rw [span_idealGenerator]
  exact (original_nonzero_masks S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ (G*I) hb).1.of_mul_left_right

/-- Exact FixedPair adapter for the genuine tuple-restricted source.
Instantiate F and hτ with FixedPair.left_height or right_height. The
column window is handled later by height_column_integral, not discarded. -/
theorem original_divisor_column (η τ : Character) (F : O→ℂ) (ξ : RayCharacter)
    (hτ : ∀I : Id,Supported I→∀t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (G L I : Id) (hI : Supported I) (t : ℝ) :
    divisorCoefficient L (fun J : Id=>primaryGenerator J)
      (fun J=>βoriginal (G*J)*rowWeight η (fixedBadMask*idealGenerator R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then βoriginal (G*I) else 0)*heightCoeff τ t I := by
  have hh := divisor_column_masked η τ F ξ hτ (idealGenerator R) L I hI
    (fun J=>βoriginal (G*J)) t
  rw [extracted_puncture_redundant S H pool d hd R seed ν Wslot P W₁ W₂
    b X₁ X₂ Y₁ Y₂ G] at hh
  exact hh

end
end Candidate.FourthPower.MixedOriginalCoprimality
