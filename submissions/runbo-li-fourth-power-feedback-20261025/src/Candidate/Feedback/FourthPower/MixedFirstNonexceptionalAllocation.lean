/- Copyright (c) 2026 Sil. Apache-2.0.
The actual genuine-allocation sum of the checked nonexceptional cost.
This is finite numerical normalization, not an assumed energy estimate.
The live source retains its original prefix pair and artificial seed.
-/
import Candidate.Feedback.FourthPower.MixedActualNonexceptionalBound
import Candidate.Feedback.FourthPower.MixedCommonEnergy
import Candidate.Feedback.FourthPower.MixedLiveNormalization
import Candidate.Feedback.FourthPower.MixedSourceAssembly
import Candidate.Feedback.FourthPower.MixedFirstInactiveConductor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstNonexceptionalAllocation
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open RayFourExpansion CenteredMomentCompleteCommon CenteredMomentActive CenteredMomentCanonicalFirst
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentAllocationCost
open CenteredMomentCommonRawScale CenteredMomentSecondRadicalBudget
open CenteredMomentSecondWindowBudget CenteredMomentFirstPhysicalSource
open CenteredMomentFirstDiscardedEnergy
open MixedCommonCoefficient MixedCommonEnergy MixedLiveNormalization
open MixedActualNonexceptionalBound MixedSourceAssembly MixedFirstInactiveConductor
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι]

/-- Full raw volume divided by the full original prefix. -/
theorem live_volume_ratio (B : Tuple ι) (hB : ∀j,B j≠0)
    (d : Id×Id) (T : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    (T*∏i : liveIndices B,P i.val)/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))=
      ((T*∏i,P i)/pairNorm d)/rawReduction B P := by
  have hraw := raw_scale_identity B hB T P
  have hred := (rawReduction_pos B hB P hP).ne'
  rw [extracted_pair_norm]
  calc
    _ = remainingRaw B T P/pairNorm d := by unfold remainingRaw;ring
    _ = ((T*∏i,P i)/rawReduction B P)/pairNorm d := by
      rw [(eq_div_iff hred).mpr hraw]
    _ = _ := by ring

/-- Each actual nonzero frozen coefficient supplies a second raw-scale
reciprocal. The literal puncture can only decrease its norm. -/
theorem frozen_quadratic_cost (H : Id) (B : Tuple ι) (hB : ∀j,B j≠0)
    (G R : Id) (hG : G≠0) (hprod : finiteTupleProduct B=G)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hWnorm : ∀i x,‖Wslot i x‖≤M i) (hM : ∀i,1≤M i)
    (hW : ∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2) :
    ‖frozenWeight H B*frozenCoefficient B G R ν Wslot P‖^2/(rawReduction B P)^2≤
      (∏i,M i)^2*((2:ℝ)^Fintype.card ι)^2/(G.absNorm:ℝ)^2 := by
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hr := rawReduction_pos B hB P hP
  by_cases hc : frozenCoefficient B G R ν Wslot P=0
  · simp only [hc,mul_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hm := frozenCoefficient_norm B G R ν Wslot P M hν hWnorm hM
    have hh := (actual_reduction_norm B hB G R hprod ν Wslot P hP 1 2
      zero_lt_one hW hc).2
    rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hh
    have hi : (1:ℝ)/rawReduction B P≤(2:ℝ)^Fintype.card ι/(G.absNorm:ℝ) := by
      apply (div_le_div_iff₀ hr hg).mpr
      simpa only [one_mul] using hh
    have hnorm := (frozen_scalar_norm_le H B (frozenCoefficient B G R ν Wslot P)).trans hm
    have hMprod : 0≤∏i,M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (hM i))
    have hquot : ‖frozenWeight H B*frozenCoefficient B G R ν Wslot P‖/rawReduction B P≤
        (∏i,M i)*((2:ℝ)^Fintype.card ι)/(G.absNorm:ℝ) := by
      calc
        _ ≤ (∏i,M i)/rawReduction B P := div_le_div_of_nonneg_right hnorm hr.le
        _ = (∏i,M i)*(1/rawReduction B P) := by ring
        _ ≤ (∏i,M i)*((2:ℝ)^Fintype.card ι/(G.absNorm:ℝ)) :=
          mul_le_mul_of_nonneg_left hi hMprod
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hr.le) hquot 2
    simpa only [div_pow,mul_pow] using hs

/-- The checked closedBudget with its live dimension, volume, modulus
and seed factored out. In particular the original outer 1/W is retained. -/
def fixedBudget (degree : ℕ) (Cp Cg Z exponent A b tp Wblock : ℝ) : ℝ :=
  4*(fixedFactor:ℝ)*Cp*Cg*A*b^2*Z^exponent*
    heightEnvelope tp^(2*degree)*profileMoment degree^2/Wblock

theorem closedBudget_factored (slots degree : ℕ)
    (Cp Cg Z exponent A b volume tp Wblock : ℝ) (η : Character) (seed : Id) (d : Id×Id) :
    closedBudget slots degree Cp Cg Z exponent A b volume tp Wblock η seed d=
      fixedBudget degree Cp Cg Z exponent A b tp Wblock*(2:ℝ)^slots*
        (η.modulus.absNorm:ℝ)*(volume/pairNorm d)^2/(seed.absNorm:ℝ) := by
  unfold closedBudget fixedBudget
  ring

theorem fixedBudget_nonneg (degree : ℕ) (Cp Cg Z exponent A b tp Wblock : ℝ)
    (hCp : 0≤Cp) (hCg : 0≤Cg) (hZ : 0≤Z) (hA : 0≤A) (hW : 0≤Wblock) :
    0≤fixedBudget degree Cp Cg Z exponent A b tp Wblock := by
  have hz := Real.rpow_nonneg hZ exponent
  have ht : 0≤heightEnvelope tp := by unfold heightEnvelope;positivity
  unfold fixedBudget
  positivity

/-- Exactly the finite sum produced by the checked genuine-allocation
Cauchy estimate, with the literal frozen scalar on each summand. -/
def allocationBudget (H : Id) (S : (ι⊕Fin 2)→Finset Id) (G R : Id)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (degree : ℕ) (Cp Cg Z exponent A b T tp Wblock : ℝ)
    (η : Character) (seed : Id) (d : Id×Id) : ℝ :=
  ((actualAllocations S G).card:ℝ)*∑B : actualAllocations S G,
    ‖frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P‖^2*
      closedBudget (Fintype.card (liveIndices B.val)) degree Cp Cg Z exponent A b
        (T*∏i : liveIndices B.val,P i.val) tp Wblock η seed
        (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1))

def fullCost (P M : ι→ℝ) (degree : ℕ) (Cp Cg Z exponent A b T tp Wblock : ℝ)
    (seed : Id) (d : Id×Id) : ℝ :=
  fixedBudget degree Cp Cg Z exponent A b tp Wblock*(2:ℝ)^Fintype.card ι*
    (∏i,M i)^2*((2:ℝ)^Fintype.card ι)^2*((T*∏i,P i)/pairNorm d)^2/(seed.absNorm:ℝ)

/-- Uniform genuine count; every remaining factor is displayed. A is
the common profile/height cost of the checked live supplier. No energy
estimate for either the original or extracted coefficient is a premise. -/
theorem uniform_allocation_budget (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N→
    ∀(H : Id)(S : (ι⊕Fin 2)→Finset Id)(G R : Id),G≠0→
    ∀(ν : ι→Id→ℂ)(Wslot : ι→ℝ→ℂ)(P M : ι→ℝ),
      (∀i,0<P i)→(∀i I,‖ν i I‖≤1)→(∀i x,‖Wslot i x‖≤M i)→(∀i,1≤M i)→
      (∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2)→
    ∀(degree : ℕ)(Cp Cg Z exponent A b T tp Wblock : ℝ),
      0≤Cp→0≤Cg→0≤Z→0≤A→0≤Wblock→
    ∀(η : Character)(seed : Id)(d : Id×Id),
      allocationBudget H S G R ν Wslot P degree Cp Cg Z exponent A b T tp Wblock η seed d≤
      C*(G.absNorm:ℝ)^δ*fullCost P M degree Cp Cg Z exponent A b T tp Wblock seed d*
        (η.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2 := by
  obtain ⟨C,hC,hcount⟩ := genuine_count_squared (N+2) δ hδ
  refine ⟨C,hC,?_⟩
  intro ι instι hn H S G R hG ν Wslot P M hP hν hWnorm hM hW
    degree Cp Cg Z exponent A b T tp Wblock hCp hCg hZ hA hWblock η seed d
  let F := fixedBudget degree Cp Cg Z exponent A b tp Wblock
  let V := (T*∏i,P i)/pairNorm d
  let E := fullCost P M degree Cp Cg Z exponent A b T tp Wblock seed d*
    (η.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2
  have hF : 0≤F := fixedBudget_nonneg degree Cp Cg Z exponent A b tp Wblock hCp hCg hZ hA hWblock
  have hE : 0≤E := by
    change 0≤F*(2:ℝ)^Fintype.card ι*(∏i,M i)^2*((2:ℝ)^Fintype.card ι)^2*
      V^2/(seed.absNorm:ℝ)*(η.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2
    positivity
  have hterm (B : actualAllocations S G) :
      ‖frozenWeight H B.val*frozenCoefficient B.val G R ν Wslot P‖^2*
        closedBudget (Fintype.card (liveIndices B.val)) degree Cp Cg Z exponent A b
          (T*∏i : liveIndices B.val,P i.val) tp Wblock η seed
          (d.1*B.val (Sum.inr 0),d.2*B.val (Sum.inr 1))≤E := by
    have hB := (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1
    have hc := frozen_quadratic_cost H B.val hB G R hG (Finset.mem_filter.mp B.property).2
      ν Wslot P M hP hν hWnorm hM hW
    have hdim : Fintype.card (liveIndices B.val)≤Fintype.card ι := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
    have hp : (2:ℝ)^Fintype.card (liveIndices B.val)≤2^Fintype.card ι :=
      pow_le_pow_right₀ (by norm_num) hdim
    have hx := mul_le_mul hp hc
      (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
    have hf : 0≤F*(η.modulus.absNorm:ℝ)*V^2/(seed.absNorm:ℝ) := by positivity
    have he := mul_le_mul_of_nonneg_left hx hf
    rw [closedBudget_factored,live_volume_ratio B.val hB d T P hP]
    convert he using 1 <;> dsimp only [E,fullCost,F,V] <;> ring
  have hdim : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hn 2
  have hc := hcount hdim S G hG
  calc
    _ ≤ ((actualAllocations S G).card:ℝ)*∑_B : actualAllocations S G,E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hterm B)) (Nat.cast_nonneg _)
    _ = ((actualAllocations S G).card:ℝ)^2*E := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring
    _ ≤ (C*(G.absNorm:ℝ)^δ)*E := mul_le_mul_of_nonneg_right hc hE
    _ = _ := by dsimp only [E];ring

/-- For the ACTUAL inactive fixed pair, the linear conductor cost can
consume only one of the two extracted common-norm denominators. -/
theorem inactive_pair_denominators (η : Character) (C D : Id)
    (hC : Supported C) (hD : D≠0) (E : Finset (CommonIndex C D))
    (hE : E∈inactiveSubsets C D) (χ ξ : RayCharacter) (F : FixedPair η C D hC E χ ξ) :
    (F.left.modulus.absNorm:ℝ)/(C.absNorm:ℝ)^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)/(C.absNorm:ℝ) ∧
    (F.right.modulus.absNorm:ℝ)/(D.absNorm:ℝ)^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)/(D.absNorm:ℝ) := by
  have hc : 0<(C.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hp : 0≤fixedPresentationCost*(η.modulus.absNorm:ℝ) :=
    mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)
  have hh := fixed_pair_common_caps η C D hC hD E hE χ ξ F
  constructor
  · have he := div_le_div_of_nonneg_right
      (hh.1.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hp)) (sq_nonneg (C.absNorm:ℝ))
    apply he.trans_eq
    field_simp [hc.ne']
  · have he := div_le_div_of_nonneg_right
      (hh.2.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hp)) (sq_nonneg (D.absNorm:ℝ))
    apply he.trans_eq
    field_simp [hd.ne']

end
end Candidate.Feedback.FourthPower.MixedFirstNonexceptionalAllocation
