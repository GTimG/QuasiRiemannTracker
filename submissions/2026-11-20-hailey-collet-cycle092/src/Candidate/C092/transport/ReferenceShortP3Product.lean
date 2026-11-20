/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact normalization: the duplicated Input is the square of the original
short column and its original whole-slot product. -/
import Candidate.C092.transport.ReferenceShortP3Input

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentSlotNormalization
open CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentDetectorPlainSource CenteredMomentUncenteredTerminal
open QRH.Cycle092.OrdinaryColumn
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_ReferenceShortP3Product_145cd43465607e5a_001 {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

theorem duplicated_positive_row {ι : Type} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (W : ℝ→ℂ)
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X : ℝ) (hX : 0 ≤ X) (hP : ∀ i, 0 ≤ P i) :
    positiveSlotRow η m A z W W (fun j : Fin 2×ι => pool j.2)
      (fun j : Fin 2×ι => coeff j.2) (fun j : Fin 2×ι => P j.2) t X X =
      (original η m A z W t X * ∏ i,normalizedSlot η m A z (pool i) (coeff i) t (P i))^2 := by
  rw [←selectedProduct_univ η m A z W W (fun j : Fin 2×ι => pool j.2)
    (fun j : Fin 2×ι => coeff j.2) (fun j : Fin 2×ι => P j.2) t X X
    (mul_nonneg hX hX) (fun j => hP j.2)]
  simp only [selectedProduct,Fintype.prod_prod_type,Fin.prod_univ_two,original]
  rw [Real.sqrt_mul hX,Complex.ofReal_mul,mul_inv_rev]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (η : Character) (t : ℝ)
variable (pool : ι → Finset (Ideal O)) (ν : ι → Ideal O → ℂ)
variable (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
variable (hprime : ∀ i, ∀ I∈pool i, Prime I) (hP : ∀ i, 0 < P i)
variable (hM : ∀ i, 1 ≤ M i) (hν : ∀ i I, ‖ν i I‖ ≤ 1)
variable (hWslot : ∀ i, Function.support (Wslot i) ⊆ Set.Icc (1:ℝ) 2)
variable (hWbound : ∀ i x, ‖Wslot i x‖ ≤ M i)
variable (W : 𝓢(ℝ,ℂ)) (a b X : ℝ) (ha : 0 < a)
variable (hs : Function.support (W : ℝ→ℂ) ⊆ Set.Icc a b) (hX : 0 < X)

theorem fourthInput_normalized_product (z : O) :
    let s := fourthInput η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX
    (Real.sqrt (volume s.toData) : ℂ)⁻¹ *
      (∑ I∈finiteColumns (Fintype.piFinset s.pools),coefficient s 1 1 I*
        rowWeight η fixedBadMask 1 z t I) =
    (original η (fixedBadMask*idealGenerator 1) 1 z W t X *
      ∏ i,normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z (pool i)
        (fun I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t (P i))^2 := by
  dsimp only
  let s := fourthInput η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX
  have he := normalized_input_difference s 1 z
  have hy : positiveSlotRow s.η (fixedBadMask*idealGenerator 1) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂ = 0 := by
    unfold positiveSlotRow
    change (Real.sqrt _ : ℂ)⁻¹ * ((CenteredMomentHeckeHeight.rowTwistedSum η
      (fixedBadMask*idealGenerator 1) 1 z W t (comparisonScale b) * _) * _) = 0
    rw [comparison_row_zero η (fixedBadMask*idealGenerator 1) 1 z t W a b ha hs,
      zero_mul,zero_mul,mul_zero]
  rw [hy,sub_zero] at he
  apply he.symm.trans
  exact duplicated_positive_row η (fixedBadMask*idealGenerator 1) 1 z W pool
    (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X hX.le (fun i => (hP i).le)

#print axioms duplicated_positive_row
#print axioms fourthInput_normalized_product
end
end QRH.Cycle092.ReferenceShortP3
