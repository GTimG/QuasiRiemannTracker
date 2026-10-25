/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform residual profile factors. Only dimension and slot caps are
enlarged; ordinary profiles remain homogeneous of degree two after
squaring. No moving volume, prefix or character is hidden in a constant.

-/
import Candidate.SilPrior.FourthPower.RepairedComponentRawCost

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedSupplierProfiles
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI.SevenEighths.CenteredMomentFiniteProfileExceptional
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalBudget
open MixedSupplierFourthRow MixedSupplierSource MixedInnerExceptionalLedger
open OuterFreshSource OuterFreshSelected
local notation "Id" => Ideal HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def selectedCap (N : ℕ) (Kslot : ℝ) : ℝ := (256:ℝ)^N*Kslot^(2*N)
def markedCap (N : ℕ) (Kslot : ℝ) : ℝ := (1024:ℝ)^N*Kslot^(3*N)
def profileEnvelope (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) : ℝ :=
  (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^degree*markedCap N Kslot

theorem profileEnvelope_nonneg (s : Source ι a b) (N : ℕ) (Kslot : ℝ)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ)
    (hK : 0 ≤ Kslot) (hZ : 0 ≤ Z) :
    0 ≤ profileEnvelope s N Kslot degree control Z ε := by
  have h₁ := sourceControl_nonneg control s.W₁
  have h₂ := sourceControl_nonneg control s.W₂
  unfold profileEnvelope markedCap
  positivity

theorem product_slot_cap {κ : Type*} [Fintype κ] (M : κ → ℝ) (N : ℕ)
    (Kslot : ℝ) (hcard : Fintype.card κ ≤ N) (hK : 1 ≤ Kslot)
    (hM : ∀ i,0 ≤ M i) (hcap : ∀ i,M i ≤ Kslot) :
    (∏ i,M i) ≤ Kslot^N := by
  calc
    _ ≤ ∏ _i : κ,Kslot := Finset.prod_le_prod₀ (fun i _ => hM i) (fun i _ => hcap i)
    _ = Kslot^(Fintype.card κ) := by simp only [Finset.prod_const,Finset.card_univ]
    _ ≤ _ := pow_le_pow_right₀ hK hcard

theorem selectedMass_le (s : Source ι a b) (ha : 0 < a) (u : Id)
    (L : Finset ι) (J : Finset {i // i ∉ Lᶜ})
    (N : ℕ) (hcard : Fintype.card ι ≤ N) (Kslot : ℝ) (hK : 1 ≤ Kslot)
    (hM : ∀ i,s.M i ≤ Kslot) :
    selectedMass (supplierData s ha u L J) s.M ≤ selectedCap N Kslot := by
  let q := supplierData s ha u L J
  have hj := (MixedSelectedVolume.selected_card_le q).trans hcard
  have hp := product_slot_cap (fun j : q.J => s.M j.val.val) N Kslot hj hK
    (fun j => zero_le_one.trans (s.hM j.val.val)) (fun j => hM j.val.val)
  have hprod : 0 ≤ ∏ j : q.J,s.M j.val.val :=
    Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.hM j.val.val))
  have hs : (∏ j : q.J,s.M j.val.val)^2 ≤ Kslot^(2*N) := by
    apply (pow_le_pow_left₀ hprod hp 2).trans_eq
    rw [← pow_mul]
    congr 1
    omega
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hj) hs
    (sq_nonneg _) (by positivity)

theorem residual_sourceProfile_le (s : Source ι a b) (ha : 0 < a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i ∉ Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (N : ℕ) (hcard : Fintype.card ι ≤ N) (Kslot : ℝ) (hK : 1 ≤ Kslot)
    (hM : ∀ i,s.M i ≤ Kslot) (degree : ℕ) (control : Finset (ℕ×ℕ))
    (Z ε : ℝ) (hZ : 0 ≤ Z) :
    sourceProfile (residualSource s ha cover u L J x) degree control Z ε ≤
      profileEnvelope s N Kslot degree control Z ε := by
  let q := supplierData s ha u L J
  let r := residualSource s ha cover u L J x
  have hr := (rest_card_le q).trans hcard
  have hp := product_slot_cap r.M N Kslot hr hK
    (fun j => zero_le_one.trans (r.hM j)) (fun j => hM j.val.val)
  have hprod : 0 ≤ ∏ j,r.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (r.hM j))
  have hp3 : (∏ j,r.M j)^3 ≤ Kslot^(3*N) := by
    apply (pow_le_pow_left₀ hprod hp 3).trans_eq
    rw [← pow_mul]
    congr 1
    omega
  have hmarked : fullMarkedCost r ≤ markedCap N Kslot := by
    rw [fullMarkedCost_eq]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hr) hp3
      (pow_nonneg hprod _) (by positivity)
  have h₁ := sourceControl_nonneg control s.W₁
  have h₂ := sourceControl_nonneg control s.W₂
  change ((sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^degree)*fullMarkedCost r ≤ _
  exact mul_le_mul_of_nonneg_left hmarked (by positivity)

end
end Candidate.SilPrior.FourthPower.RepairedSupplierProfiles
