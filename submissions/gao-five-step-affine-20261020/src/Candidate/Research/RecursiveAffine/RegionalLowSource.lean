/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.LowBranch.Gate
import Candidate.Cycle63.Moment.LowBranch.FixedDeletion

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyPaidBands
open Cycle63Moment.LowBranch

variable {α : Type*} [Fintype α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- An unconditional regional LOW source operator. The native LOW detector
supplies the slot bound, and actual whole-slot removal supplies an attaining
subset. The remaining energy is literal: same natural state, mask, character,
plain profiles, scales, and radial weight, with the undeleted slots and all
rows. It can therefore be consumed by a strictly shorter recursive source
proof; it is not assumed to lie in the old region.

The fixed constant precedes the base character and every moving state,
allocation, height and scale. Neither `DeletesIntoOldRegion`, a second-step
junction nor a hypothetical bound of the source energy occurs as a premise. -/
theorem actual_regional_low_source
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height mesh a del : ℝ) (i : ℕ),
      (∀ j, 0 ≤ w j) → (∀ j ∈ J, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j ∈ J, w j ≤ mesh) →
      (∀ j, σmin ≤ σ j) → (∀ j, σ j ≤ σmax) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 → 0 ≤ del →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ s : NaturalState Z Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧ (∑ j ∈ R, w j) ≤ del+mesh ∧
        (R = J ∨ del ≤ ∑ j ∈ R, w j) ∧
        energy s.character s.mask 1 t W₁ W₂
          (fun j : J => primePool M H B (Z^(w j)))
          (fun (j : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
            annularWeight W (Z^(w j)) (σ j) (v j) I)
          (fun j : J => Z^(w j)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
          s.radial.profile s.radial.scale ≤
        C^(Fintype.card α) * Z^(2*ε*d*(Fintype.card α : ℝ)+q*(del+mesh)) *
          energy s.character s.mask 1 t W₁ W₂
            (fun j : ↥(J \ R) => primePool M H B (Z^(w j)))
            (fun (j : ↥(J \ R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
              annularWeight W (Z^(w j)) (σ j) (v j) I)
            (fun j : ↥(J \ R) => Z^(w j)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨Cs,hCs,hslots⟩ := actual_low_slots M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨max 1 Cs,le_max_left _ _,?_⟩
  intro η₀
  filter_upwards [hslots η₀] with Z hslot
  refine ⟨hslot.1,?_⟩
  intro J θ w σ v t height mesh a del i hw hwr hmesh hwm hσlo hσhi hheight hv ha ha' hdel
    hfreq hhigh s hs hQM hQη W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZ0 : 0 < Z := zero_lt_one.trans hslot.1
  let low := ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
  let pay : ℝ := max 1 Cs * Z^(2*ε*d)
  have hpay : 1 ≤ pay := by
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
      (Real.one_le_rpow hslot.1.le (by positivity))
  have hpayslot : ∀ z, s.radial.keep z → low z → ∀ j ∈ J,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H B (Z^(w j)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
          annularWeight W (Z^(w j)) (σ j) (v j) I) t (Z^(w j))‖^2 ≤ pay*Z^(q*w j) := by
    intro z hz hl j hj
    have hf : |t+v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
      have hh := abs_add_le t (v j)
      linarith [hv j]
    exact (hslot.2 s hs hQM hQη a i ha ha' (w j) (σ j) t (v j) (hw j) (hwr j hj)
      (hσlo j) (hσhi j) hf hhigh z hz hl (θ j)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 Cs) (Real.rpow_nonneg hZ0.le _))
        (Real.rpow_nonneg hZ0.le _))
  obtain ⟨R,hR,hsum,hcover,hfix⟩ := fixed_low_energy s low J W₁ W₂
    (fun j => primePool M H B (Z^(w j)))
    (fun j I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
      annularWeight W (Z^(w j)) (σ j) (v j) I)
    t X₁ X₂ q del mesh hX₁ hX₂ hq₀ hdel hmesh w (fun _ => pay)
    (fun j _ => hw j) hwm (fun _ _ => zero_le_one.trans hpay) hpayslot
  refine ⟨R,hR,hsum,hcover,hfix.trans ?_⟩
  have hprod : (∏ j ∈ R,pay) ≤ pay^(Fintype.card α) := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hpay ((Finset.card_le_card hR).trans (Finset.card_le_univ J))
  have hpower : pay^(Fintype.card α) =
      (max 1 Cs)^(Fintype.card α)*Z^(2*ε*d*(Fintype.card α : ℝ)) := by
    dsimp only [pay]
    rw [mul_pow,←Real.rpow_natCast (Z^(2*ε*d)) (Fintype.card α),←Real.rpow_mul hZ0.le]
  have hFa : (∏ j ∈ R,pay)*Z^(q*(del+mesh)) ≤
      (max 1 Cs)^(Fintype.card α)*Z^(2*ε*d*(Fintype.card α : ℝ)+q*(del+mesh)) := by
    calc _ ≤ pay^(Fintype.card α)*Z^(q*(del+mesh)) :=
          mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hZ0.le _)
      _ = _ := by rw [hpower,Real.rpow_add hZ0]; ring
  exact mul_le_mul_of_nonneg_right hFa (natural_energy_nonneg s _ _ _ _ _ _ _ _ _)

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_regional_low_source
