/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The genuine all-length nonprincipal floor on the original tiny-radius energy. -/
import Candidate.C092.transport.LowActualOriginalCaps

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyState CenteredMomentCoreFloor
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalMaskedFloor
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

/-- Removing every original mark leaves the exact original unmarked energy,
with the same ordinary factors, mask, keep and radial scale. -/
theorem empty_subset_energy {Slot : Type*}
    (η : Character) (mask A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (X₁ X₂ : ℝ) (r : CenteredMomentRadialEligibleEnergy.Radial)
    (hX : 0 ≤ X₁*X₂) (hP : ∀ i, 0 ≤ P i) :
    subsetEnergy ∅ η mask A t W₁ W₂ pool coeff P X₁ X₂ r.keep r.profile r.scale =
      zeroEnergy η mask A t W₁ W₂ X₁ X₂ r := by
  rw [subsetEnergy_eq_selected_tsum ∅ η mask A t W₁ W₂ pool coeff P X₁ X₂ r.keep r.profile r.scale hX hP]
  simp only [selectedProduct,Finset.prod_empty,mul_one,zeroEnergy,zeroRow]

/-- The already proved masked nonprincipal contour floor handles every
positive ordinary length, including bounded and shortened lengths. Only the
fixed character modulus is absorbed into an early positive exponent q. -/
theorem original_unmarked_floor {q : ℝ} (hq : 0 < q)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) (η : Character) (Q : Ideal O) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → ∀ (Φ : 𝓢(ℝ,ℂ)),
        ∀ (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ) (hΦ : ∀ x, 0 ≤ (Φ x).re),
      ∀ (p : Profiles (1/4) (9/4)) (t height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ →
      zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂
        { keep := initialKeep η Q, profile := Φ, scale := U^V,
          scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _,
          nonneg := fun _ => hΦ _ } ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(5*V+5*q) := by
  obtain ⟨degree,controls,C0,hC0,hfloor⟩ := natural_masked_floor (1/4) (9/4) 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨degree,controls,C0*bΦ^4,mul_pos hC0 (pow_pos hbΦ _),?_⟩
  have hlarge := (tendsto_rpow_atTop hq).eventually (eventually_ge_atTop (η.modulus.absNorm : ℝ))
  filter_upwards [hlarge] with U hη
  intro hU V hV Φ hΦs hΦ p t height X₁ X₂ hh hX₁ hX₂
  let st := regularState η Q Φ bΦ U V q hU hV hq.le hΦs hΦ hη
  have hf := hfloor (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
    η Q 1 st.radial bΦ one_ne_zero hbΦ.le hΦs (fun _ hz => hz.1) (fun _ hz => hz.2)
    U V q (V+q) t X₁ X₂ hU hV hq.le rfl le_rfl hX₁ hX₂ hη
  have hheight : (1+‖t‖)^degree ≤ (1+|t|+height)^degree := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hh]) _
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hp := p.control_nonneg controls
  change zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂ st.radial ≤ _
  have hf' : zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂ st.radial ≤
      (C0*bΦ^4*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2)*
        (1+‖t‖)^degree*U^(5*V+5*q) := by
    simpa [Profiles.control,sourceControl,st,regularState,Ideal.one_eq_top,Ideal.radical_top,Ideal.absNorm_top,show V+q+4*(V+q)=5*V+5*q by ring] using hf
  exact hf'.trans (by gcongr)

end
end QRH.Cycle092.TinyCore
