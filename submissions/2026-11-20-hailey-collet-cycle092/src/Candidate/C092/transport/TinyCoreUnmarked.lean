/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The actual incumbent zero-slot source on the original row state.
   Uses the OpenAI/Hailey incumbent certified energy induction unchanged. -/
import Candidate.C092.transport.TinyCoreSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyState CenteredMomentCoreFloor CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O

/-- This is the already proved incumbent zero-slot estimate itself. Its
individual ordinary length caps are U; its row-state width remains genuine. -/
theorem incumbent_zero_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ ε : ℝ) (hbΦ : 0 < bΦ) (hε : 0 < ε)
    (η₀ : Character) (Q : Ideal O) (hQray : Q ≤ rayM)
    (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
        ZeroAt (internalQ Q η₀) (1/4) (9/4) bΦ 0 1 2 ε U degree controls C := by
  let κ : ℝ := max (3/4) (2*HeckeZeroSupremum.beta-1)
  have hκ : (3/4 : ℝ) ≤ κ := le_max_left _ _
  have hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ := le_max_right _ _
  have hc := CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Unit) rayM Hr hHr (fun _ : ℝ => (0 : ℂ))
    1 2 (1/4) (9/4) bΦ 0 1 0 0 2 κ ε
    (by norm_num) (by simp) (by fun_prop) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) hκ hε hβ hκβ
  obtain ⟨degree,controls,hsource⟩ := CenteredMomentEnergyCappedWidthInduction.certified_terminal
    (α := Unit) rayM Hr hHr (fun _ : ℝ => (0 : ℂ)) 2 (1/4) (9/4) bΦ
    0 1 0 0 2 κ ε (by norm_num) (by norm_num) (by linarith) hε hc
  obtain ⟨C,_,hC,_,hU⟩ := hsource η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,controls,C,hC,hU.mono (fun _ h => ⟨h.1,h.2.1⟩)⟩

/-- The complete original unmarked pair, including unequal lengths and
independent profiles, at every 0<=V<=1. The fixed η modulus is absorbed
before the live radius; no padding by twice the ordinary length is needed. -/
theorem original_unmarked_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) (η η₀ : Character) (Q : Ideal O)
    (hQray : Q ≤ rayM) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → V ≤ 1 → ∀ (Φ : 𝓢(ℝ,ℂ)),
        ∀ (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ) (hΦ : ∀ x, 0 ≤ (Φ x).re),
      ∀ (p : Profiles (1/4) (9/4)) (t height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂
        { keep := initialKeep η (internalQ Q η₀), profile := Φ, scale := U^V,
          scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _, nonneg := fun _ => hΦ _ } ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V+1/10000) := by
  obtain ⟨degree,controls,C,hC,hsource⟩ := incumbent_zero_source hβ rayM Hr hHr bΦ (1/20000)
    hbΦ (by norm_num) η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,?_⟩
  have hmod := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20000)).eventually
    (eventually_ge_atTop (η.modulus.absNorm : ℝ))
  filter_upwards [hsource,hmod] with U hsource hη
  intro hU V hV0 hV1 Φ hΦs hΦ p t height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U
  let st := regularState η (internalQ Q η₀) Φ bΦ U V (1/20000) hU hV0
    (by norm_num) hΦs hΦ hη
  have hw : st.width ≤ 2 := by change V+1/20000 ≤ 2; linarith only [hV1]
  have hf := hsource.2 st rfl hw p t X₁ X₂ hX₁ hX₂ (by simpa using hX₁U) (by simpa using hX₂U)
  rw [st.plainEnergy_eq_zero] at hf
  have hheight : (1+‖t‖)^degree ≤ (1+|t|+height)^degree := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hh]) _
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hp := p.control_nonneg controls
  have hf' : zeroEnergy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1) X₁ X₂ st.radial ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+‖t‖)^degree*U^(V+1/10000) := by
    simpa [st,regularState,NaturalState.width,NaturalState.mask,add_assoc,show (20000⁻¹ : ℝ)+20000⁻¹=10000⁻¹ by norm_num] using hf
  exact hf'.trans (by gcongr)

end
end QRH.Cycle092.TinyCore
