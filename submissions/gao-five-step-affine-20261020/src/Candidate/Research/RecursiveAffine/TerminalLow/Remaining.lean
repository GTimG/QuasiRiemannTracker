/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0.
The analytic inputs below are the pinned original incumbent and its genuine
reflected-energy theorem. No recursive or improved endpoint is assumed. -/
import Candidate.Cycle63.Moment.LowBranch.Incumbent
import Candidate.Cycle63.Moment.LowBranch.ReflectedEnergy
import Candidate.Cycle63.Moment.LowBranch.WidenedState

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153TerminalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyPaidBands
open CenteredMomentEnergyReferenceProfileBudget
open Cycle63Moment.LowBranch
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The literal OLD/reflection stopping test. The reflection part includes
both its total overshoot gate and its paired plain-factor gate. -/
def RemainingTerminal (Z u : ℝ) (J R : Finset α) (w : α → ℝ) (X₁ X₂ : ℝ) : Prop :=
  R = J ∨
  length Z X₁+length Z X₂+6*Cycle63.Optimization.slotPrice*(∑ j ∈ J\R,w j) ≤ u ∨
  (length Z X₁+length Z X₂+6*Cycle63.Optimization.slotPrice*(∑ j ∈ J\R,w j) ≤ u+19/5000 ∧
    (max 0 (u-length Z X₂+1/10000)+length Z X₁+
        6*Cycle63.Optimization.slotPrice*(∑ j ∈ J\R,w j)+19/5000 ≤ u ∨
     max 0 (u-length Z X₁+1/10000)+length Z X₂+
        6*Cycle63.Optimization.slotPrice*(∑ j ∈ J\R,w j)+19/5000 ≤ u))

/-- Genuine original moment control on the SAME remaining source selected
by the LOW detector. Widening changes only the character-width upper bound;
the source rows, profiles, mask, radial weight, height and deletion R stay
literal. No second greedy deletion or extra mesh charge is introduced.
The degree and control precede the fixed character, and the constant
precedes every moving source. -/
theorem actual_terminal_remaining_source
    (W : ℝ → ℂ) (Bmask L Mcap εold εreflect : ℝ)
    (hWs : Function.support W ⊆ Icc 1 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hεold : 0 < εold) (hεreflect : 0 < εreflect)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ U : Finset (ℕ × ℕ),
    ∀ (η₀ : Character) (Q : Ideal O), Q ≤ M →
    internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
    internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J R : Finset α) (θ : α → RayQuotient.Characters M H)
        (w σ v : α → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀ j, (33/50:ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ j, |v j| ≤ height) →
      ∀ (s : NaturalState Z Bmask 2), s.fixedModulus = internalQ Q η₀ →
      ∀ (u : ℝ) (hwidth : s.width ≤ u), u ≤ Mcap → u ≤ L →
      ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      RemainingTerminal Z u J R w X₁ X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun j : ↥(J\R) => primePool M H 2 (Z^(w j)))
        (fun (j : ↥(J\R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
          annularWeight W (Z^(w j)) (σ j) (v j) I)
        (fun j : ↥(J\R) => Z^(w j)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      K*diagonalControl s.radial.profile*(p.control U)^2*
        (1+|t|+height)^degree*Z^(u+εold+εreflect) := by
  obtain ⟨degree,S,hinc⟩ := original_incumbent (α:=α) M H hH
    W 1 2 (1/4) (9/4) 2 Bmask L (33/50) (33/50) Mcap εold
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hBmask hMcap hεold hbeta
  obtain ⟨Cr,Jexp,U,hCr,hSU,hdegree,href⟩ := reflected_remaining_energy_bound (α:=α) M H hH
    W 1 2 (1/4) (9/4) 2 Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (33/50) (33/50) Mcap εold Cycle63.Optimization.slotPrice
    (19/5000) (1/10000) εreflect degree S
    (by norm_num) hWs hW.continuous (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hBmask hMcap.le hεold.le
    (by linarith [Cycle63.Optimization.slotPrice_mem.1])
    (by norm_num) (by norm_num) hεreflect
  refine ⟨Jexp,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hsource⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  let K := C₀+C₁+Cr*(C₁+1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hsource,href] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro J R θ w σ v t height hw hwL hσlo hσhi hheight hv
    s hfixed u hwidth hu huL p X₁ X₂ hX₁ hX₂ hX₁L hX₂L hterminal
  let su := widenState s u hwidth
  have hus : su.width = u := widenState_width s u hwidth
  have hsuM : su.width ≤ Mcap := hus ▸ hu
  have hsuL : su.width ≤ L := hus ▸ huL
  have hsuQ : su.fixedModulus = internalQ Q η₀ := hfixed
  have hctl : p.control S ≤ p.control U :=
    mul_le_mul (control_mono hSU (p.profile 0)) (control_mono hSU (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheight1 : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hheight0 : 0 ≤ (1+|t|+height)^degree := by positivity
  have hheightUp : (1+|t|+height)^degree ≤ (1+|t|+height)^Jexp :=
    pow_le_pow_right₀ hheight1 hdegree
  have hexp : Z^(u+εold) ≤ Z^(u+εold+εreflect) :=
    Real.rpow_le_rpow_of_exponent_le hz.1.le (by linarith)
  rcases hterminal with hRJ | hOld | hReflect
  · have he := hr.2 η₀ Q C₀ C₁ hC₀.le hC₁.le hz.2.1 hz.2.2 J R θ w σ v t height
      hw hwL hσlo hσhi hheight hv su hsuQ hsuM hsuL p X₁ X₂ hX₁ hX₂ hX₁L hX₂L (Or.inl hRJ)
    rw [hus] at he
    exact he.trans (bound_upgrade (diagonalControl_nonneg s.radial.profile)
      (by positivity) (by dsimp [K]; linarith) (p.control_nonneg U) le_rfl
      (by positivity) le_rfl (Real.rpow_nonneg (zero_lt_one.trans hz.1).le _) le_rfl)
  · have he := remaining_energy_bound M H hH W 2 (1/4) (9/4) 2 Bmask L
      (Cycle25.Energy.commonMesh Mcap Bmask L εold) (33/50) (33/50) Mcap εold
      Cycle63.Optimization.slotPrice Z η₀ Q degree S C₀ C₁ hC₀.le hC₁.le hz.2.1 hz.2.2
      J R θ w σ v t height hw hwL hσlo hσhi hheight hv su hsuQ hsuM p X₁ X₂
      hX₁ hX₂ hX₁L hX₂L (Or.inr (by simpa only [hus] using hOld))
    rw [hus] at he
    exact he.trans (bound_upgrade (diagonalControl_nonneg s.radial.profile)
      (by positivity) (by dsimp [K]; nlinarith [mul_nonneg hCr.le (show 0 ≤ C₁+1 by linarith)]) (p.control_nonneg S) hctl
      hheight0 hheightUp (Real.rpow_nonneg (zero_lt_one.trans hz.1).le _) hexp)
  · have he := hr.2 η₀ Q C₀ C₁ hC₀.le hC₁.le hz.2.1 hz.2.2 J R θ w σ v t height
      hw hwL hσlo hσhi hheight hv su hsuQ hsuM hsuL p X₁ X₂ hX₁ hX₂ hX₁L hX₂L
      (Or.inr (by simpa only [hus] using hReflect))
    rw [hus] at he
    exact he.trans (bound_upgrade (diagonalControl_nonneg s.radial.profile)
      (by positivity) (by dsimp [K]; linarith) (p.control_nonneg U) le_rfl
      (by positivity) le_rfl (Real.rpow_nonneg (zero_lt_one.trans hz.1).le _) le_rfl)
end
end OAI.SevenEighths.Cycle153TerminalLow
#print axioms OAI.SevenEighths.Cycle153TerminalLow.actual_terminal_remaining_source
