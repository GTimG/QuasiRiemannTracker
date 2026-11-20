/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary characters and heights on actual regular core subrows.
The fourth suppliers are the original zero-slot source at the same U^V. -/
import Candidate.C092.transport.ExhaustedPairPriceAllRadii
import Candidate.C092.transport.RegularColoredTerminalLeafGeometry
import Candidate.C092.transport.StrongPairSmallUnmarked
import Candidate.C092.transport.TinyCoreUnmarked
import Candidate.C092.transport.TinyCoreBridgeData

namespace QRH.Cycle092.RegularColoredForward
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore
open QRH.Cycle092.ExhaustedPairPrice
open QRH.Cycle092.CofactorOrdinary QRH.Cycle092.StrongPair
local notation "O" => ActualEisensteinCubic.O

theorem terminal_empty_child
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ Vmax ρTerminal Hsource : ℝ) (hVmax : 0 ≤ Vmax) (hρ : ρTerminal<(QRH.SourceCertificate.u:ℝ)) (hbΦ : 0 < bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQ₁ray : Q₁ ≤ rayM) (hQ₁0 : internalQ Q₁ η₀₁ ≠ 0) (hQ₁t : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ₁72 : internalQ Q₁ η₀₁ ≤ Ideal.span {(72 : O)})
    (hQ₂ray : Q₂ ≤ rayM) (hQ₂0 : internalQ Q₂ η₀₂ ≠ 0) (hQ₂t : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ₂72 : internalQ Q₂ η₀₂ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop,1 < U ∧
      ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot] (T : Finset Slot),T=∅ →
      ∀ mark : Slot→FreeRow→ℂ,∀ V : ℝ, 0 ≤ V → V ≤ Vmax →
      ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      ∀ (s : Finset FreeRow),
        (∀ u ∈ s, initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
        (∀ u ∈ s, initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
        (∀ u ∈ s, rowNorm u ≤ U^V) →
      finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*U^(V+(QRH.SourceCertificate.u:ℝ)-ρTerminal+(5/6)*max 0 (Hsource-V)) := by
  let ε := ((QRH.SourceCertificate.u:ℝ)-ρTerminal)/2
  have hε : 0<ε := by unfold ε;linarith
  obtain ⟨degree,controls,C,hC,hsource⟩ := exhausted_pair_all_radii hβ rayM Hr hHr bΦ Vmax ε hVmax hε hbΦ hsΦ
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁t hQ₁72 hQ₂ray hQ₂0 hQ₂t hQ₂72
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hsource] with U hsource
  refine ⟨hsource.1,?_⟩
  intro Slot _ _ T hT mark V hV0 hVm p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U rows hk₁ hk₂ hy
  have hE := hsource.2 V hV0 hVm p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U rows hk₁ hk₂ hy
  rw [finiteEnergyOn,hT]
  simp only [Finset.prod_empty,mul_one]
  apply hE.trans
  have hr : U^(V+ε)≤ U^(V+(QRH.SourceCertificate.u:ℝ)-ρTerminal+(5/6)*max 0 (Hsource-V)) :=
    Real.rpow_le_rpow_of_exponent_le hsource.1.le (by
      have := le_max_left (0:ℝ) (Hsource-V)
      unfold ε;linarith)
  exact mul_le_mul_of_nonneg_left hr (by
    have := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    positivity)

#print axioms terminal_empty_child
end
end QRH.Cycle092.RegularColoredForward
