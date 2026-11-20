/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual P.1 source step from its single remaining signed centered terminal. -/
import Candidate.C092.transport.OrderedPairPhaseTerminal
import Candidate.C092.transport.OrderedPairClosureSelection

set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairPhase
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrderedPairClosure
open QRH.Cycle092.StrongPair QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore
open QRH.Cycle092.WholeSlot QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle092.LowActual QRH.Cycle092.ReferenceShortP3
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" =>  ActualEisensteinCubic.O

/-- Enlarging only the freely small output exponent preserves every original
source datum and the early mesh, profiles, degree and constant. -/
theorem pair_unit_error_mono {N Y l mesh ε ε' : ℝ} (hε : ε ≤ ε')
    (hsource : PairUnitBox N Y l mesh ε) : PairUnitBox N Y l mesh ε' := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d,S,C,hC,hsource⟩ := hsource Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs
    η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [hsource,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂
  have hb := hz T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY rows mark hk₁ hk₂ hy hm₁ hm₂
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  exact hb.trans (by gcongr)

/-- The exact admitted P.1 domain leaves a strict genuine P.3 conductor
reserve for every quota below the advertised source width. -/
theorem actual_source_gates {n y l : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hl : l < sourceWidth n y) : n ≤ 1 ∧ y ≤ 1 ∧ n+y ≤ 1+shortWidth ∧ 4*(shortWidth+l) < 1 := by
  have hncap := hn1.trans (mul_le_mul_of_nonneg_left hy1 (by norm_num [sourceRatio]))
  have hquota := original_width_cap_sharp hy0 hy1 hn0
  norm_num [sourceRatio,sourceY,shortWidth,u] at hncap hy1 hquota ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor  <;>  linarith

/-- The reference is supplied genuinely, including both direct short cases.
Thus the open source now follows from the actual both-long signed centered
terminal, at its original masks; no uncentered source estimate is assumed. -/
theorem pair_uniform_of_centered
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {N Y l : ℝ} (hN : N ≤ 1) (hY : Y ≤ 1) (hNY : N+Y ≤ 1+shortWidth)
    (hl : 4*(shortWidth+l) < 1) (terminal : CenteredUniformBox N Y l) : PairUniformBox N Y l := by
  intro ε hε
  have he : 0 < min ε 1 := lt_min hε zero_lt_one
  obtain ⟨mesh,hm,hsource⟩ := terminal (min ε 1) he
  exact ⟨mesh,hm,pair_unit_error_mono (min_le_left _ _)
    (pair_unit_of_centered hβ hN hY hNY hl he (min_le_right _ _) hsource)⟩

theorem pair_open_of_centered_terminal
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (terminal : ∀ l : ℝ,0 ≤ l → l < sourceWidth n y → CenteredUniformBox n y l) :
    PairOpenWidth n y := by
  intro l hl0 hl
  obtain ⟨hN,hY,hNY,hgate⟩ := actual_source_gates hy0 hy1 hn0 hn1 hl
  exact pair_uniform_of_centered hβ hN hY hNY hgate (terminal l hl0 hl)

/-- The genuine native start and full-prefix 2904-stage induction are joined
to the proved source transition. Only the explicitly displayed signed
centered terminal remains to be supplied by the actual source assembly. -/
theorem all_pair_strips_of_centered_terminal
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (terminal : ∀ n y,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover PairOpenWidth y →
      ∀ l : ℝ,0 ≤ l → l < sourceWidth n y → CenteredUniformBox n y l) :
    ∀ n y,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → PairOpenWidth n y := by
  apply all_pair_strips_of_full_increment hβ
  intro n y hy0 hy1 hn0 hn1 cover
  exact pair_open_of_centered_terminal hβ hy0 hy1 hn0 hn1 (terminal n y hy0 hy1 hn0 hn1 cover)

/-- Componentwise shorter labelled caps retain the originally proved open
quota after the actual signed-terminal/source join. No ordering of the live
lengths, pitches or profiles is introduced. -/
theorem shortened_sources_of_centered_terminal
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (terminal : ∀ n y,sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover PairOpenWidth y →
      ∀ l : ℝ,0 ≤ l → l < sourceWidth n y → CenteredUniformBox n y l)
    {n y N Y l : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hN : N ≤ n) (hY : Y ≤ y) (hl0 : 0 ≤ l) (hl : l < sourceWidth n y) :
    PairUniformBox N Y l :=
  pair_uniform_mono hN hY le_rfl
    (all_pair_strips_of_centered_terminal hβ terminal n y hy0 hy1 hn0 hn1 l hl0 hl)

#print axioms shortened_sources_of_centered_terminal

#print axioms pair_unit_error_mono
#print axioms actual_source_gates
#print axioms pair_uniform_of_centered
#print axioms pair_open_of_centered_terminal
#print axioms all_pair_strips_of_centered_terminal
end
end QRH.Cycle092.OrderedPairPhase
