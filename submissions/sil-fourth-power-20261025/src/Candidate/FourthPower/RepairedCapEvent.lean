/- Copyright (c) 2026 Sil. Apache-2.0.
One arithmetic event before all moving root/common/supplier data.
Every field is numeric/support data; no energy field. 
-/
import Candidate.FourthPower.RepairedRootCaps
import Candidate.FourthPower.ReferenceCubicCharacter
import Candidate.FourthPower.OuterFreshPhysical
import Candidate.FourthPower.MixedInnerExceptionalLedger

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedCapEvent
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail MixedOriginalTailCaps
open RepairedRootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def sigmaFixed : ℝ := (ReferenceCubicCharacter.conductorConstant:ℝ) * (Ideal.span {(12:O)}).absNorm
def outerFixed : ℝ := 4 * (Ideal.span {(12:O)}).absNorm *
  (Ideal.span {fixedBadMask}).absNorm^2 * (Ideal.span {(72:O)}).absNorm^2
def innerFixed : ℝ := 4 * (CenteredMomentSecondRadicalBudget.fixedFactor:ℝ) *
  (Ideal.span {fixedBadMask}).absNorm * (Ideal.span {(72:O)}).absNorm

def PoolBound (N : ℕ) (Z : ℝ) : Prop :=
  ∀ (κ : Type u) [Fintype κ], ∀ r : Source κ (1/4) (9/4), Fintype.card κ ≤ N →
    r.X₁ ≤ Z^(3:ℝ) → r.X₂ ≤ Z^(3:ℝ) → r.Y₁ ≤ Z^(3:ℝ) → r.Y₂ ≤ Z^(3:ℝ) →
    (∏ i,r.P i) ≤ Z → poolCap r ≤ Z^(8:ℝ)

structure Event (N : ℕ) (ε Z : ℝ) : Prop where
  dimension : (9/4:ℝ)^2 * (2:ℝ)^N ≤ Z
  presentation : fixedPresentationCost ≤ Z
  sigma : sigmaFixed ≤ Z
  outer : outerFixed ≤ Z
  inner : innerFixed ≤ Z
  uniform : OuterFreshRootAdmission.UniformEvent (9/4) N (cutoffLoss N ε) Z
  pool : PoolBound.{u} N Z

theorem eventually_event (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, Event.{u} N ε Z := by
  have hpad := (internal_losses_paid N ε hε).1
  filter_upwards [eventually_source_caps N (9/4) 3 1 1 (by norm_num),
    eventually_ge_atTop ((9/4:ℝ)^2 * (2:ℝ)^N),
    eventually_ge_atTop fixedPresentationCost, eventually_ge_atTop sigmaFixed,
    eventually_ge_atTop outerFixed, eventually_ge_atTop innerFixed,
    OuterFreshRootAdmission.uniform_event (9/4) N (cutoffLoss N ε) hpad]
    with Z hp hd hf hs ho hi hu
  refine ⟨hd,hf,hs,ho,hi,hu,?_⟩
  intro κ instκ r hcard hx₁ hx₂ hy₁ hy₂ hprod
  have hh := (hp.2 κ (1/4) r hcard hx₁ hx₂ hy₁ hy₂ (by simpa only [Real.rpow_one] using hprod)).1
  simpa only [show (2*(3:ℝ)+1+1)=8 by norm_num] using hh

end
end Candidate.FourthPower.RepairedCapEvent
