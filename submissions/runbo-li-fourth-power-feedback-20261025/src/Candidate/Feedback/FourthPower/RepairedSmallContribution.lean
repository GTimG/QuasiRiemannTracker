/- Copyright (c) 2026 Sil. Apache-2.0.
Actual SMALL contribution in the shared final Frame contract. All four
providers and both Cauchy counts are supplied by the proof, with no extra
analytic input.
-/
import Candidate.Feedback.FourthPower.RepairedSmallFirstCost

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedSmallContribution
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedFirstProfileEnvelope
open RepairedRawContext RepairedFirstFrame
open RepairedSmallCommonProfile RepairedSmallSideAlgebra RepairedSmallFirstCost
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondWindowBudget
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}

theorem uniform_small_contribution
    (Index : Type v) [Fintype Index] (RootSlot : Index→Type u) [∀k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (RootSlot k)≤N) (ε : ℝ) (hε : 0<ε)
    (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot⊆Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1≤Kslot) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)
    (η η₀ : Character) (hQη₀ : Q≤η₀.modulus) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧ ∃Cside : ℝ,1≤Cside ∧
    ∀ᶠZ : ℝ in atTop,∀k : Index,
    ∀d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀f : Frame d,∀u : Id,Squarefree u → (u.absNorm:ℝ)≤Z^(8:ℝ) →
    ∀tp : ℝ,∀rows : Finset O,
      d.contribution hε false f.label.val.1 u f.tau tp f.scale rows≤
      (Cside*(sourceControl S d.root.W₁*sourceControl S d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^J)*
        f.reference*Z^(ε/4)/(u.absNorm:ℝ)*(1+‖tp‖)^(2*J) := by
  obtain ⟨J,S,h00,C,hC,hsmall⟩:=uniform_small_first_cost (M:=M) (H:=H) (hH:=hH)
    Index RootSlot N Holes hcard ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  let Cside:=1+C*(heightEnvelope 0)^(2*J)
  have hCside:1≤Cside:=by
    have hh:=pow_nonneg (heightEnvelope_pos 0).le (2*J)
    dsimp only [Cside]
    nlinarith
  refine ⟨J,S,h00,Cside,hCside,hsmall.mono ?_⟩
  intro Z hZ k d f u hu hucap tp rows
  have hz := zero_lt_one.trans d.one_lt_Z
  have hdV := d.hV
  have he:=hZ k d f u hu hucap tp rows
  have hp:=pow_le_pow_left₀ (heightEnvelope_pos tp).le (height_envelope_le_zero tp) (2*J)
  rw [mul_pow] at hp
  have href:0≤f.reference:=by
    have hz:=(zero_lt_one.trans d.one_lt_Z).le
    unfold Frame.reference MixedFirstExceptionalNormalization.reference
    positivity
  have hh:0≤height d.t₀ d.V d.root.t₁ d.root.t₂:=by unfold height; positivity
  have hCc:C*(heightEnvelope 0)^(2*J)≤Cside:=by dsimp only [Cside]; linarith
  apply he.trans
  calc
    _≤(C*((sourceControl S d.root.W₁*sourceControl S d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^J*
        ((heightEnvelope 0)^(2*J)*(1+‖tp‖)^(2*J))))*f.reference*Z^(ε/4)/(u.absNorm:ℝ) := by
      unfold commonProfile
      gcongr
    _=((C*(heightEnvelope 0)^(2*J))*(sourceControl S d.root.W₁*sourceControl S d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^J)*f.reference*Z^(ε/4)/(u.absNorm:ℝ)*(1+‖tp‖)^(2*J) := by ring
    _≤_:=by gcongr

end
end Candidate.Feedback.FourthPower.RepairedSmallContribution
