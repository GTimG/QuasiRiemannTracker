/- Copyright (c) 2026 Sil. Apache-2.0.
Actual LARGE contribution in the final shared source-side format.
This theorem supplies its branch; the small branch and final raw-energy
split are separate, explicit consumers. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedLargeProfile

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedLargeContribution
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedFirstProfileEnvelope
open RepairedRawContext RepairedFirstFrame RepairedLargeFirstCost RepairedLargeProfile
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}

theorem uniform_large_contribution
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀ k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀ k,Fintype.card (RootSlot k) ≤ N) (ε : ℝ) (hε : 0 < ε)
    (Wslot : ℝ → ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot ⊆ Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M)
    (η η₀ : Character) (hQη₀ : Q ≤ η₀.modulus) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ ∃ Cside : ℝ,1 ≤ Cside ∧
    ∀ᶠ Z : ℝ in atTop, ∀ k : Index,
    ∀ d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀ f : Frame d, ∀ u : Id, Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
    ∀ (tp : ℝ) (rows : Finset O),
      d.contribution hε true f.label.val.1 u f.tau tp f.scale rows ≤
      (Cside*(sourceControl S d.root.W₁*sourceControl S d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^J)*
        f.reference*Z^(ε/4)/(u.absNorm:ℝ)*(1+‖tp‖)^(2*J) := by
  obtain ⟨U,c,C₀,hC₀,hlarge⟩ := uniform_large_first_cost (M:=M) (H:=H) (hH:=hH)
    Index RootSlot N Holes hcard ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  obtain ⟨Cp,hCp,hprofile⟩ := uniform_root_profile (M:=M) (H:=H) (hH:=hH) N Kslot hKslot U c
  let Cside := 1+C₀*Cp
  have hCside : 1 ≤ Cside := by dsimp only [Cside]; nlinarith
  refine ⟨degree U,control U,control_zero U,Cside,hCside,hlarge.mono ?_⟩
  intro Z hZ k d f u hu hucap tp rows
  have hz := zero_lt_one.trans d.one_lt_Z
  have hdV := d.hV
  have he := hZ k d f u hu hucap tp rows
  have hp := hprofile (RootSlot k) (hcard k) Wslot Holes ε Z η η₀ d tp
  have href : 0 ≤ f.reference := by
    have hz := (zero_lt_one.trans d.one_lt_Z).le
    unfold Frame.reference MixedFirstExceptionalNormalization.reference
    positivity
  have hheight : 0 ≤ height d.t₀ d.V d.root.t₁ d.root.t₂ := by unfold height; positivity
  have hCprod : C₀*Cp ≤ Cside := by dsimp only [Cside]; linarith
  apply he.trans
  calc
    _ ≤ (C₀*(Cp*(sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U)*(1+‖tp‖)^(2*degree U)))*
        f.reference*Z^(ε/4)/(u.absNorm:ℝ) := by gcongr
    _ = ((C₀*Cp)*(sourceControl (control U) d.root.W₁*sourceControl (control U) d.root.W₂)^2*
        (height d.t₀ d.V d.root.t₁ d.root.t₂)^(degree U))*
        f.reference*Z^(ε/4)/(u.absNorm:ℝ)*(1+‖tp‖)^(2*degree U) := by ring
    _ ≤ _ := by gcongr

end
end Candidate.FourthPower.RepairedLargeContribution
