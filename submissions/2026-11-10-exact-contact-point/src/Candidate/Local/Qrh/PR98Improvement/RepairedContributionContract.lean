import Candidate.Local.Qrh.PR98Improvement.RepairedLargeContribution
import Candidate.Local.Qrh.PR98Improvement.RepairedSourceSideSupply
set_option autoImplicit false
namespace Candidate.PR98.RepairedContributionContract
universe u
noncomputable section
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceProfileMass
open MixedPrincipalPair MixedFirstProfileEnvelope
open Candidate.PR98.RepairedRootParameters Candidate.PR98.RepairedRawContext Candidate.PR98.RepairedFirstFrame Candidate.PR98.RepairedSourceSideSupply
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
def contributionBound {ι : Type u} [Fintype ι] {M : Id} [NeZero M]
    {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput M H hH ι W N Holes ε Z Kslot η η₀)
    (f : Frame d) (J : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) (u : Id) (tp : ℝ) : ℝ :=
  amplitude d.root d.t₀ d.V J S C*f.reference*Z^(ε/4)/(u.absNorm:ℝ)*(1+‖tp‖)^(2*J)
def ContributionFor {ι : Type u} [Fintype ι] {M : Id} [NeZero M]
    {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput M H hH ι W N Holes ε Z Kslot η η₀)
    (hε : 0 < ε) (branch : Bool) (J : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ f : Frame d,∀ u : Id,Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
    ∀ (tp : ℝ) (rows : Finset O),
      d.contribution hε branch f.label.val.1 u f.tau tp f.scale rows ≤
        contributionBound d f J S C u tp
def PendingSmallContribution : Prop :=
  (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
  ∀ ε : ℝ,∀ hε : 0 < ε,∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (M : Id) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
  ∀ (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2),
  ∀ (η η₀ : Character) (Q : Id) [NeZero Q],
    Q ≠ ⊤ → Q ≤ Ideal.span {(72:O)} → Q ≤ M → Q ≤ η₀.modulus →
  let N := Fintype.card α
  let Kslot := RestoredRootSource.slotBound W hW.continuous hWs
  ∃ J : ℕ,∃ S : Finset (ℕ×ℕ),(0,0) ∈ S ∧ ∃ C : ℝ,1 ≤ C ∧
    ∀ᶠ Z : ℝ in atTop,∀ k : RootShape α,
    ∀ d : RootInput M H hH (RootSlot k) W N (2*N) ε Z Kslot η η₀,
      ContributionFor d hε false J S C
end
end Candidate.PR98.RepairedContributionContract
