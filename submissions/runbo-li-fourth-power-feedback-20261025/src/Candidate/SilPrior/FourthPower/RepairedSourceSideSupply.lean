/- Copyright (c) 2026 Sil. Apache-2.0.
Interface for the raw and small-source side estimates.
The mesh and fixed losses are specified before the moving root data.
-/
import Candidate.SilPrior.FourthPower.RepairedRawContext
import Candidate.SilPrior.FourthPower.RepairedFirstRawRetained
import Candidate.SilPrior.FourthPower.RestoredInitialSource
import Candidate.SilPrior.FourthPower.RestoredRootSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedSourceSideSupply
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedOriginalTail MixedFirstProfileEnvelope
open RepairedRootParameters RepairedRawContext RepairedFirstRawRetained
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

abbrev RootShape (α : Type u) [Fintype α] := Σ T0 : Finset α, Finset T0
abbrev RootSlot {α : Type u} [Fintype α] (k : RootShape α) := ↥k.2

theorem root_slot_card {α : Type u} [Fintype α] (k : RootShape α) :
    Fintype.card (RootSlot k) ≤ Fintype.card α :=
  (Fintype.card_le_of_injective (fun i : RootSlot k => i.val) Subtype.val_injective).trans
    (Fintype.card_le_of_injective (fun i : k.1 => i.val) Subtype.val_injective)

def amplitude {ι : Type u} [Fintype ι] {a b : ℝ} (s : Source ι a b)
    (t₀ V : ℝ) (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) : ℝ :=
  Cside*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J

theorem amplitude_nonneg {ι : Type u} [Fintype ι] {a b : ℝ} (s : Source ι a b)
    (t₀ V : ℝ) (hV : 0 ≤ V) (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) (hC : 0 ≤ Cside) :
    0 ≤ amplitude s t₀ V J control Cside := by
  have hh : 0 ≤ height t₀ V s.t₁ s.t₂ := by unfold height;positivity
  unfold amplitude
  positivity

/-- A uniform side provider must prove this exact retained-side contract,
with loss epsilon/4 and the ORIGINAL quadratic profile control. -/
def SupplyFor {ι : Type u} [Fintype ι] {M : Id} [NeZero M]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput M H hH ι W N Holes ε Z Kslot η η₀)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) : Prop :=
  RetainedRawSides d.root (by norm_num) η d.Kroot Z (cutoffLoss N ε) (cutoffLoss N ε)
    (Z^(8:ℝ)) (amplitude d.root d.t₀ d.V J control Cside) (ε/4) J

/-- Raw-energy input expressed through SupplyFor and RootInput.
The large and small-source estimates supply this input. -/
def ContraryRawSideProvider : Prop :=
  theta < HeckeZeroSupremum.beta →
  ∀ ε : ℝ, 0 < ε →
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (M : Id) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
  ∀ (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2),
  ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Id) [NeZero Q],
    Q≠⊤ → Q ≤ Ideal.span {(72:O)} → Q ≤ M → Q ≤ η₀.modulus →
  let N := Fintype.card α
  let Kslot := RestoredRootSource.slotBound W hW.continuous hWs
  ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ Cside : ℝ,
    1 ≤ Cside ∧ (0,0)∈control ∧ ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧
    ∀ k : RootShape α,
    ∀ d : RootInput M H hH (RootSlot k) W N (2*N) ε Z Kslot η η₀,
      d.Kroot=bΦ*Z → SupplyFor d J control Cside

theorem outer_loss_budget (ε : ℝ) (hε : 0 < ε) :
    ε/4+ε/8 ≤ ε/2 ∧ omegaLoss ε+ε/100 ≤ ε/2 ∧ ε/2 ≤ ε := by
  have ho := (omega_spec ε hε).2.2.1
  constructor
  · linarith
  · constructor <;> linarith

end
end Candidate.SilPrior.FourthPower.RepairedSourceSideSupply
