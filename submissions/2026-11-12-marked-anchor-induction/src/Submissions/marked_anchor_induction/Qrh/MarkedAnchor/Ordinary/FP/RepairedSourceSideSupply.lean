/- Copyright (c) 2026 Sil. Apache-2.0.
Modified by Arvi (2026-10-25): the contrary hypothesis `theta < beta` is replaced by
`51/100 ≤ beta`, the only consequence of it that the source construction uses.
Interface for the raw and small-source side estimates.
The mesh and fixed losses are specified before the moving root data.
Modified by Sil (2026-10-26): SupplyFor is the balanced summed Seam 0 First.SummedRetainedRawSides (per block Second.Concrete.BalancedSummedRawSideBounds at the uncompleted child radius childScale) with contract loss 3 eps in the RootInput's eps (FP: per-divisor RetainedRawSides, eps/4); ProviderAt G eps meshCap quantifies over root inputs with slot widths <= meshCap; ContraryRawSideProvider G exports meshCap after eps and before the ambient type; eta is still fixed before the constants; outer_loss_budget restated for the 3 eps / 4 eps budget.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedRawContext
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.First.RawSidesRetained
import Submissions.sil_density_split_20261026.CubeFree.FP.RestoredInitialSource
import Submissions.sil_density_split_20261026.CubeFree.FP.RestoredRootSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSideSupply
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedOriginalTail MixedFirstProfileEnvelope
open Qrh.MarkedAnchor.Ordinary.RootParameters RepairedRawContext
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqSideSupply {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance instFiniteQuotSideSupply (M : Id) [NeZero M] : Finite (O ⧸ M) :=
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
with loss epsilon/4 and the ORIGINAL quadratic profile control.
Cube-free: the contract loss is `3ε` in the RootInput's `ε` (the root chain is instantiated at
`ε/12` by `uniform_setup_of_side_provider`, so this is FP's `ε/4` in the outer units).
Cube-free: the contract is the BALANCED summed Seam 0 (`First.SummedRetainedRawSides`,
per block `Second.Concrete.BalancedSummedRawSideBounds` at the uncompleted child radius
`childScale`), not FP's
per-divisor `RetainedRawSides`; the losses are those of the step gates `G`. -/
def SupplyFor {D : StepData} {G : StepGates D} {ι : Type u} [Fintype ι] {M : Id} [NeZero M]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH ι W N Holes ε Z Kslot η η₀)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) : Prop :=
  First.SummedRetainedRawSides d.root (by norm_num) η d.Kroot Z (cutoffLoss G N ε) (cutoffLoss G N ε)
    (Z^(8:ℝ)) (amplitude d.root d.t₀ d.V J control Cside) (3*ε) J

/-- The provider at a fixed loss `ε` and slot-width cap `meshCap`: every root input whose
slot widths are below `meshCap` satisfies the summed balanced contract. -/
def ProviderAt {D : StepData} (G : StepGates D) (ε meshCap : ℝ) : Prop :=
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
    ∀ d : RootInput G M H hH (RootSlot k) W N (2*N) ε Z Kslot η η₀,
      d.Kroot=bΦ*Z → (∀ i, d.w i ≤ meshCap) → SupplyFor d J control Cside

/-- Raw-energy input expressed through SupplyFor and RootInput.
The large and small-source estimates supply this input. Cube-free: indexed by the step
gates `G`; the slot-width cap `meshCap` (from the Seam A leaves' `meshMax`) is chosen after
`ε` and before the ambient type `α`; the original character `η` is fixed before
`∃ J control Cside`. -/
def ContraryRawSideProvider {D : StepData} (G : StepGates D) : Prop :=
  (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
  ∀ ε : ℝ, 0 < ε → ∃ meshCap : ℝ, 0 < meshCap ∧ ProviderAt G ε meshCap

theorem outer_loss_budget {D : StepData} (G : StepGates D) (ε : ℝ) (hε : 0 < ε) :
    3*ε+ε/8 ≤ 4*ε ∧ omegaLoss G ε+ε/100 ≤ 4*ε ∧ 0 < ε := by
  have ho := (omega_spec G ε hε).2.2.1
  constructor
  · linarith
  · constructor <;> linarith

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceSideSupply
