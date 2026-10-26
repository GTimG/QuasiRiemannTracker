import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.FixedDeletion
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelHigh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The second step of Collet's argument at the state left by the fixed deletion of a LOW child of the first step: the
old moment at the width of the state plus the count form of the HIGH part of the second transform. Released under
Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional QuadraticInitialBound

/-- The second step at the state `s` left by the fixed deletion of a LOW child, whose slots are `J \ R`: the energy of
the state on its remaining slots, over all its kept rows, is at most the old moment at the width of the state plus the
count form of the HIGH part of the second transform, one record `Hb b` for each orientation `b` of the second
transform. The character `η₀` and the ideal `Q` come first, with the conditions under which the generic step and its
certificates hold (the ideal is below `M` and its internal modulus `internalQ Q η₀` is nonzero, not the unit ideal and
below `(72)`); then come the constants `degree`, `S`, `Kclass` and `C`, which depend on them and precede the state, the
heights and the length scales. The records and the reals `unit`, `amp`, `loss` of their payment follow the state, so
the bound is linear in the count of the HIGH part. The records pay at the energy scale of the state, its row width
`s.rowWidth` (the logarithm of its radial scale), and have at most `Kclass` classes each.
`Applicable η₀ Z s v₁ x₁ x₂ z W T length amp loss` says that the second step applies to the state `s` of the child
with multiplier `v₁`: the child is presented by `v₁` in the dictionary `base η₀`, its plain lengths `x₁`, `x₂` and its
slot length `z` lie in the range of the second step, its ledger unit is at most `W`, the heights of the zeros are at
most `T`, and `length`, `amp`, `loss` are the total length, the amplifier and the losses of the second step. -/
def SecondStepReturnAt {α : Type*} [Fintype α] {Base : Type}
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (base : Character → Base → Character)
    (Wslot : ℝ → ℂ) (bslot ap bp bΦ Bmask L Lslot lo hi Mcap ε B : ℝ)
    (Applicable : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) :
    Prop :=
  ∀ (η₀ : Character) (Q : Ideal O), Q ≤ M →
    internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)) (Kclass : ℝ) (C : ℝ), 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (J R : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
    ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
    ∀ (p : Profiles ap bp) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    ∀ (v₁ : O) (T W length amp loss : ℝ),
      Applicable η₀ Z s v₁ (CenteredMomentEnergyBands.length Z X₁) (CenteredMomentEnergyBands.length Z X₂)
        (∑ i ∈ J \ R, w i) W T length amp loss →
    ∃ (unit : Bool → FirstSourceLabel → O)
      (Hb : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z B T b v₁ (unit b)),
      (∀ b, (Hb b).Pays Cycle63.Optimization.secondJunction s.rowWidth length amp loss) ∧
      (∀ b, (Fintype.card (Hb b).Class : ℝ) ≤ Kclass) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : ↥(J \ R) => primePool M H bslot (Z ^ (w i)))
        (fun (i : ↥(J \ R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : ↥(J \ R) => Z ^ (w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 * (1 + |t| + height) ^ degree *
        (Z ^ (s.width + ε) + ∑ b, (Hb b).value)

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
