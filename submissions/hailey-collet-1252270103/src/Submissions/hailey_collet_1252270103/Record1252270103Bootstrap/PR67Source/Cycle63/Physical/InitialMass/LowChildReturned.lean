import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildPrimeReserve
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.TwoLevelHigh
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The returned part of a LOW child at the second step, and the allowance of its labels. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic Cycle63Moment
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger CenteredMomentRankinRadical
open CenteredMomentSectorLocalization CenteredMomentPartitionNorm CenteredMomentFirstMixedRoot
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondMovingSupport CenteredMomentSupport
open CenteredMomentFirstCanonicalFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The returned part of a LOW child at the second step: the count form of the HIGH part of the second transform,
one record for each orientation, at the child multiplier `v₁`, with the energy scale, the total length, the amplifier
and the loss of its payment. Both records pay the HIGH reserve of the second step's parent from `secondJunction`. -/
structure ReturnedPart {Base : Type} (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ)
    (v₁ : O) where
  /-- The units of the labels of each orientation. -/
  unit : Bool → FirstSourceLabel → O
  /-- The count form of the HIGH part of each orientation. -/
  record : (b : Bool) → SecondStepHighCount M H hH (base η₀) η₀ Z Bnorm T b v₁ (unit b)
  /-- The energy scale of the second step's parent. -/
  scale : ℝ
  /-- The total length of the second step's parent. -/
  length : ℝ
  /-- The amplifier of the second step's parent. -/
  amp : ℝ
  /-- The losses of the second step. -/
  loss : ℝ
  /-- Every class of both records pays the HIGH reserve of the parent. -/
  pays : ∀ b, (record b).Pays Cycle63.Optimization.secondJunction scale length amp loss

variable {M H hH}

/-- The count form of the returned part: the sum over the two orientations of the count forms of the records. -/
def ReturnedPart.value {Base : Type} {base : Character → Base → Character} {η₀ : Character} {Z Bnorm T : ℝ}
    {v₁ : O} (P : ReturnedPart M H hH base η₀ Z Bnorm T v₁) : ℝ :=
  ∑ b, (P.record b).value

/-- The count form of the returned part is nonnegative. -/
theorem ReturnedPart.value_nonneg {Base : Type} {base : Character → Base → Character} {η₀ : Character}
    {Z Bnorm T : ℝ} {v₁ : O} (P : ReturnedPart M H hH base η₀ Z Bnorm T v₁) (hZ : 0 ≤ Z) : 0 ≤ P.value :=
  Finset.sum_nonneg (fun b _ => (P.record b).value_nonneg hZ)

variable (M H hH) in
/-- The returned part of a bound is zero or, when `AllowRet`, the factor `factor` times the count form of a returned
part at the child multiplier `v₁` with energy scale `scale`, loss `loss`, total length at most `lengthCap`, amplifier
at most `ampCap` and at most `Kcap` classes in each record. -/
def ReturnedClause (AllowRet : Prop) {Base : Type} (base : Character → Base → Character) (η₀ : Character)
    (Z Bnorm Tz : ℝ) (v₁ : O) (scale loss lengthCap ampCap Kcap factor Ret : ℝ) : Prop :=
  Ret=0 ∨ (AllowRet ∧ ∃P : ReturnedPart M H hH base η₀ Z Bnorm Tz v₁,
    P.scale=scale ∧ P.loss=loss ∧ P.length≤lengthCap ∧ P.amp≤ampCap ∧
    (∀b,(Fintype.card (P.record b).Class:ℝ)≤Kcap) ∧ Ret=factor*P.value)

/-- A bound with the returned part zero has the returned clause. -/
theorem ReturnedClause.zero (AllowRet : Prop) {Base : Type} (base : Character → Base → Character) (η₀ : Character)
    (Z Bnorm Tz : ℝ) (v₁ : O) (scale loss lengthCap ampCap Kcap factor : ℝ) :
    ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ scale loss lengthCap ampCap Kcap factor 0 :=
  Or.inl rfl

/-- The returned clause for a returned part. -/
theorem ReturnedClause.of_part {AllowRet : Prop} (hA : AllowRet) {Base : Type} {base : Character → Base → Character}
    {η₀ : Character} {Z Bnorm Tz : ℝ} {v₁ : O} (P : ReturnedPart M H hH base η₀ Z Bnorm Tz v₁)
    {scale loss lengthCap ampCap Kcap factor : ℝ} (h₁ : P.scale=scale) (h₂ : P.loss=loss)
    (h₃ : P.length≤lengthCap) (h₄ : P.amp≤ampCap) (h₅ : ∀b,(Fintype.card (P.record b).Class:ℝ)≤Kcap) :
    ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ scale loss lengthCap ampCap Kcap factor
      (factor*P.value) :=
  Or.inr ⟨hA,P,h₁,h₂,h₃,h₄,h₅,rfl⟩

/-- The surplus of the first label `(C₁, D₁)` of a LOW child with the own first ideal `C₁`: the sixth of the excess of
three times the log norm of `C₁` over five times that of `D₁` and the log norm of the active conductor, when
positive. -/
def lowSurplus (Z : ℝ) (C₁ D₁ : Ideal O) : ℝ :=
  max (3*Real.logb Z (C₁.absNorm : ℝ) - 5*Real.logb Z (D₁.absNorm : ℝ) -
    Real.logb Z ((Ideal.span {activeConductor C₁ D₁}).absNorm : ℝ)) 0/6

/-- The allowance of the labels of a LOW child: the surplus of its first label and the excess of the log norm of the
own second ideal `E₂` over that of the common radical of the second label `(C₂, D₂)`. -/
def lowAllowance (Z : ℝ) (C₁ D₁ C₂ D₂ E₂ : Ideal O) : ℝ :=
  lowSurplus Z C₁ D₁ + (Real.logb Z (E₂.absNorm : ℝ) - Real.logb Z ((commonRadical C₂ D₂).absNorm : ℝ))

/-- The surplus of a first label is not negative. -/
theorem lowSurplus_nonneg (Z : ℝ) (C₁ D₁ : Ideal O) : 0 ≤ lowSurplus Z C₁ D₁ :=
  div_nonneg (le_max_right _ _) (by norm_num)

/-- The allowance of the labels is not negative when the own second ideal is one of the two ideals of the second
label, which have the same support. -/
theorem lowAllowance_nonneg {Z : ℝ} (hZ : 1 < Z) (C₁ D₁ C₂ D₂ E₂ : Ideal O) (hC : Supported C₂)
    (hD : Supported D₂) (hCD : primeSupport C₂ = primeSupport D₂) (hE : E₂ = C₂ ∨ E₂ = D₂) :
    0 ≤ lowAllowance Z C₁ D₁ C₂ D₂ E₂ := by
  have h := logb_commonRadical_le C₂ D₂ E₂ hC hD hCD hE Z hZ
  unfold lowAllowance
  linarith [lowSurplus_nonneg Z C₁ D₁]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
