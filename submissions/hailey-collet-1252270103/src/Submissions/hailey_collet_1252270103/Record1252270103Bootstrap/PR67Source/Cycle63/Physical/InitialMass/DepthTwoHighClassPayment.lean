import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The payment of one class of a paying HIGH part of the second step paired with a first-level label: the exponent of
the pair is at most minus the margin of the two-level ledger plus the losses. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle63.Physical Cycle63.Optimization
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A class of a HIGH part of the second step that pays its reserve, paired with a first-level label: the first-level
outside coordinate and missing radical, the class exponent and missing radical, the density times the row norm of the
class and the price of the fixed deletion are at most minus the margin of the two-level ledger plus the losses, with
`δ = 2 zeroBin σ - 1`. Premises: the first-level payment `h₁` with its common-rate saving `γ₁ ≥ 0`, the scale identity
of the child against the log norm of the child multiplier, the volume of the child after the deletion, the target of
the deletion, the cell bounds of the two-level ledger and the bound of the second-level amplifier. -/
theorem second_step_class_pair_bound {Base : Type} {base : Base → Character} {η₀ : Character} {Z B T : ℝ}
    {left : Bool} {v₁ : O} {unit : FirstSourceLabel → O}
    (R : SecondStepHighCount M H hH base η₀ Z B T left v₁ unit) {lo scale length amp loss : ℝ}
    (hpay : R.Pays lo scale length amp loss) (hlo : secondJunction ≤ lo) (σ : R.Class) {b : ℝ}
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop)
    {X0₁ X1₁ X2₁ X3₁ m₁ A₁ a₁ small₁ γ₁ κ deleted target mesh pad price ω : ℝ}
    (h₁ : X0₁ + X1₁ + density (2*R.zeroBin σ - 1)*X2₁ + (2*R.zeroBin σ - 1)*X3₁ ≤
      small₁ - (m₁*(1 - density (2*R.zeroBin σ - 1)) - (2*R.zeroBin σ - 1)*A₁ -
        a₁*amplifierCost (2*R.zeroBin σ - 1)) - γ₁)
    (hγ₁ : 0 ≤ γ₁)
    (hscale : scale + Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ) ≤ X2₁ + κ)
    (hvol : length ≤ X3₁ - deleted + pad) (hdel : fixedDeletion b ≤ target) (htarget : target ≤ deleted)
    (hm₁ : 1 ≤ m₁) (hA₁ : A₁ ≤ twoLevelTotalA b) (ha₁ : a₁ ≤ firstAmp b) (ha₂ : amp ≤ secondAmp b + ω) :
    X0₁ + X1₁ + R.exponent σ + R.missExp σ + density (2*R.zeroBin σ - 1)*R.rowExp σ + price*(target + mesh) ≤
      -highTwoMargin + small₁ + loss + density (2*R.zeroBin σ - 1)*κ + (2*R.zeroBin σ - 1)*pad + price*mesh +
        (price - firstJunction)*target + amplifierCost (2*R.zeroBin σ - 1)*ω := by
  obtain ⟨hlo', hhi, hp⟩ := hpay σ
  set δ := 2*R.zeroBin σ - 1 with hδ
  set Lv := Real.logb Z ((Ideal.span {v₁}).absNorm : ℝ) with hLv
  have h₂ : (R.exponent σ - scale) + R.missExp σ + density δ*(R.rowExp σ - Lv) + δ*0 ≤
      loss - (scale*(1 - density δ) - δ*length - amp*amplifierCost δ) - 0 := by
    unfold amplifierCost
    rw [density_eq_unmarkedDensity]
    linarith only [hp]
  have hq : R.rowExp σ ≤ (R.rowExp σ - Lv) + Lv := le_of_eq (by ring)
  have hbound := depth_two_pair_exponent_bound (mesh := mesh) (price := price) ⟨hlo.trans hlo', hhi⟩ hb h₁ h₂ hγ₁
    le_rfl hq hscale hvol hdel htarget hm₁ hA₁ ha₁ ha₂
  linarith only [hbound]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
