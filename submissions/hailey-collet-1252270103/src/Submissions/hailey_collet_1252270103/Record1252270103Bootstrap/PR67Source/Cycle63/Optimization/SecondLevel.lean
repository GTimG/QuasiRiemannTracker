import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.LowRegion
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The region of the second application of Collet's step: the states whose LOW and HIGH reserves one amplifier
pays. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-! A state of width `M`, total length `A` and slot length `z` overshoots the old region by
`F = A + (6κ - 1) z - M`, `κ` the slot price. A second step at the junction `q` with amplifier `a` deletes the slots
of its LOW children at price `q`; the LOW reserve `a (1 - q/κ) - (q/(6κ)) F` vanishes for
`a = q F/(6 (κ - q))`, and the HIGH reserve of the zero-extraction child is `(1 - ρ(q)) M - q A - a (5 - 6 ρ(q))`.
With `K = 6 (κ - q)/(q (5 - 6 ρ(q)))` the HIGH reserve at that amplifier is
`((1 + K q)(I M - A - c z) + m M)/K` for the slope `c = (6κ - 1)/(1 + K q)` and the intercept
`I = (1 + K (1 - ρ(q)) - m)/(1 + K q)` of the region, `m` its margin (`second_high_reserve_eq`). So the region
`A + c z ≤ I M` is where one amplifier pays both reserves with `m M/K` to spare. -/

/-- The amplifier cost `5 - 6 ρ(q)` of the HIGH reserve at the junction `q`. -/
def amplifierCost (q : ℝ) : ℝ := 5 - 6*density q

/-- The LOW overshoot per unit of HIGH reserve at the second junction `q`. -/
def secondRatio (q : ℝ) : ℝ := 6*(slotPrice - q)/(q*amplifierCost q)

/-- The slot slope `c` of the second step's region. -/
def regionSlope (q : ℝ) : ℝ := (6*slotPrice - 1)/(1 + secondRatio q*q)

/-- The intercept `I` of the second step's region with margin `m`. -/
def regionIntercept (q m : ℝ) : ℝ := (1 + secondRatio q*(1 - density q) - m)/(1 + secondRatio q*q)

/-- The slot price `(1 + c)/6` at which deleting slots restores the region. -/
def regionPrice (q : ℝ) : ℝ := (1 + regionSlope q)/6

/-- The overshoot of a state over the old region. -/
def oldOvershoot (A z M : ℝ) : ℝ := A + (6*slotPrice - 1)*z - M

/-- The amplifier of the second step: the one whose LOW reserve vanishes. -/
def secondAmplifier (q A z M : ℝ) : ℝ := q*oldOvershoot A z M/(6*(slotPrice - q))

/-- The HIGH reserve of the zero-extraction child of the second step at the amplifier `a`. -/
def secondHigh (q A M a : ℝ) : ℝ := (1 - density q)*M - q*A - a*amplifierCost q

/-- The LOW reserve of the second step at the amplifier `a`. -/
def secondLow (q A z M a : ℝ) : ℝ := a*(1 - q/slotPrice) - (q/(6*slotPrice))*oldOvershoot A z M

theorem second_low_reserve_eq {q : ℝ} (hq : q ≠ slotPrice) (A z M : ℝ) :
    secondLow q A z M (secondAmplifier q A z M) = 0 := by
  have hk := slotPrice_pos.ne'
  have hd : slotPrice - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold secondLow secondAmplifier
  field_simp
  ring

/-- At the amplifier that pays the LOW reserve, the HIGH reserve is the region's slack. -/
theorem second_high_reserve_eq {q : ℝ} (hq : q ≠ 0) (hq' : q ≠ slotPrice) (hcost : amplifierCost q ≠ 0)
    (hden : 1 + secondRatio q*q ≠ 0) (A z M m : ℝ) :
    secondHigh q A M (secondAmplifier q A z M) =
      ((1 + secondRatio q*q)*(regionIntercept q m*M - A - regionSlope q*z) + m*M)/secondRatio q := by
  have hd : slotPrice - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq')
  have hK : secondRatio q ≠ 0 := by
    unfold secondRatio
    exact div_ne_zero (mul_ne_zero (by norm_num) hd) (mul_ne_zero hq hcost)
  have hKdef : 6*(slotPrice - q) = secondRatio q*(q*amplifierCost q) := by
    unfold secondRatio
    field_simp
  have hden' : 1 + q*secondRatio q ≠ 0 := by rwa [mul_comm]
  unfold secondHigh secondAmplifier oldOvershoot regionIntercept regionSlope
  rw [hKdef]
  field_simp
  ring


/-! The first step deletes from each LOW child a slot length fixed by the cell. For a region with slot slope `c`,
intercept `I` and price `κ' = (1 + c)/6`, a parent cell of total length `A₀` and slot sum `b` overshoots the region by
`g = A₀ + c b - I`; the child loses the width `6 a` of the amplifier `a`, so its overshoot is `g + 6 I a`, and the
deletion `d = (g + 6 I a)/(6 κ')` puts it on the region's boundary. -/

/-- The deletion that puts a zero-extraction child of the cell on the region's boundary. -/
def regionDeletion (price intercept gap a : ℝ) : ℝ := (gap + 6*intercept*a)/(6*price)

/-- The child after the deletion lies on the boundary of the region. -/
theorem region_deletion_boundary {price slope intercept : ℝ} (hprice : 6*price = 1 + slope) (hp : price ≠ 0)
    (A₀ b a : ℝ) :
    let d := regionDeletion price intercept (A₀ + slope*b - intercept) a
    (A₀ - d) + slope*(b - d) - intercept*(1 - 6*a) = 0 := by
  intro d
  have h : (1 + slope)*d = A₀ + slope*b - intercept + 6*intercept*a := by
    dsimp only [d, regionDeletion]
    rw [← hprice]
    field_simp
  linear_combination -h

/-- The LOW reserve of the first step at the amplifier `q g/(6 (κ' - q)) + α`: the deletion at price `q` leaves
`α (1 - q I/κ') + (q g/(6 κ')) q (1 - I)/(κ' - q)`. -/
theorem first_low_reserve_eq {q price intercept : ℝ} (hp : price ≠ 0) (hq : price - q ≠ 0) (gap α : ℝ) :
    let a := q*gap/(6*(price - q)) + α
    a - q*regionDeletion price intercept gap a =
      α*(1 - q*intercept/price) + q*gap/(6*price)*(q*(1 - intercept)/(price - q)) := by
  intro a
  dsimp only [a, regionDeletion]
  field_simp
  ring

/-- The HIGH reserve of the joint count at zero extraction is the second step's HIGH reserve at the deleted child
plus the first step's LOW reserve: `(1 - ρ) - q₁ A₀ + (q₁ - q₀) d - (a₁ + a₂)(5 - 6ρ)` for the second junction
`q₁` and `ρ = ρ(q₁)`. -/
theorem joint_high_split (q₀ q₁ A₀ d a₁ a₂ : ℝ) :
    (1 - density q₁) - q₁*A₀ + (q₁ - q₀)*d - (a₁ + a₂)*amplifierCost q₁ =
      secondHigh q₁ (A₀ - d) (1 - 6*a₁) a₂ + (a₁ - q₀*d) := by
  unfold secondHigh amplifierCost
  ring

/-- The region is Collet's plane at the second junction: `n₁ + n₂ + (1 + c) z ≤ I M` with slope `λ = 1 + c` obeying
her cancellation identity `q (λ - 1) = K_a (5 - 6ρ(q)) (6κ - λ)`, `K_a = q/(6 (κ - q))`, so the HIGH reserve at the
junction is the same in every cell of the plane. -/
theorem region_plane_cancellation {q : ℝ} (hq : q ≠ 0) (hq' : q ≠ slotPrice) (hcost : amplifierCost q ≠ 0)
    (hden : 1 + secondRatio q*q ≠ 0) :
    q*regionSlope q = amplifierRatio slotPrice 1 q*amplifierCost q*(6*slotPrice - (1 + regionSlope q)) := by
  have hd : slotPrice - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq')
  have hden' : 1 + q*secondRatio q ≠ 0 := by rwa [mul_comm]
  have hK : secondRatio q ≠ 0 := by
    unfold secondRatio
    exact div_ne_zero (mul_ne_zero (by norm_num) hd) (mul_ne_zero hq hcost)
  have hKdef : 6*(slotPrice - q) = secondRatio q*(q*amplifierCost q) := by
    unfold secondRatio
    field_simp
  unfold regionSlope amplifierRatio
  rw [mul_one, hKdef]
  field_simp
  ring
end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
