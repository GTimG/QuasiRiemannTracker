import Mathlib.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The balanced window top: the closed form of the window top at which the capped plain line of the
detector count is tight. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section

/-! The detector count caps the slot capacity of its plain line at the window top `s`:
`zS m = min s ((B - 2 m)/λ)`. Where the cap binds, the count is the closed form of the capped
line, whose top-row margin at slot amplitude `1/2`, cleared of the denominator `25/12 - 3 δ/2`, is
a quadratic in the zero parameter `δ`. Its coefficient of `δ²` falls and its coefficient of `δ`
rises linearly with `s`, and its constant term does not depend on `s`, so its discriminant is a
quadratic in `s`. The smallest window top at which the quadratic stays nonnegative at the class
bound is the one at which it has a double root: the smaller root of the discriminant
(`balancedTop`).

The plane of the marked ledger, and with it the class bound and the row length of the top row,
depends on the window top through the marked loss, whose slot sums are bounded by the window top;
the window top is therefore computed from the plane in `ChannelWindow`, and that the capped line
holds there is checked in `Arithmetic.Bernstein.top_capped_half`. -/

/-- The plain-length allowance `11/3 - 4 θ` at the bound `θ`. -/
def ellAt (θ : ℝ) : ℝ := 11/3 - 4*θ

/-- The constant term of the part of the capped top-row margin at slot amplitude `1/2` that is
affine in the zero parameter, at the bound `θ` and the row length `h`. -/
def cappedLevelConst (θ h : ℝ) : ℝ :=
  θ - 1/2 - 13*h/75 + (h - 2*ellAt θ)/2 + ellAt θ/2 - h/4 + 17*h/50 - h/8

/-- Its coefficient of the zero parameter, for the slope `lam` and the intercept `B` of the affine
moment. -/
def cappedLevelSlope (lam B θ h : ℝ) : ℝ :=
  -1/2 - ellAt θ/2 + (2*(h - 2*ellAt θ) - (2 - B)*h)/lam/4

/-- The coefficient of `δ²` of the capped top-row margin cleared of `25/12 - 3 δ/2`, for the window
top `s`. -/
def cappedQuadA (lam B θ h s : ℝ) : ℝ := -3/2*cappedLevelSlope lam B θ h - 3*h/4*(1 + s/2)

/-- Its coefficient of `δ`. -/
def cappedQuadB (lam B θ h s : ℝ) : ℝ :=
  25/12*cappedLevelSlope lam B θ h - 3/2*cappedLevelConst θ h + 3*h/4*(5/6*(1 + s/2) + 25/12)

/-- Its constant term, which does not depend on the window top. -/
def cappedQuadC (θ h : ℝ) : ℝ := 25/12*cappedLevelConst θ h - 3*h/4*(125/72)

/-- The coefficient of `s²` of the discriminant in `δ` of the cleared capped margin. -/
def tangentA (h : ℝ) : ℝ := 25*h^2/256

/-- The coefficient of `s` of that discriminant. -/
def tangentB (lam B θ h : ℝ) : ℝ := 5*h/8*cappedQuadB lam B θ h 0 + 3*h/2*cappedQuadC θ h

/-- The constant term of that discriminant. -/
def tangentC (lam B θ h : ℝ) : ℝ :=
  cappedQuadB lam B θ h 0^2 - 4*cappedQuadA lam B θ h 0*cappedQuadC θ h

/-- The smallest window top at which the cleared capped margin at the bound `θ` has a double root
in `δ`: the smaller root of its discriminant. -/
def balancedTop (lam B θ h : ℝ) : ℝ :=
  (-tangentB lam B θ h - Real.sqrt (tangentB lam B θ h^2 - 4*tangentA h*tangentC lam B θ h)) /
    (2*tangentA h)

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
