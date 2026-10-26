/- Released under Apache 2.0. -/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Candidate.Cycle63.Optimization.SlotPrice

/-! Closed forms of the top-row certificate at slot amplitude 1/2.

The affine detector count has cutoff `cutoff lam B δ` and row-count exponent `count lam B δ`
(`R*`), where `lam` is the slope and `B` the intercept of the affine plain moment and `δ` the
zero parameter of the bin. The top-row margin `margin θ lam B δ h` is `θ - g₀ - (3/4) h R*`
with the affine numerator capacity; it is affine in the bound `θ` and the row length `h`:
`margin = c (θ - boundAt lam δ) + h * rowSlope lam B δ` (`margin_eq`). At a zero `δ` of the
row-length coefficient `rowSlope`, no row length changes the margin, so no certificate of this
form reaches a bound below `boundAt lam δ` (`margin_neg_of_rowSlope_eq_zero`). -/

namespace Cycle63.Optimization

noncomputable section

/-- Cutoff of the affine closed form at slot amplitude 1/2, a ratio of two affine functions of `δ`. -/
def cutoff (lam B δ : ℝ) : ℝ :=
  (25/2*lam - 10 + (6 - 6*lam - 3*B)*δ) / (25/2*lam - 10 + (6 - 9*lam)*δ)

/-- Row-count exponent `R*` of the affine closed form at slot amplitude 1/2. -/
def count (lam B δ : ℝ) : ℝ := 1/6 + (5/6 - δ) * cutoff lam B δ

/-- Top-row margin `θ - g₀ - (3/4) h R*` at slot amplitude 1/2 with the affine numerator capacity. -/
def margin (θ lam B δ h : ℝ) : ℝ :=
  let ell := 11/3 - 4*θ
  let y := h - 2*ell
  let cap := (2*y - (2 - B)*h)/lam
  θ - ((1 + δ)/2 + 13*h/75 - y/2 - ell/2 + ell*δ*(1/2) + h*(1/4 - 17/50) - δ*(1/2)*cap/2)
    - 3/4*h*count lam B δ

/-- Coefficient of the row length `h` in the top-row margin. -/
def rowSlope (lam B δ : ℝ) : ℝ := 7/24 + δ*B/(4*lam) - 3/4*(5/6 - δ)*cutoff lam B δ

/-- Coefficient of `θ` in the top-row margin. -/
def thetaSlope (lam δ : ℝ) : ℝ := (9*lam + 6*lam*δ + 12*δ)/(3*lam)

/-- The bound at which the top-row margin vanishes when the row-length coefficient is zero. -/
def boundAt (lam δ : ℝ) : ℝ := (7*lam*(1 + δ) + 11*δ) / (9*lam + 6*lam*δ + 12*δ)

theorem margin_eq (θ lam B δ h : ℝ) (hlam : lam ≠ 0) (hden : 9*lam + 6*lam*δ + 12*δ ≠ 0) :
    margin θ lam B δ h = thetaSlope lam δ * (θ - boundAt lam δ) + h * rowSlope lam B δ := by
  have key : thetaSlope lam δ * (θ - boundAt lam δ) =
      ((9*lam + 6*lam*δ + 12*δ)*θ - (7*lam*(1 + δ) + 11*δ))/(3*lam) := by
    unfold thetaSlope boundAt
    rw [mul_sub, div_mul_div_comm, mul_comm (9*lam + 6*lam*δ + 12*δ) (7*lam*(1 + δ) + 11*δ),
      mul_div_mul_right _ _ hden]
    ring
  rw [key]
  unfold margin rowSlope count
  generalize cutoff lam B δ = t
  field_simp
  ring

/-- The quadratic whose roots are the zeros of the row-length coefficient, cleared of
denominators: `rowSlope lam B δ = rootPoly lam B δ / (24 lam (c₀ + b δ))`. -/
def rootPoly (lam B δ : ℝ) : ℝ :=
  (7*lam + 6*δ*B) * (25/2*lam - 10 + (6 - 9*lam)*δ)
    - 18*lam*(5/6 - δ) * (25/2*lam - 10 + (6 - 6*lam - 3*B)*δ)

theorem rowSlope_eq (lam B δ : ℝ) (hlam : lam ≠ 0) (hd : 25/2*lam - 10 + (6 - 9*lam)*δ ≠ 0) :
    rowSlope lam B δ = rootPoly lam B δ / (24*lam*(25/2*lam - 10 + (6 - 9*lam)*δ)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hlam) hd)]
  unfold rowSlope rootPoly cutoff
  set D := 25/2*lam - 10 + (6 - 9*lam)*δ with hD
  set N := 25/2*lam - 10 + (6 - 6*lam - 3*B)*δ with hN
  have e1 : δ*B/(4*lam) * (24*lam*D) = 6*δ*B*D := by
    field_simp
    ring
  have e2 : 3/4*(5/6 - δ)*(N/D) * (24*lam*D) = 18*lam*(5/6 - δ)*N := by
    rw [show 3/4*(5/6 - δ)*(N/D) * (24*lam*D) = 18*lam*(5/6 - δ)*N*(D/D) by ring, div_self hd, mul_one]
  rw [show (7/24 + δ*B/(4*lam) - 3/4*(5/6 - δ)*(N/D)) * (24*lam*D) =
      7*lam*D + δ*B/(4*lam) * (24*lam*D) - 3/4*(5/6 - δ)*(N/D) * (24*lam*D) by ring, e1, e2]
  ring

def rootA2 (lam B : ℝ) : ℝ := 6*B*(6 - 9*lam) + 18*lam*(6 - 6*lam - 3*B)
def rootA1 (lam B : ℝ) : ℝ :=
  7*lam*(6 - 9*lam) + 6*B*(25/2*lam - 10) - 15*lam*(6 - 6*lam - 3*B) + 18*lam*(25/2*lam - 10)
def rootA0 (lam : ℝ) : ℝ := -8*lam*(25/2*lam - 10)

theorem rootPoly_eq_quadratic (lam B δ : ℝ) :
    rootPoly lam B δ = rootA2 lam B * (δ * δ) + rootA1 lam B * δ + rootA0 lam := by
  unfold rootPoly rootA2 rootA1 rootA0
  ring

/-- Discriminant of the quadratic `rootPoly`. -/
def rootDisc (lam B : ℝ) : ℝ := discrim (rootA2 lam B) (rootA1 lam B) (rootA0 lam)

/-- The binding zero parameter: the root of `rootPoly` given by the quadratic formula with the
positive square root (the smaller root when `a₂ < 0`). -/
def deltaStar (lam B : ℝ) : ℝ := (-rootA1 lam B + Real.sqrt (rootDisc lam B)) / (2 * rootA2 lam B)

theorem rootPoly_deltaStar {lam B : ℝ} (ha : rootA2 lam B ≠ 0) (hd : 0 ≤ rootDisc lam B) :
    rootPoly lam B (deltaStar lam B) = 0 := by
  rw [rootPoly_eq_quadratic]
  have hs : discrim (rootA2 lam B) (rootA1 lam B) (rootA0 lam) =
      Real.sqrt (rootDisc lam B) * Real.sqrt (rootDisc lam B) := by
    rw [Real.mul_self_sqrt hd]
    rfl
  exact (quadratic_eq_zero_iff ha hs (deltaStar lam B)).mpr (Or.inl rfl)

/-- The best bound of the top-row certificate for given affine slope and intercept. -/
def thetaMin (lam B : ℝ) : ℝ := boundAt lam (deltaStar lam B)

def density (q0 : ℝ) : ℝ := 1 - 10*q0/(3*(5 - 2*q0))

def cutoffDen (lam δ : ℝ) : ℝ := 25/2*lam - 10 + (6 - 9*lam)*δ

/-- The cleared margin `(c₀ + b δ) · margin`, a quadratic polynomial in `δ`. -/
def clearedMargin (θ lam B δ h : ℝ) : ℝ :=
  cutoffDen lam δ * (((9*lam + 6*lam*δ + 12*δ)*θ - 7*lam*(1 + δ) - 11*δ)/(3*lam))
    + h * rootPoly lam B δ/(24*lam)

theorem clearedMargin_eq (θ lam B δ h : ℝ) (hlam : lam ≠ 0) (hd : cutoffDen lam δ ≠ 0)
    (hden : 9*lam + 6*lam*δ + 12*δ ≠ 0) :
    clearedMargin θ lam B δ h = cutoffDen lam δ * margin θ lam B δ h := by
  have hrow : rowSlope lam B δ = rootPoly lam B δ / (24*lam*cutoffDen lam δ) :=
    rowSlope_eq lam B δ hlam hd
  have hkey : thetaSlope lam δ * (θ - boundAt lam δ) =
      ((9*lam + 6*lam*δ + 12*δ)*θ - 7*lam*(1 + δ) - 11*δ)/(3*lam) := by
    unfold thetaSlope boundAt
    rw [mul_sub, div_mul_div_comm, mul_comm (9*lam + 6*lam*δ + 12*δ) (7*lam*(1 + δ) + 11*δ),
      mul_div_mul_right _ _ hden]
    ring
  rw [margin_eq θ lam B δ h hlam hden, hkey, hrow]
  unfold clearedMargin
  generalize cutoffDen lam δ = D at hd ⊢
  field_simp

/-- The optimal row length: the `h` at which the cleared margin has a double root at `δ*`. -/
def hStar (lam B : ℝ) : ℝ :=
  -8*cutoffDen lam (deltaStar lam B)*((6*lam + 12)*thetaMin lam B - 7*lam - 11)
    / Real.sqrt (rootDisc lam B)

/-- Leading coefficient of the cleared margin at `θ = thetaMin`, `h = hStar`. -/
def kappa2 (lam B : ℝ) : ℝ :=
  (6 - 9*lam)*((6*lam + 12)*thetaMin lam B - 7*lam - 11)/(3*lam) + hStar lam B*rootA2 lam B/(24*lam)

/-- The derivative of `rootPoly` at the quadratic-formula root is the square root of the
discriminant. -/
theorem rootPoly_deriv_deltaStar {lam B : ℝ} (ha : rootA2 lam B ≠ 0) :
    2*rootA2 lam B*deltaStar lam B + rootA1 lam B = Real.sqrt (rootDisc lam B) := by
  unfold deltaStar
  field_simp
  ring

/-- Exact certificate: at the optimal row length the cleared margin is a square plus a term
proportional to `θ - thetaMin`. -/
theorem clearedMargin_hStar {lam B : ℝ} (hlam : 0 < lam) (ha : rootA2 lam B ≠ 0)
    (hdisc : 0 < rootDisc lam B) (hδ : 0 ≤ deltaStar lam B) (θ δ : ℝ) :
    clearedMargin θ lam B δ (hStar lam B) =
      kappa2 lam B*(δ - deltaStar lam B)^2
        + (θ - thetaMin lam B)*cutoffDen lam δ*(9*lam + 6*lam*δ + 12*δ)/(3*lam) := by
  have hspos : 0 < Real.sqrt (rootDisc lam B) := Real.sqrt_pos.mpr hdisc
  have hroot : rootA2 lam B*(deltaStar lam B*deltaStar lam B) + rootA1 lam B*deltaStar lam B
      + rootA0 lam = 0 := by
    have := rootPoly_deltaStar ha hdisc.le
    rwa [rootPoly_eq_quadratic] at this
  have hder := rootPoly_deriv_deltaStar ha
  have hE : 0 < 9*lam + 6*lam*deltaStar lam B + 12*deltaStar lam B := by positivity
  have hF : (9*lam + 6*lam*deltaStar lam B + 12*deltaStar lam B)*thetaMin lam B =
      7*lam*(1 + deltaStar lam B) + 11*deltaStar lam B := by
    unfold thetaMin boundAt
    exact mul_div_cancel₀ _ hE.ne'
  have hh : hStar lam B * Real.sqrt (rootDisc lam B) =
      -8*cutoffDen lam (deltaStar lam B)*((6*lam + 12)*thetaMin lam B - 7*lam - 11) := by
    unfold hStar
    exact div_mul_cancel₀ _ hspos.ne'
  have hR : rootPoly lam B δ = rootA2 lam B*(δ - deltaStar lam B)^2
      + Real.sqrt (rootDisc lam B)*(δ - deltaStar lam B) := by
    rw [rootPoly_eq_quadratic, ← hder]
    linear_combination hroot
  unfold clearedMargin kappa2
  rw [hR]
  unfold cutoffDen at hh ⊢
  linear_combination (δ - deltaStar lam B)/(24*lam) * hh
    + ((25/2*lam - 10 + (6 - 9*lam)*δ)/(3*lam)) * hF

/-- At the optimal row length the top-row margin exceeds `(θ - thetaMin)(9λ + 6λδ + 12δ)/(3λ)` at
every `δ` with positive cutoff denominator: the affine branch's top-row certificate at slot
amplitude 1/2 holds for every `θ > thetaMin`, uniformly in `δ`. -/
theorem margin_hStar_lower {lam B θ δ : ℝ} (hlam : 0 < lam) (ha : rootA2 lam B ≠ 0)
    (hdisc : 0 < rootDisc lam B) (hδs : 0 ≤ deltaStar lam B) (hk : 0 ≤ kappa2 lam B)
    (hδ : 0 ≤ δ) (hd : 0 < cutoffDen lam δ) :
    (θ - thetaMin lam B)*(9*lam + 6*lam*δ + 12*δ)/(3*lam) ≤ margin θ lam B δ (hStar lam B) := by
  have hE : 0 < 9*lam + 6*lam*δ + 12*δ := by positivity
  have h1 := clearedMargin_eq θ lam B δ (hStar lam B) hlam.ne' hd.ne' hE.ne'
  have h2 := clearedMargin_hStar hlam ha hdisc hδs θ δ
  have hsq : 0 ≤ kappa2 lam B*(δ - deltaStar lam B)^2 := mul_nonneg hk (sq_nonneg _)
  have key : cutoffDen lam δ * ((θ - thetaMin lam B)*(9*lam + 6*lam*δ + 12*δ)/(3*lam)) ≤
      cutoffDen lam δ * margin θ lam B δ (hStar lam B) := by
    rw [← h1, h2]
    have : (θ - thetaMin lam B)*cutoffDen lam δ*(9*lam + 6*lam*δ + 12*δ)/(3*lam) =
        cutoffDen lam δ * ((θ - thetaMin lam B)*(9*lam + 6*lam*δ + 12*δ)/(3*lam)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hd

/-! Facts about a downward quadratic `a x² + b x + c` with `a < 0`. -/

end

end Cycle63.Optimization
