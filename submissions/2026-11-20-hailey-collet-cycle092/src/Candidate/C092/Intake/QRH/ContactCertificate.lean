/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Interval
import Candidate.C092.Intake.QRH.Count
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Recovered exact contact certificate

These are the literal polynomial, rational isolating endpoints, and directed
contact formulas from `CONTACT_EXACT.py`. The enclosure computations are
checked by Lean's kernel and transferred to real functions by the sound interval
evaluator. Existence and uniqueness refer to the displayed isolating interval.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace QRH.ContactCertificate

open QRH.RationalInterval

/-- Lower endpoint in the supplied algebraic isolation. -/
def alphaLo : ℚ := 109168232013339822100148 / 125000000000000000000000
/-- Upper endpoint in the supplied algebraic isolation. -/
def alphaHi : ℚ := 174669171221343715360237 / 200000000000000000000000
/-- The exact closed isolating interval. -/
def alphaInterval : Interval := ⟨alphaLo, alphaHi⟩

/-- The degree-nine contact polynomial, over any field. -/
def rootPolynomial {K : Type*} [Field K] (x : K) : K :=
  3888 * 19^5 * (15*x-13)^4 * (1-x)^5 - 7*(7-6*x)^4*(9*x-7)^5

/-- Exact rational endpoint signs and separation from the global domain edges. -/
theorem rational_root_bracket :
    (13/15 : ℚ) < alphaLo ∧ alphaLo < alphaHi ∧ alphaHi < 7/8 ∧
    rootPolynomial alphaLo < 0 ∧ 0 < rootPolynomial alphaHi := by
  decide +kernel

/-- The rational polynomial computation agrees with real evaluation. -/
theorem rootPolynomial_cast (q : ℚ) :
    ((rootPolynomial q : ℚ) : ℝ) = rootPolynomial (q : ℝ) := by
  norm_num [rootPolynomial]

/-- The sign-changing bracket is valid for the actual real polynomial. -/
theorem real_root_bracket :
    (13/15 : ℝ) < (alphaLo : ℝ) ∧ (alphaLo : ℝ) < (alphaHi : ℝ) ∧
    (alphaHi : ℝ) < 7/8 ∧ rootPolynomial (alphaLo : ℝ) < 0 ∧
    0 < rootPolynomial (alphaHi : ℝ) := by
  rcases rational_root_bracket with ⟨h₁,h₂,h₃,h₄,h₅⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr h₁
  · exact (Rat.cast_lt (K := ℝ)).mpr h₂
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr h₃
  · rw [← rootPolynomial_cast]; exact (Rat.cast_lt_zero (K := ℝ)).mpr h₄
  · rw [← rootPolynomial_cast]; exact (Rat.cast_pos (K := ℝ)).mpr h₅

/-- The actual contact polynomial has a real zero in its exact rational bracket. -/
theorem root_exists : ∃ x : ℝ, Contains alphaInterval x ∧ rootPolynomial x = 0 := by
  have hc : Continuous (rootPolynomial : ℝ → ℝ) := by unfold rootPolynomial; fun_prop
  have hz := intermediate_value_Icc real_root_bracket.2.1.le hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (rootPolynomial (alphaLo : ℝ))
        (rootPolynomial (alphaHi : ℝ)) from
      ⟨real_root_bracket.2.2.2.1.le, real_root_bracket.2.2.2.2.le⟩)
  rcases hz with ⟨x,hx,hzero⟩
  exact ⟨x,hx,hzero⟩

/-- Factored derivative, chosen to retain a narrow directed interval enclosure. -/
def derivativeExpr : Expr :=
  (3888*19^5)*(15*Expr.var-13)^3*(1-Expr.var)^4*(125-135*Expr.var) -
    7*(7-6*Expr.var)^3*(9*Expr.var-7)^4*(483-486*Expr.var)

/-- The real derivative expression. -/
noncomputable def rootDerivative (x : ℝ) : ℝ := value x derivativeExpr

/-- Every denominator guard of the polynomial derivative is discharged. -/
theorem derivative_safe : safe alphaInterval derivativeExpr = true := by decide +kernel

/-- The exact computed lower derivative endpoint is strictly positive. -/
theorem derivative_lower_positive : 0 < (enclose alphaInterval derivativeExpr).lo := by
  decide +kernel

/-- Direct differentiation identifies the expression with the polynomial derivative. -/
theorem rootPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt rootPolynomial (rootDerivative x) x := by
  have h₁ := ((hasDerivAt_id x).const_mul 15).sub_const 13
  have h₂ := (hasDerivAt_id x).const_sub 1
  have h₃ := ((hasDerivAt_id x).const_mul 6).const_sub 7
  have h₄ := ((hasDerivAt_id x).const_mul 9).sub_const 7
  convert (((h₁.pow 4).const_mul (3888*19^5)).mul (h₂.pow 5)).sub
    (((h₃.pow 4).const_mul 7).mul (h₄.pow 5)) using 1
  · rfl
  · simp [rootDerivative, derivativeExpr, value]
    ring

/-- The real derivative is positive throughout the entire isolating interval. -/
theorem rootDerivative_pos {x : ℝ} (hx : Contains alphaInterval x) :
    0 < rootDerivative x := by
  have hl : (0 : ℝ) < ((enclose alphaInterval derivativeExpr).lo : ℝ) := by
    exact_mod_cast derivative_lower_positive
  exact hl.trans_le (expression_sound alphaInterval derivativeExpr hx derivative_safe).1

/-- Strict monotonicity rules out a second root in the certified bracket. -/
theorem rootPolynomial_strictMono :
    StrictMonoOn (rootPolynomial : ℝ → ℝ) (Set.Icc (alphaLo : ℝ) (alphaHi : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · unfold rootPolynomial; fun_prop
  · intro x hx
    rw [(rootPolynomial_hasDerivAt x).deriv]
    have hmem : x ∈ Set.Icc (alphaLo : ℝ) (alphaHi : ℝ) := interior_subset hx
    exact rootDerivative_pos hmem

/-- The rational bracket isolates exactly one real root. -/
theorem root_exists_unique : ∃! x : ℝ, Contains alphaInterval x ∧ rootPolynomial x = 0 := by
  rcases root_exists with ⟨x,hx,hzero⟩
  refine ⟨x,⟨hx,hzero⟩,?_⟩
  intro y hy
  exact rootPolynomial_strictMono.injOn hy.1 hx (hy.2.trans hzero.symm)

/-- Exact rational map from the isolated algebraic root to the tangency parameter. -/
def wRat (x : ℚ) : ℚ := (12*x-14)/(9*(12*x-11))
/-- The real tangency map. -/
noncomputable def wValue (x : ℝ) : ℝ := (12*x-14)/(9*(12*x-11))
/-- Directed interval for the tangency parameter from the exact endpoint map. -/
def wInterval : Interval := ⟨wRat alphaLo, wRat alphaHi⟩

/-- The exact difference identity of the tangency map. -/
theorem w_difference (x y : ℝ) (hx : 12*x-11 ≠ 0) (hy : 12*y-11 ≠ 0) :
    wValue y-wValue x = 4*(y-x)/((12*y-11)*(12*x-11)) := by
  unfold wValue
  field_simp
  ring

/-- The map is monotone on the portion of the line containing the isolated root. -/
theorem w_mono {x y : ℝ} (hxy : x ≤ y) (hy : y < 11/12) : wValue x ≤ wValue y := by
  have hxneg : 12*x-11 < 0 := by linarith
  have hyneg : 12*y-11 < 0 := by linarith
  have hd := w_difference x y (ne_of_lt hxneg) (ne_of_lt hyneg)
  have hp : 0 < (12*y-11)*(12*x-11) := mul_pos_of_neg_of_neg hyneg hxneg
  have hn : 0 ≤ 4*(y-x)/((12*y-11)*(12*x-11)) := by positivity
  linarith

/-- The root's actual tangency parameter belongs to the computed rational interval. -/
theorem w_enclosed {x : ℝ} (hx : Contains alphaInterval x) : Contains wInterval (wValue x) := by
  have hupper : (alphaHi : ℝ) < 11/12 := by linarith [real_root_bracket.2.2.1]
  have hl := w_mono hx.1 (lt_of_le_of_lt hx.2 hupper)
  have hu := w_mono hx.2 hupper
  simpa [Contains, wInterval, wRat, wValue, alphaInterval] using And.intro hl hu

/-- Narrow rational tangency bounds from the actual recovered certificate. -/
theorem w_narrow : (7523/10000 : ℚ) < wInterval.lo ∧
    wInterval.lo < wInterval.hi ∧ wInterval.hi < 1881/2500 := by decide +kernel

/-- Literal expression for the contact intercept used inside the directed formulas. -/
def interceptExpr : Expr :=
  (Expr.var+12-(45/2)*Expr.var*Expr.var)/(45*Expr.var-14)
/-- Literal radial contact expression. -/
def radialExpr : Expr := 11*Expr.var/16-7/24-interceptExpr
/-- Literal `G1` expression from the recovered certificate. -/
def g1Expr : Expr :=
  (4/(5*Expr.var)+1/(5*(Expr.var-2/3)))*radialExpr-11/16
/-- Literal `G0` expression from the recovered certificate. -/
def g0Expr : Expr := interceptExpr+Expr.var*g1Expr
/-- The computed directed enclosure of the true `G1` value. -/
def g1Interval : Interval := enclose wInterval g1Expr
/-- The computed directed enclosure of the true `G0` value. -/
def g0Interval : Interval := enclose wInterval g0Expr
/-- The real contact slope, with exactly the same rational expression. -/
noncomputable def g1 (w : ℝ) : ℝ := value w g1Expr
/-- The real contact intercept, with exactly the same rational expression. -/
noncomputable def g0 (w : ℝ) : ℝ := value w g0Expr

/-- All denominator enclosures in the slope formula are strictly positive. -/
theorem g1_safe : safe wInterval g1Expr = true := by decide +kernel
/-- All denominator enclosures in the intercept formula are strictly positive. -/
theorem g0_safe : safe wInterval g0Expr = true := by decide +kernel

/-- The directed slope endpoints satisfy the stated decimal bounds and width. -/
theorem g1_directed_bounds :
    (3799809/50000000 : ℚ) < g1Interval.lo ∧ g1Interval.lo < g1Interval.hi ∧
    g1Interval.hi < 379981/5000000 ∧ g1Interval.hi-g1Interval.lo < 1/10^19 := by
  decide +kernel

/-- The directed intercept endpoints satisfy the stated decimal bounds and width. -/
theorem g0_directed_bounds :
    (5805911/100000000 : ℚ) < g0Interval.lo ∧ g0Interval.lo < g0Interval.hi ∧
    g0Interval.hi < 5805913/100000000 ∧ g0Interval.hi-g0Interval.lo < 1/10^19 := by
  decide +kernel

/-- The exact directed bounds apply to the actual slope at every bracketed parameter. -/
theorem g1_enclosed {x : ℝ} (hx : Contains alphaInterval x) :
    Contains g1Interval (g1 (wValue x)) :=
  expression_sound wInterval g1Expr (w_enclosed hx) g1_safe

/-- The exact directed bounds apply to the actual intercept at every bracketed parameter. -/
theorem g0_enclosed {x : ℝ} (hx : Contains alphaInterval x) :
    Contains g0Interval (g0 (wValue x)) :=
  expression_sound wInterval g0Expr (w_enclosed hx) g0_safe

/-- A real algebraic contact exists with both genuine directed coefficient enclosures. -/
theorem certified_contact_exists : ∃ x : ℝ, Contains alphaInterval x ∧
    rootPolynomial x = 0 ∧ Contains wInterval (wValue x) ∧
    Contains g0Interval (g0 (wValue x)) ∧ Contains g1Interval (g1 (wValue x)) := by
  rcases root_exists with ⟨x,hx,hzero⟩
  exact ⟨x,hx,hzero,w_enclosed hx,g0_enclosed hx,g1_enclosed hx⟩

/-- The recovered directed endpoints give an upper bound for the actual paired
count whenever the scalar count lies on its positive admitted branch. -/
theorem pairedCount_upper {x d p : ℝ} (hx : Contains alphaInterval x)
    (hd : 0 ≤ d) (hdUpper : d ≤ 5/6) (hp : 0 ≤ p)
    (hU : 0 ≤ QRH.Cycle090.pairedU p (g0Interval.lo : ℝ) (g1 (wValue x)))
    (hJ : 0 < QRH.Cycle090.pairedJ d p (g1 (wValue x)))
    (hJUpper : 0 < QRH.Cycle090.pairedJ d p (g1Interval.hi : ℝ)) :
    QRH.Cycle090.pairedCount d p (g0 (wValue x)) (g1 (wValue x)) ≤
      QRH.Cycle090.pairedCount d p (g0Interval.lo : ℝ) (g1Interval.hi : ℝ) := by
  exact (QRH.Cycle090.pairedCount_antitone_g₀ hd hdUpper hp (g0_enclosed hx).1 hJ).trans
    (QRH.Cycle090.pairedCount_monotone_g₁ hd hdUpper hp (g1_enclosed hx).2 hU hJ hJUpper)

end QRH.ContactCertificate
