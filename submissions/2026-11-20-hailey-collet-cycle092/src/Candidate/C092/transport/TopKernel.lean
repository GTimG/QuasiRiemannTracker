/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.TopConstants
import Candidate.C092.Physical
import Candidate.C092.Intake.QRH.Geometry
import Candidate.C092.Intake.QRH.ContactReceipt

/-! Exact common Q1 top-price certificate. The six-monomial tensor expansion
is proved once for every rational rectangle. Directed 25-digit contact bounds
and a 1e-25 capacity decrement are checked against the authentic coefficients;
30-digit downward polynomial coefficient rounding keeps repeated kernel work small.
Every per-row bound is independently checked, rather than inferred from stored margins. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Top
open QRH.Cycle090 QRH.Cycle092.TopConstants QRH.Cycle092.TopData
noncomputable section

/-- The original top capacity, with a new rigorously conservative tiny decrement. -/
def capacityProxy (h : ℝ) : ℝ := h/2-2*QRH.Cycle090.ell-1/10^(25:ℕ)
def baseProxy (h d p : ℝ) : ℝ :=
  1/2+13*h/75-(h-2*QRH.Cycle090.ell)/2-QRH.Cycle090.ell/2-9*h/100+
    d/2+d*p*(QRH.Cycle090.ell-capacityProxy h/2)
def cleared (h d p : ℝ) : ℝ :=
  (theta-baseProxy h d p)*pairedJ d p (g1Upper:ℝ)-
    3*h*pairedN d p (g0Lower:ℝ) (g1Upper:ℝ)/4

/-- Actual six-monomial polynomial evaluation, with exact rational coefficients. -/
def evaluate (a : Polynomial) (d p : ℝ) : ℝ :=
  a.c00+a.c10*d+a.c11*d*p+a.c20*d^2+a.c21*d^2*p+a.c22*d^2*p^2

def linearCoefficient (a b : ℚ) : ℕ → ℚ
  | 0 => a
  | 1 => (a+b)/2
  | _ => b

def squareCoefficient (a b : ℚ) : ℕ → ℚ
  | 0 => a^2
  | 1 => a*b
  | _ => b^2

/-- Direct tensor coefficients of the six sparse monomials. -/
def coefficients (a : Polynomial) (b : QRH.Coverage.Box) (i j : ℕ) : ℚ :=
  let d := linearCoefficient b.uLo b.uHi i
  let p := linearCoefficient b.vLo b.vHi j
  let d2 := squareCoefficient b.uLo b.uHi i
  let p2 := squareCoefficient b.vLo b.vHi j
  a.c00+a.c10*d+a.c11*d*p+a.c20*d2+a.c21*d2*p+a.c22*d2*p2

/-- Exact shape-independent tensor identity; no row-specific equality is assumed. -/
theorem expansion (a : Polynomial) (b : QRH.Coverage.Box) (x y : ℝ) :
    evaluate a ((b.uLo:ℝ)+((b.uHi:ℝ)-b.uLo)*x)
      ((b.vLo:ℝ)+((b.vHi:ℝ)-b.vLo)*y) =
    QRH.Bernstein.value 2 2 (fun i j => (coefficients a b i j:ℝ)) x y := by
  norm_num [QRH.Bernstein.value, QRH.Bernstein.tensorBasis, QRH.Bernstein.basis,
    Finset.sum_range_succ, coefficients, linearCoefficient, squareCoefficient]
  dsimp [evaluate]
  ring

def coefficientwiseLE (a b : Polynomial) : Prop :=
  a.c00≤b.c00 ∧ a.c10≤b.c10 ∧ a.c11≤b.c11 ∧
    a.c20≤b.c20 ∧ a.c21≤b.c21 ∧ a.c22≤b.c22
instance (a b : Polynomial) : Decidable (coefficientwiseLE a b) := inferInstanceAs
  (Decidable (a.c00≤b.c00 ∧ a.c10≤b.c10 ∧ a.c11≤b.c11 ∧
    a.c20≤b.c20 ∧ a.c21≤b.c21 ∧ a.c22≤b.c22))

theorem evaluate_mono {a b : Polynomial} (hc : coefficientwiseLE a b)
    {d p : ℝ} (hd : 0≤d) (hp : 0≤p) : evaluate a d p ≤ evaluate b d p := by
  have h00 := (Rat.cast_le (K:=ℝ)).mpr hc.1
  have h10 := mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hc.2.1) hd
  have h11 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hc.2.2.1) hd) hp
  have h20 := mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hc.2.2.2.1) (sq_nonneg d)
  have h21 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hc.2.2.2.2.1) (sq_nonneg d)) hp
  have h22 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hc.2.2.2.2.2) (sq_nonneg d)) (sq_nonneg p)
  dsimp [evaluate]
  linarith

theorem lower_rounding : coefficientwiseLE roundedLower exactLower := by decide +kernel
theorem upper_rounding : coefficientwiseLE roundedUpper exactUpper := by decide +kernel

theorem lower_identity (d p : ℝ) : evaluate exactLower d p = cleared hLower d p := by
  norm_num [evaluate, exactLower, cleared, baseProxy, capacityProxy, g0Lower, g1Upper,
    theta,hLower,QRH.Cycle090.ell,pairedJ,pairedN,pairedV,pairedK,pairedU]
  ring

theorem upper_identity (d p : ℝ) : evaluate exactUpper d p = cleared hUpper d p := by
  norm_num [evaluate, exactUpper, cleared, baseProxy, capacityProxy, g0Lower, g1Upper,
    theta,hUpper,QRH.Cycle090.ell,pairedJ,pairedN,pairedV,pairedK,pairedU]
  ring

theorem interpolation (h d p : ℝ) : cleared h d p =
    (1-(h-hLower)/(hUpper-hLower))*cleared hLower d p+
    ((h-hLower)/(hUpper-hLower))*cleared hUpper d p := by
  norm_num [cleared,baseProxy,capacityProxy,hLower,hUpper]
  ring

/-- A checked tensor array certifies the actual polynomial on a closed box. -/
theorem polynomial_box_bound (a : Polynomial) (box : QRH.Coverage.Box) (M : ℚ)
    (hu : box.uLo<box.uHi) (hv : box.vLo<box.vHi)
    (hc : QRH.Bernstein.coefficientsCheck 2 2 (coefficients a box) M = true)
    {point : QRH.Coverage.Point} (hp : box.Contains point) :
    (M:ℝ) ≤ evaluate a point.1 point.2 := by
  have hu' : (box.uLo:ℝ)<(box.uHi:ℝ) := Rat.cast_lt.mpr hu
  have hv' : (box.vLo:ℝ)<(box.vHi:ℝ) := Rat.cast_lt.mpr hv
  have hb := QRH.Bernstein.checked_boxValue_lower_bound 2 2 (coefficients a box) M hc
    hu' hv' hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  dsimp [QRH.Bernstein.boxValue] at hb
  rw [←expansion] at hb
  simpa only [QRH.Cycle092.Physical.reconstruct hu',QRH.Cycle092.Physical.reconstruct hv'] using hb

/-- The row-specific positive denominator lower bound, at the adverse upper corner. -/
def denominatorLower (box : QRH.Coverage.Box) : ℚ :=
  5/2-box.uHi-2*box.uHi*box.vHi*(1+2*g1Upper)

def rationalDebit (r : Row) : ℚ := (r.B+1/1000000000000)/(8175840773/10000000000)
def rationalSlope (box : QRH.Coverage.Box) : ℚ :=
  3/4*(1-box.uHi)-9/100-box.uHi*(17/200)/4

/-- The exact geometrical, quotient-sign, and conductor-slope contracts checked for each row. -/
def Shape (r : Row) : Prop :=
  0≤r.B ∧ 0<r.box.uLo ∧ r.box.uLo<r.box.uHi ∧ r.box.uHi≤1/2 ∧
  0≤r.box.vLo ∧ r.box.vLo<r.box.vHi ∧ r.box.vHi≤1/2 ∧
  0<denominatorLower r.box ∧ rationalDebit r<rationalSlope r.box
instance (r : Row) : Decidable (Shape r) := inferInstanceAs
  (Decidable (0≤r.B ∧ 0<r.box.uLo ∧ r.box.uLo<r.box.uHi ∧ r.box.uHi≤1/2 ∧
  0≤r.box.vLo ∧ r.box.vLo<r.box.vHi ∧ r.box.vHi≤1/2 ∧
  0<denominatorLower r.box ∧ rationalDebit r<rationalSlope r.box))

/-- Eighteen fresh common-polynomial coefficient checks and all row guards. -/
def check (r : Row) : Bool := decide (Shape r) &&
  (QRH.Bernstein.coefficientsCheck 2 2 (coefficients roundedLower r.box)
      (-r.B*denominatorLower r.box) &&
    QRH.Bernstein.coefficientsCheck 2 2 (coefficients roundedUpper r.box)
      (-r.B*denominatorLower r.box))

theorem shape_of_check {r : Row} (hc : check r=true) : Shape r := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  exact hc.1

/-- Checked rows supply all pointwise density and amplitude sign guards. -/
theorem point_guards {r : Row} (hs : Shape r) {point : QRH.Coverage.Point}
    (hp : r.box.Contains point) :
    0≤point.1 ∧ point.1≤1/2 ∧ 0≤point.2 ∧ point.2≤1/2 := by
  have hd0 : (0:ℝ)<(r.box.uLo:ℝ) := Rat.cast_pos.mpr hs.2.1
  have hd1 : (r.box.uHi:ℝ)≤(1/2:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      ((Rat.cast_le (K:=ℝ)).mpr hs.2.2.2.1)
  have hp0 : (0:ℝ)≤(r.box.vLo:ℝ) := Rat.cast_nonneg.mpr hs.2.2.2.2.1
  have hp1 : (r.box.vHi:ℝ)≤(1/2:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      ((Rat.cast_le (K:=ℝ)).mpr hs.2.2.2.2.2.2.1)
  exact ⟨hd0.le.trans hp.1,hp.2.1.trans hd1,hp0.trans hp.2.2.1,hp.2.2.2.trans hp1⟩

/-- The paired denominator is positive and never below its checked adverse corner. -/
theorem denominator_lower {r : Row} (hs : Shape r) {point : QRH.Coverage.Point}
    (hp : r.box.Contains point) :
    0<(denominatorLower r.box:ℝ) ∧
      (denominatorLower r.box:ℝ)≤pairedJ point.1 point.2 (g1Upper:ℝ) := by
  have hg := point_guards hs hp
  have hd0 : 0≤(r.box.uHi:ℝ) := hg.1.trans hp.2.1
  have hdp := mul_le_mul hp.2.1 hp.2.2.2 hg.2.2.1 hd0
  have hc : 0≤1+2*(g1Upper:ℝ) := by norm_num [g1Upper]
  have hprod := mul_le_mul_of_nonneg_right hdp hc
  refine ⟨Rat.cast_pos.mpr hs.2.2.2.2.2.2.2.1,?_⟩
  simp only [denominatorLower,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_one]
  dsimp [pairedJ,pairedV,pairedK]
  nlinarith [hp.2.1]

/-- The finite array and affine h interpolation prove the *actual* cleared bound. -/
theorem cleared_lower {r : Row} (hc : check r=true) {h : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower≤h) (hh' : h≤hUpper) (hp : r.box.Contains point) :
    -(r.B:ℝ)*(denominatorLower r.box:ℝ)≤cleared h point.1 point.2 := by
  have hs := shape_of_check hc
  have hg := point_guards hs hp
  have hchecks := hc
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hchecks
  have hl := polynomial_box_bound roundedLower r.box (-r.B*denominatorLower r.box)
    hs.2.2.1 hs.2.2.2.2.2.1 hchecks.2.1 hp
  have hu := polynomial_box_bound roundedUpper r.box (-r.B*denominatorLower r.box)
    hs.2.2.1 hs.2.2.2.2.2.1 hchecks.2.2 hp
  norm_num only [Rat.cast_mul,Rat.cast_neg] at hl hu
  have hl' := hl.trans (evaluate_mono lower_rounding hg.1 hg.2.2.1)
  have hu' := hu.trans (evaluate_mono upper_rounding hg.1 hg.2.2.1)
  rw [lower_identity] at hl'
  rw [upper_identity] at hu'
  have hw := QRH.Bernstein.coordinate_mem_unit conductor_interval.2.1 hh hh'
  change 0≤(h-hLower)/(hUpper-hLower) ∧ (h-hLower)/(hUpper-hLower)≤1 at hw
  rw [interpolation]
  have h0 := mul_le_mul_of_nonneg_left hl' (by linarith : 0≤1-(h-hLower)/(hUpper-hLower))
  have h1 := mul_le_mul_of_nonneg_left hu' hw.1
  nlinarith

end
end QRH.Cycle092.Top
#print axioms QRH.Cycle092.Top.expansion
#print axioms QRH.Cycle092.Top.cleared_lower
