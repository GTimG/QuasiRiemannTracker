/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Bernstein
import Candidate.C092.Intake.QRH.Count
import Candidate.C092.Intake.QRH.Debit
import Candidate.C092.Intake.QRH.Constants
import Candidate.C092.Intake.QRH.ContactCertificate
import Candidate.C092.Intake.QRH.PhysicalCertificate

/-!
# Pointwise original physical prices for all 47 Q exterior terminals

An exact generated rational Bernstein certificate proves the literal Q1 price
on every actual current-exterior leaf. Exact list equality binds all 47 boxes to
the supplied forest; no stored positive numerator is used. The zero old-exterior
count eliminates that branch. The 9,681 mixed leaves, initial direct-return routes,
and analytic source/count implications remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace QRH.Cycle092.Physical

noncomputable section
open QRH.Cycle090

/-- The original Q geometric length. -/
def ell : ℝ := 11 / 3 - 4 * theta

/-- The original Q1 price, retaining its actual capped capacity and source cost. -/
def price (h d p g₀ g₁ D : ℝ) : ℝ :=
  1 / 2 + 13 * h / 75 - (h - 2 * ell) / 2 - ell / 2 - 9 * D / 100 +
    d / 2 + d * p * (ell - cappedCapacity physicalCap (h - 2 * ell) sourceCost D / 2) +
    3 * D * pairedCount d p g₀ g₁ / 4

/-- A conservative affine lower bound for the actual top capacity. -/
def capacityProxy (h : ℝ) : ℝ := h / 2 - 2 * ell - 1 / 1000000000000

/-- Original top base with the conservative capacity and conservative contacts. -/
def baseProxy (h d p : ℝ) : ℝ :=
  1 / 2 + 13 * h / 75 - (h - 2 * ell) / 2 - ell / 2 - 9 * h / 100 +
    d / 2 + d * p * (ell - capacityProxy h / 2)

/-- Clearing the *literal* physical top expression, rather than an unrelated number. -/
def clearedProxy (h d p : ℝ) : ℝ :=
  (theta - baseProxy h d p) * pairedJ d p (379981 / 5000000) -
    3 * h * pairedN d p (5805911 / 100000000) (379981 / 5000000) / 4

/-- The cleared top expression is affine in h after retaining the conservative capacity. -/
theorem cleared_interpolation (h d p : ℝ) :
    clearedProxy h d p =
      (1 - (h - hLower) / (hUpper - hLower)) * clearedProxy hLower d p +
        ((h - hLower) / (hUpper - hLower)) * clearedProxy hUpper d p := by
  norm_num [clearedProxy, baseProxy, capacityProxy, ell, theta, hLower, hUpper]
  ring

/-- The actual top capacity exceeds the conservative polynomial proxy. -/
theorem actual_capacity_lower {h : ℝ} (hh : hLower ≤ h) (hh' : h ≤ hUpper) :
    capacityProxy h ≤ cappedCapacity physicalCap (h - 2 * ell) sourceCost h := by
  have hs : 0 ≤ sourceCost ∧ sourceCost ≤ 1 / 1000000000000000 := by
    constructor
    · unfold sourceCost; positivity
    · have hpow : (10 : ℝ) ^ 15 ≤ 10 ^ (260 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 ^ (15 : ℕ)) hpow
      norm_num [sourceCost] at hh ⊢
      exact hh
  have h0 : 0 ≤ h := by norm_num [hLower] at hh; linarith
  have h1 : h ≤ 1 := hh'.trans conductor_interval.2.2.le
  have hc : capacityProxy h ≤ 1 := by
    norm_num [capacityProxy, ell, theta] at hh' ⊢
    norm_num [hUpper] at hh'
    linarith
  unfold cappedCapacity
  apply le_min
  · norm_num [capacityProxy, physicalCap, ell, theta] at hh' ⊢
    norm_num [hUpper] at hh'
    linarith
  · apply (le_div_iff₀ (by linarith : 0 < 2 + 10 * sourceCost)).2
    have hsh := mul_le_mul_of_nonneg_left h1 hs.1
    have hsc := mul_le_mul_of_nonneg_left hc hs.1
    dsimp [capacityProxy] at hsc ⊢
    nlinarith

/-- Elementary sign guards on the full contact corridor used by the actual leaf. -/
theorem admitted {d p g₀ g₁ : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 0 ≤ g₀) (hg₀' : g₀ ≤ 3 / 50)
    (hg₁ : 7 / 100 ≤ g₁) (hg₁' : g₁ ≤ 2 / 25) :
    0 ≤ pairedU p g₀ g₁ ∧ 0 < pairedJ d p g₁ ∧ pairedJ d p g₁ ≤ 5 / 2 := by
  have ht : 0 ≤ 1 + 6 * g₀ - 4 * g₁ := by linarith
  have ht' : 1 + 6 * g₀ - 4 * g₁ ≤ 27 / 25 := by linarith
  have hu := mul_le_mul_of_nonneg_left ht' hp
  have hu' := mul_le_mul_of_nonneg_right hp' (by norm_num : (0 : ℝ) ≤ 27 / 25)
  have hk0 : 0 ≤ 1 + 2 * g₁ := by linarith
  have hk1 : 1 + 2 * g₁ ≤ 29 / 25 := by linarith
  have hk := mul_le_mul_of_nonneg_left hk1 hp
  have hk' := mul_le_mul_of_nonneg_right hp' (by norm_num : (0 : ℝ) ≤ 29 / 25)
  have hpk := mul_nonneg hp hk0
  have hdp := mul_nonneg hd hpk
  have hdk := mul_nonneg hd (by linarith : 0 ≤ 1 - p * (1 + 2 * g₁))
  dsimp [pairedU, pairedJ, pairedV, pairedK]
  exact ⟨by linarith, by nlinarith, by nlinarith⟩

/-- Pointwise comparison to the directed contact endpoint, with no count hypothesis substituted. -/
theorem count_upper {d p g₀ g₁ : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000) :
    pairedCount d p g₀ g₁ ≤ pairedCount d p (5805911 / 100000000) (379981 / 5000000) := by
  have ha := admitted hd hd' hp hp' (by linarith : 0 ≤ g₀)
    (by linarith : g₀ ≤ 3 / 50) (by linarith : 7 / 100 ≤ g₁)
    (by linarith : g₁ ≤ 2 / 25)
  have hb := admitted hd hd' hp hp' (by norm_num : (0 : ℝ) ≤ 5805911 / 100000000)
    (by norm_num : (5805911 / 100000000 : ℝ) ≤ 3 / 50)
    (by linarith : 7 / 100 ≤ g₁) (by linarith : g₁ ≤ 2 / 25)
  have hc := admitted hd hd' hp hp' (by norm_num : (0 : ℝ) ≤ 5805911 / 100000000)
    (by norm_num : (5805911 / 100000000 : ℝ) ≤ 3 / 50)
    (by norm_num : (7 / 100 : ℝ) ≤ 379981 / 5000000)
    (by norm_num : (379981 / 5000000 : ℝ) ≤ 2 / 25)
  exact (pairedCount_antitone_g₀ hd (by linarith) hp hg₀ ha.2.1).trans
    (pairedCount_monotone_g₁ hd (by linarith) hp hg₁' hb.1 hb.2.1 hc.2.1)

/-- Q1 agrees exactly with the conductor-price primitive; no term or denominator is discarded. -/
theorem price_eq_conductorPrice (h d p g₀ g₁ D : ℝ) :
    price h d p g₀ g₁ D =
      conductorPrice (1 / 2 + 13 * h / 75 - (h - 2 * ell) / 2 - ell / 2 +
        d / 2 + d * p * ell) d p (pairedCount d p g₀ g₁)
        (cappedCapacity physicalCap (h - 2 * ell) sourceCost D) D := by
  dsimp [price, conductorPrice]
  ring

/-- The exact rational version of the cleared original price, used by the finite checker. -/
def qCleared (h d p : ℚ) : ℚ :=
  let t := 436666397 / 500000000
  let l := 11 / 3 - 4 * t
  let cap := h / 2 - 2 * l - 1 / 1000000000000
  let base := 1 / 2 + 13 * h / 75 - (h - 2 * l) / 2 - l / 2 - 9 * h / 100 +
    d / 2 + d * p * (l - cap / 2)
  let v := 5 / 6 - d
  let k := 1 - p * (1 + 2 * (379981 / 5000000))
  let u := 1 - p * (1 + 6 * (5805911 / 100000000) - 4 * (379981 / 5000000))
  let j := 3 * v + 2 * d * k
  let n := j / 6 + v * (j + d * u)
  (t - base) * j - 3 * h * n / 4

/-- Rational evaluation is exactly real evaluation of the physical cleared expression. -/
theorem qCleared_cast (h d p : ℚ) :
    (qCleared h d p : ℝ) = clearedProxy h d p := by
  push_cast [qCleared]
  norm_num [clearedProxy, baseProxy, capacityProxy, ell, theta,
    pairedJ, pairedN, pairedV, pairedK, pairedU]

/-- Quadratic Bernstein coefficients recovered from the two endpoints and midpoint. -/
def quadraticCoefficients (f : ℚ → ℚ) (a b : ℚ) : ℕ → ℚ
  | 0 => f a
  | 1 => 2 * f ((a + b) / 2) - (f a + f b) / 2
  | 2 => f b
  | _ => 0

/-- Tensor quadratic coefficients of the actual price on any rational rectangle. -/
def priceCoefficients (h : ℚ) (box : QRH.Coverage.Box) (i j : ℕ) : ℚ :=
  quadraticCoefficients
    (fun d => quadraticCoefficients (qCleared h d) box.vLo box.vHi j)
    box.uLo box.uHi i

/-- The finite coefficient generator expands the actual Q1 cleared polynomial.
The identity holds independently of acceptance and independently of stored prices. -/
theorem generated_expansion (h : ℚ) (box : QRH.Coverage.Box) (x y : ℝ) :
    clearedProxy h
      ((box.uLo : ℝ) + ((box.uHi : ℝ) - box.uLo) * x)
      ((box.vLo : ℝ) + ((box.vHi : ℝ) - box.vLo) * y) =
    QRH.Bernstein.value 2 2 (fun i j => (priceCoefficients h box i j : ℝ)) x y := by
  norm_num [QRH.Bernstein.value, QRH.Bernstein.tensorBasis, QRH.Bernstein.basis,
    Finset.sum_range_succ, priceCoefficients, quadraticCoefficients]
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, qCleared_cast]
  norm_num [clearedProxy, baseProxy, capacityProxy, ell, theta,
    pairedJ, pairedN, pairedV, pairedK, pairedU]
  ring

/-- Reconstruct an original coordinate from its normalized unit coordinate. -/
theorem reconstruct {a b x : ℝ} (hab : a < b) :
    a + (b - a) * QRH.Bernstein.coordinate a b x = x := by
  dsimp [QRH.Bernstein.coordinate]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- A checked generated coefficient array certifies every point of its closed rectangle. -/
theorem generated_box_bound (h : ℚ) (box : QRH.Coverage.Box) (M : ℚ)
    (hu : box.uLo < box.uHi) (hv : box.vLo < box.vHi)
    (hc : QRH.Bernstein.coefficientsCheck 2 2 (priceCoefficients h box) M = true)
    {point : QRH.Coverage.Point} (hp : box.Contains point) :
    (M : ℝ) ≤ clearedProxy h point.1 point.2 := by
  have hu' : (box.uLo : ℝ) < (box.uHi : ℝ) := Rat.cast_lt.mpr hu
  have hv' : (box.vLo : ℝ) < (box.vHi : ℝ) := Rat.cast_lt.mpr hv
  have hb := QRH.Bernstein.checked_boxValue_lower_bound 2 2 (priceCoefficients h box) M hc
    hu' hv' hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  dsimp [QRH.Bernstein.boxValue] at hb
  rw [← generated_expansion] at hb
  simpa only [reconstruct hu', reconstruct hv'] using hb


/-- The generated checker charges a positive common cleared margin and verifies all shape guards. -/
def exteriorBoxCheck (box : QRH.Coverage.Box) : Bool :=
  decide (0 ≤ box.uLo ∧ box.uLo < box.uHi ∧ box.uHi ≤ 1 / 2 ∧
    0 ≤ box.vLo ∧ box.vLo < box.vHi ∧ box.vHi ≤ 1 / 2) &&
  (QRH.Bernstein.coefficientsCheck 2 2 (priceCoefficients (8175840773 / 10000000000) box)
    (1 / 50000000) &&
  QRH.Bernstein.coefficientsCheck 2 2 (priceCoefficients (8175840793 / 10000000000) box)
    (1 / 50000000))

/-- The 47 exact current-exterior rectangles, bound below to the actual forest. -/
def exteriorBoxes : List QRH.Coverage.Box := [
  ⟨(809/2048), (405/1024), (1023/2048), (2047/4096)⟩,
  ⟨(405/1024), (811/2048), (511/1024), (2045/4096)⟩,
  ⟨(811/2048), (203/512), (1021/2048), (2043/4096)⟩,
  ⟨(813/2048), (407/1024), (2039/4096), (255/512)⟩,
  ⟨(407/1024), (815/2048), (2037/4096), (1019/2048)⟩,
  ⟨(815/2048), (51/128), (509/1024), (2037/4096)⟩,
  ⟨(817/2048), (409/1024), (2033/4096), (1017/2048)⟩,
  ⟨(409/1024), (819/2048), (127/256), (2033/4096)⟩,
  ⟨(819/2048), (205/512), (2031/4096), (127/256)⟩,
  ⟨(205/512), (821/2048), (1015/2048), (2031/4096)⟩,
  ⟨(821/2048), (411/1024), (2029/4096), (1015/2048)⟩,
  ⟨(411/1024), (823/2048), (507/1024), (2029/4096)⟩,
  ⟨(823/2048), (103/256), (2027/4096), (507/1024)⟩,
  ⟨(103/256), (825/2048), (1013/2048), (2027/4096)⟩,
  ⟨(825/2048), (413/1024), (2025/4096), (1013/2048)⟩,
  ⟨(413/1024), (827/2048), (253/512), (2025/4096)⟩,
  ⟨(827/2048), (207/512), (2023/4096), (253/512)⟩,
  ⟨(207/512), (829/2048), (2023/4096), (253/512)⟩,
  ⟨(829/2048), (415/1024), (1011/2048), (2023/4096)⟩,
  ⟨(415/1024), (831/2048), (2021/4096), (1011/2048)⟩,
  ⟨(831/2048), (13/32), (2021/4096), (1011/2048)⟩,
  ⟨(13/32), (833/2048), (505/1024), (2021/4096)⟩,
  ⟨(833/2048), (417/1024), (505/1024), (2021/4096)⟩,
  ⟨(417/1024), (835/2048), (2019/4096), (505/1024)⟩,
  ⟨(835/2048), (209/512), (2019/4096), (505/1024)⟩,
  ⟨(209/512), (837/2048), (1009/2048), (2019/4096)⟩,
  ⟨(837/2048), (419/1024), (1009/2048), (2019/4096)⟩,
  ⟨(419/1024), (839/2048), (1009/2048), (2019/4096)⟩,
  ⟨(839/2048), (105/256), (2017/4096), (1009/2048)⟩,
  ⟨(105/256), (841/2048), (2017/4096), (1009/2048)⟩,
  ⟨(841/2048), (421/1024), (2017/4096), (1009/2048)⟩,
  ⟨(421/1024), (843/2048), (2017/4096), (1009/2048)⟩,
  ⟨(845/2048), (423/1024), (63/128), (2017/4096)⟩,
  ⟨(423/1024), (847/2048), (63/128), (2017/4096)⟩,
  ⟨(847/2048), (53/128), (63/128), (2017/4096)⟩,
  ⟨(53/128), (849/2048), (63/128), (2017/4096)⟩,
  ⟨(849/2048), (425/1024), (63/128), (2017/4096)⟩,
  ⟨(425/1024), (851/2048), (63/128), (2017/4096)⟩,
  ⟨(855/2048), (107/256), (2017/4096), (1009/2048)⟩,
  ⟨(107/256), (857/2048), (2017/4096), (1009/2048)⟩,
  ⟨(857/2048), (429/1024), (2017/4096), (1009/2048)⟩,
  ⟨(215/512), (861/2048), (1009/2048), (2019/4096)⟩,
  ⟨(863/2048), (27/64), (2019/4096), (505/1024)⟩,
  ⟨(433/1024), (867/2048), (505/1024), (2021/4096)⟩,
  ⟨(217/512), (869/2048), (2021/4096), (1011/2048)⟩,
  ⟨(893/2048), (447/1024), (2037/4096), (1019/2048)⟩,
  ⟨(225/512), (901/2048), (2043/4096), (511/1024)⟩
]

/-- Every generated coefficient and every shape guard is checked by Lean's kernel. -/
theorem exteriorBoxes_checked : exteriorBoxes.all exteriorBoxCheck = true := by
  decide +kernel

/-- Exact list equality binds the certificate to every actual current-exterior terminal. -/
theorem exteriorBoxes_binding :
    ((QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest).filter
      (fun leaf => leaf.route == .currentExterior)).map
      QRH.PhysicalCertificate.StoredLeaf.box = exteriorBoxes := by
  decide +kernel

/-- The generated physical checker covers all 47 actual current-exterior terminals. -/
theorem exteriorBoxes_length : exteriorBoxes.length = 47 := by decide

/-- Actual membership, rather than equality of a stored margin, selects the checked box. -/
theorem actual_exterior_box {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route = .currentExterior) : leaf.box ∈ exteriorBoxes := by
  rw [← exteriorBoxes_binding]
  apply List.mem_map.mpr
  refine ⟨leaf, List.mem_filter.mpr ⟨hm, ?_⟩, rfl⟩
  simp [hr]

/-- All directed h values have the generated cleared bound on every accepted rectangle. -/
theorem checked_cleared_bound {box : QRH.Coverage.Box}
    (hc : exteriorBoxCheck box = true) {h : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : box.Contains point) :
    1 / 50000000 ≤ clearedProxy h point.1 point.2 := by
  simp only [exteriorBoxCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨_, hu, _, _, hv, _⟩, hl, hh0⟩
  have hlow := generated_box_bound (8175840773 / 10000000000) box (1 / 50000000) hu hv hl hp
  have hhigh := generated_box_bound (8175840793 / 10000000000) box (1 / 50000000) hu hv hh0 hp
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hlow hhigh
  change (1 / 50000000 : ℝ) ≤ clearedProxy hLower point.1 point.2 at hlow
  change (1 / 50000000 : ℝ) ≤ clearedProxy hUpper point.1 point.2 at hhigh
  have hs := QRH.Bernstein.coordinate_mem_unit conductor_interval.2.1 hh hh'
  change 0 ≤ (h - hLower) / (hUpper - hLower) ∧
    (h - hLower) / (hUpper - hLower) ≤ 1 at hs
  rw [cleared_interpolation]
  have h0 := mul_le_mul_of_nonneg_left hlow (by linarith :
    0 ≤ 1 - (h - hLower) / (hUpper - hLower))
  have h1 := mul_le_mul_of_nonneg_left hhigh hs.1
  nlinarith

/-- A positive cleared Q1 margin implies a positive original physical top margin. -/
theorem top_price_of_cleared {h d p g₀ g₁ : ℝ}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000)
    (hm : 1 / 50000000 ≤ clearedProxy h d p) :
    1 / 125000000 ≤ theta - price h d p g₀ g₁ h := by
  have hh0 : 0 ≤ h := conductor_interval.1.le.trans hh
  have hc := actual_capacity_lower hh hh'
  have hr := count_upper hd hd' hp hp' hg₀ hg₀' hg₁ hg₁'
  have hj := admitted hd hd' hp hp' (by norm_num : (0 : ℝ) ≤ 5805911 / 100000000)
    (by norm_num : (5805911 / 100000000 : ℝ) ≤ 3 / 50)
    (by norm_num : (7 / 100 : ℝ) ≤ 379981 / 5000000)
    (by norm_num : (379981 / 5000000 : ℝ) ≤ 2 / 25)
  have he := pairedCount_clear_margin (d := d) (p := p)
    (g₀ := (5805911 / 100000000 : ℝ)) (g₁ := (379981 / 5000000 : ℝ))
    (target := theta) (base := baseProxy h d p) (h := h) (ne_of_gt hj.2.1)
  change clearedProxy h d p = _ at he
  have hproxy : 1 / 125000000 ≤
      theta - (baseProxy h d p + 3 * h * pairedCount d p
        (5805911 / 100000000) (379981 / 5000000) / 4) := by
    rw [he] at hm
    have hn := mul_le_mul_of_nonneg_left hj.2.2 (by norm_num : (0 : ℝ) ≤ 1 / 125000000)
    nlinarith
  have hcap := mul_le_mul_of_nonneg_left hc (mul_nonneg hd hp)
  have hcount := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 3 * h / 4)
  dsimp [price, baseProxy] at hproxy ⊢
  nlinarith

/-- The original Q1 price is monotone in conductor throughout the admitted leaf corridor. -/
theorem price_mono_conductor {h d p g₀ g₁ D : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000)
    (hDh : D ≤ h) : price h d p g₀ g₁ D ≤ price h d p g₀ g₁ h := by
  have ha := admitted hd hd' hp hp'
    (by linarith : 0 ≤ g₀) (by linarith : g₀ ≤ 3 / 50)
    (by linarith : 7 / 100 ≤ g₁) (by linarith : g₁ ≤ 2 / 25)
  have hr := pairedCount_lower hd (by linarith : d ≤ 5 / 6) ha.1 ha.2.1
  have hcap := cappedCapacity_increment_le physicalCap_admissible.1.le
    allowances_pos.1.le hDh (y := h - 2 * ell)
  have hsec := conductorPrice_secant_lower hd hp hp' hd'
    physicalCap_admissible.1.le hr hDh hcap
    (base := 1 / 2 + 13 * h / 75 - (h - 2 * ell) / 2 - ell / 2 + d / 2 + d * p * ell)
  rw [← price_eq_conductorPrice, ← price_eq_conductorPrice] at hsec
  have hs : 0 ≤ boxSlope (1 / 2) physicalCap := by norm_num [boxSlope, physicalCap]
  have hdiff := mul_nonneg hs (sub_nonneg.mpr hDh)
  linarith

/-- Every actual current-exterior leaf has the pointwise *original* physical-price surplus.
This theorem never reads any terminal's stored normalized or physical numerator. -/
theorem all_currentExterior_price {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route = .currentExterior) {h g₀ g₁ D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000)
    (hDh : D ≤ h) :
    1 / 125000000 ≤ theta - price h point.1 point.2 g₀ g₁ D := by
  have hc := List.all_eq_true.mp exteriorBoxes_checked leaf.box (actual_exterior_box hm hr)
  have hclear := checked_cleared_bound hc hh hh' hp
  have hshape := hc
  simp only [exteriorBoxCheck, Bool.and_eq_true, decide_eq_true_eq] at hshape
  have hd0 : (0 : ℝ) ≤ (leaf.box.uLo : ℝ) := Rat.cast_nonneg.mpr hshape.1.1
  have hd1 : (leaf.box.uHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hshape.1.2.2.1 : (leaf.box.uHi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
  have hp0 : (0 : ℝ) ≤ (leaf.box.vLo : ℝ) := Rat.cast_nonneg.mpr hshape.1.2.2.2.1
  have hp1 : (leaf.box.vHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hshape.1.2.2.2.2.2 : (leaf.box.vHi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
  have hd0' := hd0.trans hp.1
  have hd1' := hp.2.1.trans hd1
  have hp0' := hp0.trans hp.2.2.1
  have hp1' := hp.2.2.2.trans hp1
  have ht := top_price_of_cleared hh hh' hd0' hd1' hp0' hp1' hg₀ hg₀' hg₁ hg₁' hclear
  have hmono := price_mono_conductor hd0' hd1' hp0' hp1' hg₀ hg₀' hg₁ hg₁' hDh
  linarith

/-- The certified contact enclosure supplies the concrete outer bounds needed by Q1. -/
theorem actual_contact_bounds {x : ℝ}
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x) :
    5805911 / 100000000 ≤ QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x) ∧
    QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x) ≤ 5805913 / 100000000 ∧
    3799809 / 50000000 ≤ QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x) ∧
    QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x) ≤ 379981 / 5000000 := by
  have hg₀ := QRH.ContactCertificate.g0_enclosed hx
  have hg₁ := QRH.ContactCertificate.g1_enclosed hx
  have hb₀ := QRH.ContactCertificate.g0_directed_bounds
  have hb₁ := QRH.ContactCertificate.g1_directed_bounds
  have hlo₀ : (5805911 / 100000000 : ℝ) <
      (QRH.ContactCertificate.g0Interval.lo : ℝ) := by
    have hc : ((5805911 / 100000000 : ℚ) : ℝ) < _ := Rat.cast_lt.mpr hb₀.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hhi₀ : (QRH.ContactCertificate.g0Interval.hi : ℝ) <
      (5805913 / 100000000 : ℝ) := by
    have hc : (QRH.ContactCertificate.g0Interval.hi : ℝ) < ((5805913 / 100000000 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hb₀.2.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hlo₁ : (3799809 / 50000000 : ℝ) <
      (QRH.ContactCertificate.g1Interval.lo : ℝ) := by
    have hc : ((3799809 / 50000000 : ℚ) : ℝ) < _ := Rat.cast_lt.mpr hb₁.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hhi₁ : (QRH.ContactCertificate.g1Interval.hi : ℝ) <
      (379981 / 5000000 : ℝ) := by
    have hc : (QRH.ContactCertificate.g1Interval.hi : ℝ) < ((379981 / 5000000 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hb₁.2.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact ⟨hlo₀.le.trans hg₀.1, hg₀.2.trans hhi₀.le,
    hlo₁.le.trans hg₁.1, hg₁.2.trans hhi₁.le⟩

/-- All 47 actual current-exterior leaves have the original price bound at the certified contact. -/
theorem all_currentExterior_price_of_contact {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route = .currentExterior) {h x D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x)
    (hDh : D ≤ h) :
    1 / 125000000 ≤ theta - price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) D := by
  have hb := actual_contact_bounds hx
  exact all_currentExterior_price hm hr hh hh' hp hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hDh

/-- The actual forest has no old-exterior leaf; no historical old-price assumption is required here. -/
theorem no_oldExterior {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest) :
    leaf.route ≠ .oldExterior := by
  intro hr
  have hz := QRH.PhysicalCertificate.qForest_oldExterior
  unfold QRH.PhysicalCertificate.routeCount at hz
  have hn := List.countP_eq_zero.mp hz leaf hm
  simp [hr] at hn

/-- Every exterior leaf in the supplied Q forest is on the proved current branch. -/
theorem exterior_is_current {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route ≠ .mixed) : leaf.route = .currentExterior := by
  cases hh : leaf.route with
  | mixed => exact False.elim (hr hh)
  | currentExterior => rfl
  | oldExterior => exact False.elim (no_oldExterior hm hh)

/-- Every actual exterior terminal pays the original price, actual padding, and the outer-loss budget.
No stored terminal margin is a premise or an input to this theorem. Initial direct-return
routes and mixed terminals have their own formulas and are outside this result. -/
theorem all_exterior_padded_positive {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route ≠ .mixed) {h x D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x)
    (hDh : D ≤ h) :
    0 < theta - price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) D -
        paddingDebit - 1 / 100000000000000 := by
  have hm := all_currentExterior_price_of_contact hm (exterior_is_current hm hr) hh hh' hp hx hDh
  have hs := sourceCost_le_rowPad
  have hp := rowPad_small
  dsimp [paddingDebit]
  linarith

/-- Above h the actual minimum capacity can decrease by at most the conductor increment. -/
theorem capacity_drop_le {cap y s D h : ℝ}
    (hcap : 0 ≤ cap) (hs : 0 ≤ s) (hDh : h ≤ D) :
    cappedCapacity cap y s h - cappedCapacity cap y s D ≤ D - h := by
  have hden : 0 < 2 + 10 * s := by linarith
  have hh0 := min_le_left (cap * h) ((2 * y - (1 + s) * h) / (2 + 10 * s))
  have hh1 := min_le_right (cap * h) ((2 * y - (1 + s) * h) / (2 + 10 * s))
  have hh1' := (le_div_iff₀ hden).mp hh1
  have hgap := mul_nonneg hcap (sub_nonneg.mpr hDh)
  have hsgap := mul_nonneg hs (sub_nonneg.mpr hDh)
  have hlow : min (cap * h) ((2 * y - (1 + s) * h) / (2 + 10 * s)) - (D - h) ≤
      min (cap * D) ((2 * y - (1 + s) * D) / (2 + 10 * s)) := by
    apply le_min
    · linarith
    · apply (le_div_iff₀ hden).mpr
      nlinarith
  dsimp [cappedCapacity]
  linarith

/-- The same original paired count is at most one on the physical contact corridor. -/
theorem count_le_one {d p g₀ g₁ : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000) :
    pairedCount d p g₀ g₁ ≤ 1 := by
  have ha := admitted hd hd' hp hp'
    (by linarith : 0 ≤ g₀) (by linarith : g₀ ≤ 3 / 50)
    (by linarith : 7 / 100 ≤ g₁) (by linarith : g₁ ≤ 2 / 25)
  have hU1 : pairedU p g₀ g₁ ≤ 1 := by
    have hprod := mul_nonneg hp (by linarith : 0 ≤ 1 + 6 * g₀ - 4 * g₁)
    dsimp [pairedU]
    linarith
  have hv : 0 ≤ pairedV d := by dsimp [pairedV]; linarith
  have hk0 : 0 ≤ pairedK p g₁ := by
    have ht : 1 + 2 * g₁ ≤ 29 / 25 := by linarith
    have ht' := mul_le_mul_of_nonneg_left ht hp
    have ht'' := mul_le_mul_of_nonneg_right hp' (by norm_num : (0 : ℝ) ≤ 29 / 25)
    dsimp [pairedK]
    linarith
  have hjv : pairedV d ≤ pairedJ d p g₁ := by
    have hdk := mul_nonneg hd hk0
    dsimp [pairedJ]
    linarith
  have hvu := mul_le_mul_of_nonneg_left hU1 hv
  have hpay := mul_le_mul_of_nonneg_left (hvu.trans (by simpa using hjv)) hd
  apply (div_le_one ha.2.1).mpr
  have hid : pairedN d p g₀ g₁ =
      (1 - d) * pairedJ d p g₁ + d * (pairedV d * pairedU p g₀ g₁) := by
    dsimp [pairedN, pairedV]
    ring
  change pairedN d p g₀ g₁ ≤ pairedJ d p g₁
  rw [hid]
  nlinarith

/-- The full original Q1 price increases by at most the conductor increment above h. -/
theorem price_increment_le {h d p g₀ g₁ D : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000)
    (hDh : h ≤ D) : price h d p g₀ g₁ D - price h d p g₀ g₁ h ≤ D - h := by
  have hcap := capacity_drop_le physicalCap_admissible.1.le allowances_pos.1.le
    hDh (y := h - 2 * ell)
  have hdp : d * p ≤ 1 / 4 := by
    have hp1 := mul_le_mul_of_nonneg_left hp' hd
    linarith
  have hdp0 := mul_nonneg hd hp
  have hpay := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ d * p / 2)
  have hdp1 := mul_le_mul_of_nonneg_right hdp (sub_nonneg.mpr hDh)
  have hr := count_le_one hd hd' hp hp' hg₀ hg₀' hg₁ hg₁'
  have hr1 := mul_le_mul_of_nonneg_right hr (sub_nonneg.mpr hDh)
  dsimp [price]
  nlinarith

/-- All 47 actual exterior leaves remain physically paid through the actual padded support.
This uses the original price at D itself, including when h < D ≤ h + rowPad. -/
theorem all_exterior_padded_support_positive {leaf : QRH.PhysicalCertificate.StoredLeaf}
    (hm : leaf ∈ QRH.PhysicalCertificate.forestRecords QRH.PhysicalCertificate.qForest)
    (hr : leaf.route ≠ .mixed) {h x D : ℝ} {point : QRH.Coverage.Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hx : QRH.RationalInterval.Contains QRH.ContactCertificate.alphaInterval x)
    (hDh : D ≤ h + rowPad) :
    0 < theta - price h point.1 point.2
      (QRH.ContactCertificate.g0 (QRH.ContactCertificate.wValue x))
      (QRH.ContactCertificate.g1 (QRH.ContactCertificate.wValue x)) D -
        paddingDebit - 1 / 100000000000000 := by
  by_cases hle : D ≤ h
  · exact all_exterior_padded_positive hm hr hh hh' hp hx hle
  have hc := List.all_eq_true.mp exteriorBoxes_checked leaf.box
    (actual_exterior_box hm (exterior_is_current hm hr))
  simp only [exteriorBoxCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hd0 : (0 : ℝ) ≤ (leaf.box.uLo : ℝ) := Rat.cast_nonneg.mpr hc.1.1
  have hd1 : (leaf.box.uHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.1 : (leaf.box.uHi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
  have hp0 : (0 : ℝ) ≤ (leaf.box.vLo : ℝ) := Rat.cast_nonneg.mpr hc.1.2.2.2.1
  have hp1 : (leaf.box.vHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hc.1.2.2.2.2.2 : (leaf.box.vHi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
  have hb := actual_contact_bounds hx
  have ht := all_currentExterior_price_of_contact hm (exterior_is_current hm hr)
    hh hh' hp hx (le_refl h)
  have hinc := price_increment_le (hd0.trans hp.1) (hp.2.1.trans hd1)
    (hp0.trans hp.2.2.1) (hp.2.2.2.trans hp1) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
    (le_of_not_ge hle)
  have hs := sourceCost_le_rowPad
  have hp := rowPad_small
  dsimp [paddingDebit]
  linarith


/-!
Whole-slot selection and damping adapted from Joseph Bebel's Apache-2.0
`PositiveSelection.lean`, supplied in `evidence/upstream-contracts`, itself
adapted from PR137 physical Geometry by Sil and predecessor authors (Apache-2.0).
Here y is explicit and the physical cap is the actual Q cap 17/200; no
Geometry.Parameters instance or historical numerical geometry is imported.
-/
namespace Selection
open scoped BigOperators

/-- The actual unmarked whole-slot scale, with the geometric length explicit. -/
def plainScale (y d t : ℝ) : ℝ := 1 - y / d + t

/-- The normalized affine source face, preserving the full two-times shift. -/
def affineCapacity (y s d t : ℝ) : ℝ :=
  (1 - s - 2 * plainScale y d t) / (2 + 10 * s)

/-- The normalized capacity clipped at the actual physical source cap 17/200. -/
def clippedCapacity (y s d t : ℝ) : ℝ := min physicalCap (affineCapacity y s d t)

/-- A possibly empty whole-slot selection uses the nonnegative scheduled face. -/
def scheduledCapacity (y s d v : ℝ) : ℝ := max 0 (clippedCapacity y s d (v / 2))

/-- The unshifted normalized capacity, before taking a positive part. -/
def zeroCapacity (y s d : ℝ) : ℝ := clippedCapacity y s d 0

/-- A nonempty actual whole-slot selection obeys its original affine source face.
No positive minimum slot width or geometry typeclass is assumed. -/
theorem selected_admissible_or_empty {α : Type*} (T : Finset α) (width : T → ℝ)
    {y s d t : ℝ} (hs : 0 ≤ s) (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity y s d (2 * t)) :
    (2 * plainScale y d t + (2 + 10 * s) * (∑ i, width i) ≤ 1 - s ∧
      (∑ i, width i) ≤ physicalCap) ∨ T = ∅ := by
  by_cases hT : T = ∅
  · exact Or.inr hT
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hne : (Finset.univ : Finset T).Nonempty := ⟨⟨i, hi⟩, Finset.mem_univ _⟩
    have hpos : 0 < ∑ i, width i := Finset.sum_pos (fun i _ => hw i) hne
    have hsel : (∑ i, width i) ≤ max 0 (clippedCapacity y s d t) := by
      simpa only [scheduledCapacity, show 2 * t / 2 = t by ring] using hselected
    have hc : 0 ≤ clippedCapacity y s d t := by
      by_contra hn
      rw [max_eq_left (le_of_not_ge hn)] at hsel
      linarith
    rw [max_eq_right hc] at hsel
    have hcap := hsel.trans (min_le_left physicalCap (affineCapacity y s d t))
    have ha := hsel.trans (min_le_right physicalCap (affineCapacity y s d t))
    have hden : 0 < 2 + 10 * s := by positivity
    have hm := (le_div_iff₀ hden).mp ha
    exact Or.inl ⟨by linarith, hcap⟩

/-- Exact conversion from normalized whole-slot capacity to the original Q1 capacity.
The full shift is 2*d*t in the physical numerator. -/
theorem scaled_clipped_capacity {y s d t : ℝ} (hd : 0 < d) :
    d * clippedCapacity y s d t = cappedCapacity physicalCap (y - d * t) s d := by
  unfold clippedCapacity cappedCapacity
  rw [mul_min_of_nonneg _ _ hd.le]
  congr 1
  · ring
  · unfold affineCapacity plainScale
    field_simp
    ring

/-- At zero shift, normalized selection capacity is exactly the capacity used by Q1. -/
theorem scaled_zero_capacity {y s d : ℝ} (hd : 0 < d) :
    d * zeroCapacity y s d = cappedCapacity physicalCap y s d := by
  simpa only [zeroCapacity, mul_zero, sub_zero] using
    (scaled_clipped_capacity (y := y) (s := s) (t := 0) hd)

/-- Scheduling v/2 retains the full v conductor debit after converting to original units. -/
theorem scaled_scheduled_capacity {y s d v : ℝ} (hd : 0 < d) :
    d * scheduledCapacity y s d v =
      max 0 (cappedCapacity physicalCap (y - d * v / 2) s d) := by
  unfold scheduledCapacity
  rw [mul_max_of_nonneg _ _ hd.le, mul_zero, scaled_clipped_capacity hd]
  congr 2
  ring

/-- A nonempty selected set is paid by the original capped physical capacity. -/
theorem selected_physical_capacity_or_empty {α : Type*} (T : Finset α) (width : T → ℝ)
    {y s d t : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hw : ∀ i, 0 < width i)
    (hselected : (∑ i, width i) ≤ scheduledCapacity y s d (2 * t)) :
    d * (∑ i, width i) ≤ cappedCapacity physicalCap (y - d * t) s d ∨ T = ∅ := by
  rcases selected_admissible_or_empty T width hs hw hselected with h | h
  · left
    have ha : (∑ i, width i) ≤ affineCapacity y s d t := by
      apply (le_div_iff₀ (by positivity : 0 < 2 + 10 * s)).mpr
      linarith [h.1]
    have hc : (∑ i, width i) ≤ clippedCapacity y s d t := le_min h.2 ha
    have hm := mul_le_mul_of_nonneg_left hc hd.le
    simpa only [scaled_clipped_capacity hd] using hm
  · exact Or.inr h

/-- Clipping a pair of faces cannot enlarge their nonnegative separation. -/
theorem min_difference_le (c u v : ℝ) (hvu : v ≤ u) :
    min c u - min c v ≤ u - v := by
  by_cases hcv : c ≤ v
  · rw [min_eq_left (hcv.trans hvu), min_eq_left hcv]
    linarith
  · rw [min_eq_right (le_of_not_ge hcv)]
    exact sub_le_sub_right (min_le_right c u) v

/-- The literal two-times shift loses no more than 2*t/(2+10*s) normalized capacity. -/
theorem clipped_shift_loss {y s d t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    zeroCapacity y s d - clippedCapacity y s d t ≤ 2 * t / (2 + 10 * s) := by
  have hden : 0 < 2 + 10 * s := by positivity
  have hface : affineCapacity y s d t ≤ affineCapacity y s d 0 := by
    unfold affineCapacity plainScale
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  have hm := min_difference_le physicalCap _ _ hface
  unfold zeroCapacity clippedCapacity
  calc
    _ ≤ affineCapacity y s d 0 - affineCapacity y s d t := hm
    _ = 2 * t / (2 + 10 * s) := by unfold affineCapacity plainScale; ring

/-- The complete actual shift debit has strictly positive damping 1/1000.
The source face and the factor two in the scheduled conductor dilation are retained. -/
theorem capacity_damping {y s d v a delta : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (had : a ≤ delta / 2) (hdelta : 0 ≤ delta) :
    a * zeroCapacity y s d / 2 + (1 / 1000) * delta * v ≤
      delta * v / 4 + a * scheduledCapacity y s d v / 2 := by
  have hloss := clipped_shift_loss hs (by linarith : 0 ≤ v / 2) (y := y) (d := d)
  have hden : 0 < 2 + 10 * s := by positivity
  have hdiv : 2 * (v / 2) / (2 + 10 * s) ≤ v / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hs hv]
  have hscheduled : clippedCapacity y s d (v / 2) ≤ scheduledCapacity y s d v :=
    le_max_right _ _
  have hdrop : zeroCapacity y s d - scheduledCapacity y s d v ≤ v / 2 := by linarith
  have hpay := mul_le_mul_of_nonneg_left hdrop ha
  have hamp := mul_le_mul_of_nonneg_right had hv
  have hnonneg := mul_nonneg hdelta hv
  nlinarith

end Selection

end
end QRH.Cycle092.Physical

#print axioms QRH.Cycle092.Physical.all_exterior_padded_support_positive
#print axioms QRH.Cycle092.Physical.exteriorBoxes_binding
#print axioms QRH.Cycle092.Physical.exteriorBoxes_checked
#print axioms QRH.Cycle092.Physical.generated_expansion

#print axioms QRH.Cycle092.Physical.Selection.selected_admissible_or_empty
#print axioms QRH.Cycle092.Physical.Selection.scaled_zero_capacity
#print axioms QRH.Cycle092.Physical.Selection.scaled_scheduled_capacity
#print axioms QRH.Cycle092.Physical.Selection.selected_physical_capacity_or_empty
#print axioms QRH.Cycle092.Physical.Selection.capacity_damping
