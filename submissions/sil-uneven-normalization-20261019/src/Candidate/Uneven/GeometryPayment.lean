import Candidate.Target830.Kernel.BalancedGeometry
import Candidate.Uneven.SkewCone
import Candidate.Cycle63.Physical.InitialMass.GeometryPayment
import Candidate.Target830.Source.BalancedPayment
import Candidate.Cycle63.Physical.InitialMass.Normalization

/- Original module: Candidate.Uneven.SkewGeometry. -/
section

/- Copyright (c) 2026 Sil. Apache-2.0.
   Extends PR63's balanced source geometry; inherited declarations are unchanged.
   Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
namespace Sil.Uneven.Geometry
noncomputable section
open QRH830.BalancedGeometry

def left (a c d r e p : ℝ) : ℝ :=
  QRH830.BalancedGeometry.left a c d r e + SkewNormalization.skew c d r p

def right (a c d r e p : ℝ) : ℝ :=
  QRH830.BalancedGeometry.right a c d r e - SkewNormalization.skew c d r p




theorem allocations_nonnegative {c d r p : ℝ} (hs : 0 ≤ surplus c d r p) :
    0 ≤ surplus c d r p + SkewNormalization.skew c d r p ∧
    0 ≤ surplus c d r p - SkewNormalization.skew c d r p := by
  exact SkewNormalization.allocations_nonnegative (r := (d-c)/10) hs

theorem budget (m a c d r e p : ℝ) :
    outer m a r e + (left a c d r e p + right a c d r e p)/2 = m := by
  unfold left right
  linarith only [QRH830.BalancedGeometry.balanced_budget m a c d r e]


theorem right_bin_bound {a c d r e p c' d' r' e' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) (hp : |p'-p| ≤ w) :
    |right a c' d' r' e' p' - right a c d r e p| ≤ 41*w/5 := by
  have hb := QRH830.BalancedGeometry.right_bin_bound (a := a) hc hd hr he
  have ht := SkewNormalization.skew_lipschitz hc hd hr hp
  rcases abs_le.mp hb with ⟨hb0, hb1⟩
  rcases abs_le.mp ht with ⟨ht0, ht1⟩
  rw [abs_le]
  unfold right
  constructor <;> linarith only [hb0, hb1, ht0, ht1]

theorem cross_label_budget {m a c d r e p c' d' r' e' p' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) (hp : |p'-p| ≤ w) :
    outer m a r e + (left a c d r e p + right a c' d' r' e' p')/2 ≤
      m + 41*w/10 := by
  have hb := (abs_le.mp (right_bin_bound (a := a) hc hd hr he hp)).2
  have h := budget m a c d r e p
  linarith only [hb, h]

end
end Sil.Uneven.Geometry
end

/- Original module: Candidate.Uneven.GeometryPayment. -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Target830.Source.Uneven
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

open Cycle63InitialMass

def skew (v : Fin 5 → ℝ) : ℝ :=
  SkewNormalization.skew (v 0) (v 1) (v 3) (v 2)

def unevenLeft (A : ℝ) (v : Fin 5 → ℝ) : ℝ := balancedLeft A v+skew v
def unevenRight (A : ℝ) (v : Fin 5 → ℝ) : ℝ := balancedRight A v-skew v
def allocation (reflected : Bool) (v : Fin 5 → ℝ) : ℝ :=
  surplus v + if reflected then -skew v else skew v

theorem allocation_nonneg (reflected : Bool) (v : Fin 5 → ℝ) (hs : 0 ≤ surplus v) :
    0 ≤ allocation reflected v := by
  have hh := Sil.Uneven.Geometry.allocations_nonnegative hs
  cases reflected <;> dsimp [allocation,skew,surplus] at * <;> linarith only [hh.1,hh.2]

theorem left_eq_old (A : ℝ) (v : Fin 5 → ℝ) :
    unevenLeft A v=Cycle63InitialMass.leftExponent A v+allocation false v := by
  rw [unevenLeft,Source.left_eq_old]
  simp only [allocation,Bool.false_eq_true,ite_false]
  ring

theorem right_eq_old (A : ℝ) (v : Fin 5 → ℝ) :
    unevenRight A v=Cycle63InitialMass.rightExponent A v+allocation true v := by
  rw [unevenRight,Source.right_eq_old]
  simp only [allocation,ite_true]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_allocation_nonneg (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hZ : 1<Z) (q : FirstSourceCoordinate s R seed K Z ξ) :
    0 ≤ allocation reflected (geometryExponents s R seed K Z ξ q) := by
  exact allocation_nonneg reflected _ (actual_surplus_nonneg s R seed K Z ξ hZ q)

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_uneven_cross_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s R seed K Z ξ q.val))*
      Real.sqrt (Z^(unevenLeft A (geometryExponents s R seed K Z ξ q.val)))*
      Real.sqrt (Z^(unevenRight A (geometryExponents s R seed K Z ξ r.val))) ≤
        32*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤ Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := Sil.Uneven.Geometry.cross_label_budget
    (m := M) (a := A)
    (c := geometryExponents s R seed K Z ξ q.val 0)
    (d := geometryExponents s R seed K Z ξ q.val 1)
    (r := geometryExponents s R seed K Z ξ q.val 3)
    (e := geometryExponents s R seed K Z ξ q.val 4)
    (c' := geometryExponents s R seed K Z ξ r.val 0)
    (d' := geometryExponents s R seed K Z ξ r.val 1)
    (r' := geometryExponents s R seed K Z ξ r.val 3)
    (e' := geometryExponents s R seed K Z ξ r.val 4)
    (p := geometryExponents s R seed K Z ξ q.val 2)
    (p' := geometryExponents s R seed K Z ξ r.val 2)
    (w := Real.logb Z 2)
    (abs_le.mpr ⟨by linarith [hdiff q r 0],hdiff r q 0⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 1],hdiff r q 1⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 3],hdiff r q 3⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 4],hdiff r q 4⟩)
    (abs_le.mpr ⟨by linarith [hdiff q r 2],hdiff r q 2⟩)
  change outsideExponent M A (geometryExponents s R seed K Z ξ q.val)+
    (unevenLeft A (geometryExponents s R seed K Z ξ q.val)+
      unevenRight A (geometryExponents s R seed K Z ξ r.val))/2≤ M+41*Real.logb Z 2/10 at he
  have hp : Z^(M+5*Real.logb Z 2)=32*Z^M := by
    rw [Real.rpow_add hz,show 5*Real.logb Z 2=Real.logb Z 2*5 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith


omit [DecidableEq ι] in

end
end OAI.SevenEighths.Target830.Source.Uneven
end
