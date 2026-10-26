import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryBins
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.Normalization
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
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

/-- The surplus of the coordinates `c, d, p, R, E` (`v 0` to `v 4`) of a first label: half of
`c + d - R - 2p` less the two side penalties. Every actual label has a nonnegative surplus
(`actual_geometry_surplus_nonneg`). -/
def geometrySurplus (v : Fin 5 → ℝ) : ℝ :=
  (v 0+v 1-v 3-2*v 2-max (3*v 0-5*v 1-v 3) 0/6-max (3*v 1-5*v 0-v 3) 0/6)/2

/-- The side exponents of the actual first label keep its surplus, so that the outside exponent and
the two sides balance exactly (`geometry_balance`): the balanced source energy of tracker PR #63
(Zhongpai Gao, `Target830/Kernel/BalancedGeometry.lean`). -/
def leftExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 0+v 3+v 4+max (3*v 0-5*v 1-v 3) 0/6+geometrySurplus v

def rightExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 1+v 3+v 4+max (3*v 1-5*v 0-v 3) 0/6+geometrySurplus v

def outsideExponent (M A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  M-A-v 3/2-v 4

theorem geometry_balance (M A : ℝ) (v : Fin 5 → ℝ) :
    outsideExponent M A v+(leftExponent A v+rightExponent A v)/2=M := by
  unfold outsideExponent leftExponent rightExponent geometrySurplus
  ring

lemma allowance_variation (v u : Fin 5 → ℝ) (w : ℝ) (hw : 0≤w)
    (hd : ∀i, v i-u i≤w ∧ u i-v i≤w) (i j : Fin 5) :
    max (3*v i-5*v j-v 3) 0/6 ≤ max (3*u i-5*u j-u 3) 0/6+3*w/2 := by
  have hmax : max (3*v i-5*v j-v 3) 0 ≤ max (3*u i-5*u j-u 3) 0+9*w := by
    apply max_le
    · have hh := le_max_left (3*u i-5*u j-u 3) (0:ℝ)
      linarith [(hd i).1,(hd j).2,(hd 3).2]
    · have hh := le_max_right (3*u i-5*u j-u 3) (0:ℝ)
      linarith
  linarith

/-- Cross-label products within one geometry bin lose at most two bin widths in their exponent: the
right exponent, `A + (c - d)/2 + R/2 + E` plus half the difference of the side penalties, moves by at
most four. -/
lemma cross_exponent_payment (v r : Fin 5 → ℝ) (M A w : ℝ) (hw : 0≤w)
    (hr : ∀i, r i-v i≤w ∧ v i-r i≤w) :
    outsideExponent M A v+(leftExponent A v+rightExponent A r)/2≤M+2*w := by
  have hd := allowance_variation r v w hw hr 1 0
  have hc := allowance_variation v r w hw (fun i => ⟨(hr i).2,(hr i).1⟩) 0 1
  have hb := geometry_balance M A v
  unfold outsideExponent leftExponent rightExponent geometrySurplus at *
  linarith [(hr 0).1,(hr 0).2,(hr 1).1,(hr 1).2,(hr 3).1,(hr 3).2,(hr 4).1,(hr 4).2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryPaymentSumDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma actual_geometry_fiber_difference (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1<Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (key : ℤ×(Fin 5→ℤ))
    (q r : CommonGeometryFiber s R seed K Z ξ key) (i : Fin 5) :
    geometryExponents s R seed K Z ξ q.val i-geometryExponents s R seed K Z ξ r.val i≤
      Real.logb Z 2 := by
  have hq := actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key q i
  have hr := actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key r i
  nlinarith

omit [DecidableEq ι] in
/-- Every actual label has a nonnegative surplus, by the extracted common-support allowance. -/
lemma actual_geometry_surplus_nonneg (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (hZ : 1<Z) (q : FirstSourceCoordinate s R seed K Z ξ) :
    0≤geometrySurplus (geometryExponents s R seed K Z ξ q) := by
  have hsup : CanonicalQuadraticSieve.Supported q.1.val.1 ∧
      CanonicalQuadraticSieve.Supported q.1.val.2 := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) q.1.val.1 q.1.val.2 q.1.property
  have hc := actual_labels_commonPart s R seed K Z ξ q
  have hh := Cycle63.Physical.actual_joint_side_exponent q.1.val.1 q.1.val.2 hsup.1 hsup.2
    Z 0 0 (geometryExponents s R seed K Z ξ q 4) hZ
  dsimp only at hh
  rw [hc.1,hc.2] at hh
  set v := geometryExponents s R seed K Z ξ q
  change 0-0-v 3/2-v 4+((v 2+0-v 0+v 3+v 4+max (3*v 0-5*v 1-v 3) 0/6)+
    (v 2+0-v 1+v 3+v 4+max (3*v 1-5*v 0-v 3) 0/6))/2≤0 at hh
  unfold geometrySurplus
  linarith

omit [DecidableEq ι] in
/-- Uniform cross-label payment. The left and right labels may differ;
no sum of per-label Cauchy estimates is substituted for joint Cauchy. -/
theorem actual_geometry_cross_payment (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q r : CommonGeometryFiber s R seed K Z ξ key) :
    Z^(outsideExponent M A (geometryExponents s R seed K Z ξ q.val))*
      Real.sqrt (Z^(leftExponent A (geometryExponents s R seed K Z ξ q.val)))*
      Real.sqrt (Z^(rightExponent A (geometryExponents s R seed K Z ξ r.val))) ≤
        4*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := cross_exponent_payment
    (geometryExponents s R seed K Z ξ q.val)
    (geometryExponents s R seed K Z ξ r.val) M A (Real.logb Z 2) hw
    (fun i => ⟨hdiff r q i,hdiff q r i⟩)
  have hp : Z^(M+2*Real.logb Z 2)=4*Z^M := by
    rw [Real.rpow_add hz,show 2*Real.logb Z 2=Real.logb Z 2*2 by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [←hp]
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

/-- Pairwise control of the geometric weights pays the product of the two
whole energy sums. There is no cardinality loss for either finite family. -/
lemma weighted_joint_energy {I J : Type*} [Fintype I] [Fintype J]
    (p L : I→ℝ) (q R : J→ℝ) (C : ℝ)
    (hp : ∀i,0≤p i) (hq : ∀j,0≤q j) (hL : ∀i,0≤L i) (hR : ∀j,0≤R j)
    (hC : 0≤C) (hpair : ∀i j,p i*q j≤C^2) :
    Real.sqrt (∑i,p i*L i)*Real.sqrt (∑j,q j*R j) ≤
      C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j) := by
  have hb : (∑i,p i*L i)*(∑j,q j*R j)≤C^2*(∑i,L i)*(∑j,R j) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hh := mul_le_mul_of_nonneg_right (hpair j i) (mul_nonneg (hL j) (hR i))
    nlinarith only [hh]
  have hl₀ : 0≤∑i,L i := Finset.sum_nonneg (fun i _=>hL i)
  have hr₀ : 0≤∑j,R j := Finset.sum_nonneg (fun j _=>hR j)
  have hl₁ : 0≤∑i,p i*L i := Finset.sum_nonneg (fun i _=>mul_nonneg (hp i) (hL i))
  have hr₁ : 0≤∑j,q j*R j := Finset.sum_nonneg (fun j _=>mul_nonneg (hq j) (hR j))
  have hs₁ : (Real.sqrt (∑i,p i*L i)*Real.sqrt (∑j,q j*R j))^2=
      (∑i,p i*L i)*(∑j,q j*R j) := by
    rw [mul_pow,Real.sq_sqrt hl₁,Real.sq_sqrt hr₁]
  have hs₀ : (C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j))^2=
      C^2*(∑i,L i)*(∑j,R j) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hl₀,Real.sq_sqrt hr₀]
  have hnonneg : 0≤C*Real.sqrt (∑i,L i)*Real.sqrt (∑j,R j) := by positivity
  nlinarith only [hb,hs₁,hs₀,hnonneg]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
