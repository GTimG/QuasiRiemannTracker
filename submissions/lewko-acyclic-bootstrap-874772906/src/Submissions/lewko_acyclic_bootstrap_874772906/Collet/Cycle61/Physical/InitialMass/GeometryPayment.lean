import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.Normalization

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
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

/-- The coordinates are c,d,p,R,E, all taken from the actual first label. -/
def leftExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 0+v 3+v 4+max (3*v 0-5*v 1-v 3) 0/6

def rightExponent (A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  v 2+A-v 1+v 3+v 4+max (3*v 1-5*v 0-v 3) 0/6

def outsideExponent (M A : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  M-A-v 3/2-v 4

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

/-- The left scalar is kept inside its square sum. Cross-label products
within one geometry bin lose at most five bin widths in their exponent. -/
lemma cross_exponent_payment (v u r : Fin 5 → ℝ) (M A w : ℝ) (hw : 0≤w)
    (hv : ∀i, v i-u i≤w ∧ u i-v i≤w)
    (hr : ∀i, r i-u i≤w ∧ u i-r i≤w)
    (hbase : outsideExponent M A u+(leftExponent A u+rightExponent A u)/2≤M) :
    outsideExponent M A v+(leftExponent A v+rightExponent A r)/2≤M+5*w := by
  have hl := allowance_variation v u w hw hv 0 1
  have hr' := allowance_variation r u w hw hr 1 0
  have hleft : 2*outsideExponent M A v+leftExponent A v ≤
      2*outsideExponent M A u+leftExponent A u+9*w/2 := by
    dsimp [outsideExponent,leftExponent]
    linarith [(hv 2).1,(hv 0).2,(hv 4).2]
  have hright : rightExponent A r≤rightExponent A u+11*w/2 := by
    dsimp [rightExponent]
    linarith [(hr 2).1,(hr 1).2,(hr 3).1,(hr 4).1]
  linarith

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
/-- The single-label balance is used only after the five arithmetic
coordinates have been frozen to one common bin. -/
lemma actual_geometry_balance (s : Input ι) (R seed : Ideal O) (K Z ξ M A : ℝ)
    (hZ : 1<Z) (q : FirstSourceCoordinate s R seed K Z ξ) :
    outsideExponent M A (geometryExponents s R seed K Z ξ q)+
      (leftExponent A (geometryExponents s R seed K Z ξ q)+
       rightExponent A (geometryExponents s R seed K Z ξ q))/2≤M := by
  have hsup : CanonicalQuadraticSieve.Supported q.1.val.1 ∧
      CanonicalQuadraticSieve.Supported q.1.val.2 := CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) q.1.val.1 q.1.val.2 q.1.property
  have hc := actual_labels_commonPart s R seed K Z ξ q
  have hh := Cycle61.Physical.actual_joint_side_exponent q.1.val.1 q.1.val.2 hsup.1 hsup.2
    Z M A (geometryExponents s R seed K Z ξ q 4) hZ
  dsimp only at hh
  rw [hc.1,hc.2] at hh
  change outsideExponent M A (geometryExponents s R seed K Z ξ q)+
    (leftExponent A (geometryExponents s R seed K Z ξ q)+
      rightExponent A (geometryExponents s R seed K Z ξ q))/2≤M at hh
  exact hh

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
        32*Z^M := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  have hdiff := actual_geometry_fiber_difference s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key
  have he := cross_exponent_payment
    (geometryExponents s R seed K Z ξ q.val)
    (geometryExponents s R seed K Z ξ q.val)
    (geometryExponents s R seed K Z ξ r.val) M A (Real.logb Z 2) hw
    (fun i => ⟨by simpa using hw,by simpa using hw⟩)
    (fun i => ⟨hdiff r q i,hdiff q r i⟩)
    (actual_geometry_balance s R seed K Z ξ M A hZ q.val)
  have hp : Z^(M+5*Real.logb Z 2)=32*Z^M := by
    rw [Real.rpow_add hz,show 5*Real.logb Z 2=Real.logb Z 2*5 by ring,
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
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
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

omit [DecidableEq ι] in
/-- The actual first scalar stays on the left of joint Cauchy. Normalized
left and right energies are still summed over every label in the bin. -/
theorem actual_geometry_joint_energy {I J : Type*} [Fintype I] [Fintype J] (s : Input ι) (R seed : Ideal O)
    (K Z ξ B M A : ℝ) (hZ : 1<Z) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤Z^B)
    (key : ℤ×(Fin 5→ℤ))
    (left : I→CommonGeometryFiber s R seed K Z ξ key)
    (right : J→CommonGeometryFiber s R seed K Z ξ key) (L : I→ℝ) (N : J→ℝ)
    (hL : ∀q,0≤L q) (hN : ∀q,0≤N q) :
    Real.sqrt (∑q,Z^(2*outsideExponent M A (geometryExponents s R seed K Z ξ (left q).val)+
        leftExponent A (geometryExponents s R seed K Z ξ (left q).val))*L q)*
      Real.sqrt (∑q,Z^(rightExponent A (geometryExponents s R seed K Z ξ (right q).val))*N q) ≤
        32*Z^M*Real.sqrt (∑q,L q)*Real.sqrt (∑q,N q) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  apply weighted_joint_energy _ _ _ _ _ (fun _=>Real.rpow_nonneg hz.le _)
    (fun _=>Real.rpow_nonneg hz.le _) hL hN (by positivity)
  intro q r
  have hh := actual_geometry_cross_payment s R seed K Z ξ B M A hZ hs hz₁ hz₂ hsource key (left q) (right r)
  have hsquared := pow_le_pow_left₀ (by positivity) hh 2
  rw [mul_pow,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hz.le _),
    Real.sq_sqrt (Real.rpow_nonneg hz.le _),←Real.rpow_mul_natCast hz.le,
    ←Real.rpow_add hz] at hsquared
  convert hsquared using 1
  congr 2
  ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_cross_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_joint_energy
