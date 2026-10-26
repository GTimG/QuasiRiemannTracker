import Candidate.Cycle63.Physical.InitialMass.SecondLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowReciprocal

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle63Moment Cycle63FinalCapacity
local notation "O" => HeckeFamily.O

def lowGeometryExponent (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) : ℝ :=
  A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
    Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)

/-- The exact low payment leaves a one-sided reciprocal ideal norm, which
can be summed inside each of the two separate joint Cauchy energies. -/
theorem actual_low_scalar_reciprocal (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve error : ℝ)(hZ : 1<Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error)=
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then D₂ else C₂).absNorm:ℝ) := by
  have hh := actual_low_scalar_payment reflected second l hC hD heq C₂ D₂ hC₂ U
    Z M A a ξ reserve error hZ
  dsimp only at hh ⊢
  rw [hh]
  have hn : (0:ℝ)<(if second then D₂ else C₂).absNorm := by
    cases second
    · exact CenteredMomentFirstScale.norm_pos C₂ hC₂.1
    · exact CenteredMomentFirstScale.norm_pos D₂ hD₂.1
  rw [show (A-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
      Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)+error)=
      (lowGeometryExponent reflected Z A l+error)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) by unfold lowGeometryExponent; ring]
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn]

/-- Sum the one-sided low weights over second labels and the first
projector shell, then pay the first-label count once. -/
theorem actual_low_full_label_budget (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(reflected second : Bool)(Z T A p exponent error : ℝ),
      2≤Z → 1≤T → p≤B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z A l≤exponent) →
      ∀(Ds : FirstSourceLabel→Finset (Ideal O))
        (children : FirstSourceLabel→Ideal O→Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑l∈labels,∑D∈Ds l,∑v∈children l D,
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
          K*Z^(p+exponent+error+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨Kf,hKf,hfirst⟩ := actual_first_low_label_count B (ε/2) hB (half_pos hε)
  obtain ⟨Ks,hKs,hsecond⟩ := actual_low_reciprocal_projector_shell B (ε/2) hB (half_pos hε)
  refine ⟨Kf*Ks,mul_pos hKf hKs,?_⟩
  intro reflected second Z T A p exponent error hZ hT hp seed hs hs0 labels
    hsup heq hseed hnorm hrad hgeom Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hZ1 : 1≤Z := by linarith
  have hZ0 : 0<Z := by linarith
  have hc := hfirst Z hZ1 p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpoint (l : FirstSourceLabel)(hl : l∈labels) :
      (∑D∈Ds l,∑v∈children l D,
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
        Z^(exponent+error)*(Ks*Z^(ε/2)) := by
    have hh := hsecond second Z T hZ hT (Ds l) (hDs l hl) (hdyad l hl) (children l)
      (hsup₂ l hl) (heq₂ l hl) (hseed₂ l hl) (hnorm₂ l hl)
    calc
      _=Z^(lowGeometryExponent reflected Z A l+error)*
          (∑D∈Ds l,∑v∈children l D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
        simp only [Finset.mul_sum,mul_one_div]
      _≤Z^(exponent+error)*(Ks*Z^(ε/2)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [hgeom l hl])) hh
        (by positivity) (by positivity)
  calc
    _≤∑_l∈labels,Z^(exponent+error)*(Ks*Z^(ε/2)) := Finset.sum_le_sum hpoint
    _=(labels.card:ℝ)*(Z^(exponent+error)*(Ks*Z^(ε/2))) := by simp
    _≤(Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Z^(exponent+error)*(Ks*Z^(ε/2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by
      have hsplit : Z^ε=Z^(ε/2)*Z^(ε/2) := by
        rw [←Real.rpow_add hZ0,add_halves]
      simp only [Real.rpow_add hZ0]
      rw [hsplit]
      ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_low_scalar_reciprocal
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_low_full_label_budget
