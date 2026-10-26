import Candidate.Cycle63.Physical.InitialMass.SecondChildLowPayment

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle63Moment Cycle63FinalCapacity CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Actual child scalar costs are summed over the full first/second label
and projector shell, with no squarefree restriction on either ideal label. -/
theorem eventual_actual_geometry_low_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤s.lower →
      ∀(reflected second : Bool)(T p exponent error εcommon M a ξ reserve : ℝ),
      0≤εcommon → 1≤T → p≤B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
      ∀(Ds : FirstSourceLabel→Finset (Ideal O))
        (children : FirstSourceLabel→Ideal O→Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      ∀Rfirst : Ideal O,
      ∀alloc : (l : FirstSourceLabel)→(D : Ideal O)→(v : FirstSourceLabel)→
        actualAllocations s.pools (if reflected then l.1.2 else l.1.1),
      ∀(χ : FirstSourceLabel→Ideal O→FirstSourceLabel→Character)
        (t : FirstSourceLabel→Ideal O→FirstSourceLabel→ℝ),
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,
        frozenCoefficient (alloc l D v).val (if reflected then l.1.2 else l.1.1)
          Rfirst s.ν s.W s.P≠0) →
      (∑l∈labels,∑D∈Ds l,∑v∈children l D,
        Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
          volume (child s (if reflected then l.1.2 else l.1.1) Rfirst
            (alloc l D v) (χ l D v) (t l D v)))*
          (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
          Z^(Cycle63FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
            (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
            v.1.1 v.1.2 v.2.val+a+error))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hlabels⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a ξ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ Rfirst alloc χ t halloc
  have hbudget := hlabels reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbudget
  apply le_trans _ hbudget
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro v hv
  have hh := hz.2 s hcard hlow reflected second l (hsup l hl).1 (hsup l hl).2
    (heq l hl) Rfirst (alloc l D v) (χ l D v) (t l D v) (halloc l hl D hD v hv)
    v.1.1 v.1.2 (hsup₂ l hl D hD v hv).1 (hsup₂ l hl D hD v hv).2 v.2.val
    M a ξ reserve error εcommon B hecommon (by
      cases second
      · exact (hnorm₂ l hl D hD v hv).1
      · exact (hnorm₂ l hl D hD v hv).2)
  simpa only [add_assoc] using hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_low_label_payment
