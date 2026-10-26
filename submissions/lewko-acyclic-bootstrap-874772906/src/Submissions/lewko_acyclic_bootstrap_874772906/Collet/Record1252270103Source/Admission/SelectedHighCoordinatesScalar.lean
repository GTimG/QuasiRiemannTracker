/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal second-allocation frozen cost enters the existing physical x0 coordinate. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedExceptionalAllocationCost
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryHighSelected
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCoordinates
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentFirstAmplificationChoice Cycle61Moment Cycle61InitialMass
open Record1252270103Second OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Exact raw reduction and the literal frozen coefficient pay one common
norm. The child profile costs no more than the parent profile. Zero frozen
coefficients are included in this inequality. -/
theorem frozen_child_normalized_profile {ι:Type*} [Fintype ι]
    (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) (τ:Character) (t:ℝ) :
    ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (volume (child s C R B τ t)/volume s)*forcedProfileCost (child s C R B τ t)≤
      (forcedProfileCost s)^2/(C.absNorm:ℝ) := by
  have hC:=allocation_ne s C B
  have hv:=frozen_child_volume_cost s C R hC B τ t
  have hV:=volume_pos s
  have hf:‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
      (volume (child s C R B τ t)/volume s)≤forcedProfileCost s/(C.absNorm:ℝ) := by
    calc
      _=(‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*volume (child s C R B τ t))/volume s := by ring
      _≤((forcedProfileCost s/(C.absNorm:ℝ))*volume s)/volume s :=
        div_le_div_of_nonneg_right hv hV.le
      _=_:=by field_simp
  exact (mul_le_mul hf (child_forcedProfileCost s C R B τ t)
    (forcedProfileCost_nonneg _) (div_nonneg (forcedProfileCost_nonneg _) (Nat.cast_nonneg _))).trans_eq (by ring)

/-- This proposition is the literal second-allocation inequality, not an
analytic premise. All second allocations and their physical factors remain. -/
def SecondAllocationBound {ι:Type} [Fintype ι] (s:Input ι)
    (reflected left second:Bool) (l:FirstSourceLabel) (R:Ideal O)
    (B₁:actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ₁:Character) (t₁ Z M a ξ reserve ε errv:ℝ) : Prop :=
  let C₁:=if reflected then l.1.2 else l.1.1
  let s₁:=child s C₁ R B₁ τ₁ t₁
  ∀(C₂ D₂:Ideal O),Supported C₂→∀(U:Finset (CommonIndex C₂ D₂))
    (B₂:actualAllocations s₁.pools (if second then D₂ else C₂)) (τ₂:Character) (t₂:ℝ),
  let Cchosen:=if second then D₂ else C₂
  let s₂:=child s₁ Cchosen (R*C₁) B₂ τ₂ t₂
  let x:=childHighCoordinates (actualHighCoordinates reflected left second l C₂ D₂ U
    Z M (Real.logb Z (volume s)) a ξ reserve ε) errv
  Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume s₁)*
    normalizer C₂ D₂ U*‖frozenCoefficient B₂.val Cchosen (R*C₁) s₁.ν s₁.W s₁.P‖^2*
      (volume s₂/volume s₁)*forcedProfileCost s₂≤(forcedProfileCost s₁)^2*Z^(x 0)

/-- The original generic supported first-label theorem supplies x0. Its
threshold precedes all actual inputs and both common allocations, with no
old density, q-range or ordinary-active-source condition. -/
theorem eventual_selected_high_coefficient (N:ℕ) (lo errv:ℝ) (hlo:0<lo) (he:0<errv) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type} [Fintype ι] (s:Input ι),
    Fintype.card ι≤N→lo≤s.lower→∀(reflected left second:Bool) (l:FirstSourceLabel),
    Supported l.1.1→Supported l.1.2→primeSupport l.1.1=primeSupport l.1.2→
    ∀(R:Ideal O) (B₁:actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (τ₁:Character) (t₁:ℝ),
    frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0→
    ∀M a ξ reserve ε:ℝ,SecondAllocationBound s reflected left second l R B₁ τ₁ t₁ Z M a ξ reserve ε errv := by
  filter_upwards [eventual_actual_child_high_coefficient N lo errv hlo he] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst s hN hloS reflected left second l hC hD heq R B₁ τ₁ t₁ hB₁ M a ξ reserve ε
  let C₁:=if reflected then l.1.2 else l.1.1
  let s₁:=child s C₁ R B₁ τ₁ t₁
  intro C₂ D₂ hC₂ U B₂ τ₂ t₂ Cchosen s₂ x
  have hb:=hz.2 s hN hloS reflected left second l hC hD heq R B₁ τ₁ t₁ hB₁
    C₂ D₂ hC₂ U M a ξ reserve ε
  have hnc:(0:ℝ)<Cchosen.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (allocation_ne s₁ Cchosen B₂))
  have hZ:0<Z:=zero_lt_one.trans hz.1
  rw [Real.rpow_logb hZ hz.1.ne' hnc] at hb
  have hc:=frozen_child_normalized_profile s₁ Cchosen (R*C₁) B₂ τ₂ t₂
  have hp:0≤Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume s₁)*
      normalizer C₂ D₂ U :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
      (div_nonneg (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
        (volume_pos s₁).le)) (normalizer_pos C₂ D₂ hC₂ U).le
  calc
    _=(Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume s₁)*
        normalizer C₂ D₂ U)*
      (‖frozenCoefficient B₂.val Cchosen (R*C₁) s₁.ν s₁.W s₁.P‖^2*
        (volume s₂/volume s₁)*forcedProfileCost s₂) := by ring
    _≤(Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume s₁)*
        normalizer C₂ D₂ U)*((forcedProfileCost s₁)^2/(Cchosen.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hc hp
    _=(forcedProfileCost s₁)^2*(Z^(-a)*
      (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume s₁)*
        (normalizer C₂ D₂ U/(Cchosen.absNorm:ℝ))) := by ring
    _≤_:=mul_le_mul_of_nonneg_left hb (sq_nonneg _)

/-- The chosen common ideal of a literal modified column equals the ideal
read from its actual first label, in both orientations. -/
theorem modified_column_ideal {ι:Type*} [Fintype ι] (reflected:Bool)
    (s:Input ι) (modifier:Tuple ι→ℂ) (R seed:Ideal O) (K Z ξ:ℝ) (hK:0<K)
    (bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin)) :
    FirstFamily.columnIdeal reflected s modifier R seed K Z ξ hK bin j=
      if reflected then (FirstFamily.firstLabel s modifier R seed K Z ξ hK bin j).1.2
      else (FirstFamily.firstLabel s modifier R seed K Z ξ hK bin j).1.1 := by
  cases reflected <;> rfl

/-- Actual modified first columns supply the support and common-prime gates
internally; no embedding into an ordinary active source is used. -/
theorem eventual_modified_high_coefficient (N:ℕ) (lo errv:ℝ) (hlo:0<lo) (he:0<errv) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type} [Fintype ι] (s:Input ι),
    Fintype.card ι≤N→lo≤s.lower→∀(modifier:Tuple ι→ℂ) (R seed:Ideal O) (K ξ:ℝ) (hK:0<K)
      (bin:ℤ×(Fin 5→ℤ))
      (j:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin))
      (reflected left second:Bool),
    let l:=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin j
    ∀(B₁:actualAllocations s.pools (if reflected then l.1.2 else l.1.1)) (τ₁:Character) (t₁:ℝ),
    frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0→
    ∀M a reserve ε:ℝ,SecondAllocationBound s reflected left second l R B₁ τ₁ t₁ Z M a ξ reserve ε errv := by
  filter_upwards [eventual_selected_high_coefficient N lo errv hlo he] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst s hN hloS modifier R seed K ξ hK bin j reflected left second l B₁ τ₁ t₁ hB₁ M a reserve ε
  have hl:=FirstFamily.label_supported s modifier R seed K Z ξ hK bin j
  exact hz.2 s hN hloS reflected left second l hl.1 hl.2.1 hl.2.2 R B₁ τ₁ t₁ hB₁ M a ξ reserve ε

end
end QRH.Record1252270103Source.Admission.SelectedHighCoordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.frozen_child_normalized_profile
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.eventual_selected_high_coefficient
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.modified_column_ideal
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.eventual_modified_high_coefficient
