import Candidate.Target836.SourceProvider.NamedSource
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometryPayment

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

theorem actual_high_coordinate_excess_identity (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)=
      S+(1-ρ)*ω+ρ*ε+Cycle63.Physical.highJointExcess M A a δ c d p R E
        (max (3*c-5*d-R) 0/6) Lc
        (Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)) b₂
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  dsimp only
  dsimp [highExponentValue,actualHighCoordinates,Cycle63.Physical.highJointExcess]
  rw [actual_missing_log left l hC Z]
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)];ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  linear_combination hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))

theorem actual_high_coordinate_valuation_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Named.q≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Named.total b) (ha : a≤M*Named.amp b) :
    let ρ := unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)≤
      S-M*Named.high b δ-Named.gamma δ*(c+b₂)+(1-ρ)*ω+ρ*ε := by
  have hr := Named.rho_bounds_full hδ
  have hh := actual_high_joint_valuation_saving reflected left second l hC hD
    C₂ D₂ hC₂ hD₂ heq₂ U Z δ M A a hZ hr.1 hr.2
  have hid := actual_high_coordinate_excess_identity reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hZ
  have hδ0 : 0≤δ := by norm_num [Named.q] at hδ; linarith [hδ.1]
  have hcoef : 0≤5-6*unmarkedDensity δ := by change 0≤5-6*Named.rho δ; linarith [hr.2]
  have hb₂ : 0≤Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hAmul := mul_le_mul_of_nonneg_left hA hδ0
  have hamul := mul_le_mul_of_nonneg_right ha hcoef
  have hbmul := mul_le_mul_of_nonneg_right (Named.gamma_bounds_full hδ).2 hb₂
  dsimp only at hid hh ⊢
  rw [hid]
  unfold Named.high Named.gamma Named.rho at *
  nlinarith only [hh,hAmul,hamul,hbmul]

theorem actual_geometry_compensated_valuation_payment
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b δ : ℝ)(hZ : 1<Z)
    (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Named.q≤δ ∧ δ≤3/4)(hD : 0≤D)
    (hA : A≤D*Named.total b)(ha : a≤D*Named.amp b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    highExponentValue δ x≤
      (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
        D*Named.high b δ-Named.gamma δ*(c+b₂) := by
  intro l side x c b₂
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD' : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z ξ hK bin j.1).sameSupport
  have hh:=actual_high_coordinate_valuation_payment reflected left second l hC hD' heq
    d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z b δ D A a ξ reserve ε hZ hb hδ hD hA ha
  have he:=actual_geometry_high_side_identity s R seed K Z ξ hK bin j reflected A
  change side=_ at he
  dsimp only at hh
  rw [←he] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  dsimp only [c,b₂]
  linarith only [hh]

/-- The exact amplification cap is retained before the fixed source omega loss. -/
theorem raw_frequency_moving (M c d b₂ a R Lc omega err raw amp : ℝ)
    (hc : 0≤c)(hd : 0≤d)(hb₂ : 0≤b₂)(hR : R≤c)(hLc : 0≤Lc)
    (ha : a≤M*amp)(hω : omega≤M/1000)(herr : 0≤err)
    (hraw : raw=M-R-max (c-d) 0+Lc-6*a-omega+err) :
    M*(1-6*amp-1/1000)-2*(c+b₂)≤raw := by
  have hm : max (c-d) 0≤c := max_le (by linarith) hc
  nlinarith

/-- Moving frequency and volume for the literal actual two-stage allocation. -/
theorem actual_geometry_compensated_moving_frequency
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv b : ℝ)(hZ : 1<Z)
    (ha : a≤D*Named.amp b)(hω : frequencyLoss Z 32 ξ+reserve≤D/1000)(hε : 0≤ε) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂:=Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ)
    0≤c ∧ 0≤b₂ ∧ x 3=A-(c+b₂) ∧
      D*Named.frequency b-2*(c+b₂)≤Named.core*x 2 := by
  intro l side x c b₂
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  have hc : 0≤c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hd : 0≤Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.2 hD.1
    · exact norm_ge_one l.1.1 hC.1
  have hb₂ : 0≤b₂ := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d₂.C d₂.hC.1
    · exact norm_ge_one d₂.D d₂.hD.1
  have hg:=actual_first_gates left l hC hD Z hZ
  have hR : Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)≤c := by
    cases reflected
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.1
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.2.1
  have hLc : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero left l hC))
  refine ⟨hc,hb₂,?_,?_⟩
  · dsimp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c,b₂]
    ring
  · have hraw := raw_frequency_moving D c
      (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) b₂ a
      (Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ))
      (Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ))
      (frequencyLoss Z 32 ξ+reserve) ε (x 2) (Named.amp b) hc hd hb₂ hR hLc ha hω hε
      (by simp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c])
    unfold Named.frequency Named.core Named.omega
    nlinarith

end
end Target874836.SourceProvider

#print axioms Target874836.SourceProvider.actual_high_coordinate_valuation_payment
#print axioms Target874836.SourceProvider.actual_geometry_compensated_valuation_payment
#print axioms Target874836.SourceProvider.actual_geometry_compensated_moving_frequency
