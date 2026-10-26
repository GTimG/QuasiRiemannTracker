/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform first MAIN radius caps for actual initial columns. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.ExceptionalInitialGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCompleteCommon
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstCanonicalFamily CenteredMomentLogDyadic
open CenteredMomentSourceInputFirstTailUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile Cycle61Moment Cycle61InitialMass
open High.CoupledFirst Admission.FirstFamily Filter
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance exceptionalGeometryBoundsDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

theorem actual_first_radius_upper {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(Z ξ amp reserve:ℝ)(hZ:1<Z)
    (hs:Squarefree seed)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hsource:sourceRadius s≤Z^(2:ℝ))(hV:volume s≤Z)
    (hamp:amp≤1)(hreserve:reserve≤1)(hfreq:frequencyLoss Z 32 ξ≤1)
    (reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin)):
    literalFirstRadius reflected Z (volume s) Z ξ reserve
      (firstLabel s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j)+6*amp≤32 := by
  let l:=firstLabel s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hl:=label_supported s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
  have hn:=label_common_bounds s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin hs hz₁ hz₂ j
  have logbound (I:Ideal O)(hI:I≠0)(hcap:(I.absNorm:ℝ)≤Z^(2:ℝ)):
      0≤Real.logb Z (I.absNorm:ℝ) ∧ Real.logb Z (I.absNorm:ℝ)≤2 := by
    have hnorm:0<(I.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos I hI
    have hnorm1:(1:ℝ)≤I.absNorm:=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=Real.logb_le_logb_of_le hZ hnorm hcap
    rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
    exact ⟨Real.logb_nonneg hZ hnorm1,hh⟩
  have hc:=logbound l.1.1 hl.1.1 (hn.2.2.1.trans hsource)
  have hd:=logbound l.1.2 hl.2.1.1 (hn.2.2.2.trans hsource)
  have hdiff:max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0≤2 := by
    cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals exact max_le (by linarith) (by norm_num)
  let E:=Ideal.span {primeSubsetGenerator (fun p:CommonIndex l.1.1 l.1.2=>p.val) l.2.val}
  have hE:E≠0:=(subsetGenerator_supported l.1.1 l.1.2 hl.1 l.2.val).1
  have hT:=firstNominalScale_pos l.1.1 l.1.2 E hE Z (volume s) (zero_lt_one.trans hZ) (volume_pos s)
  have htcap:firstNominalScale l.1.1 l.1.2 E Z (volume s)≤Z:=by
    have hh:=first_nominal_scale_le l.1.1 l.1.2 l.2.val Z (volume s) (zero_lt_one.trans hZ)
    have hh':firstNominalScale l.1.1 l.1.2 E Z (volume s)≤(volume s)^2/Z:=by
      simpa only [E,primeSubsetGenerator,span_idealGenerator] using hh
    apply hh'.trans
    apply (div_le_iff₀ (zero_lt_one.trans hZ)).mpr
    simpa only [pow_two] using pow_le_pow_left₀ (volume_pos s).le hV 2
  have hlog:nominalLog l.1.1 l.1.2 E Z (volume s) Z≤1:=by
    have hh:=Real.logb_le_logb_of_le hZ hT htcap
    simpa only [nominalLog,Real.logb_self_eq_one hZ] using hh
  change literalFirstRadius reflected Z (volume s) Z ξ reserve l+6*amp≤32
  dsimp only [literalFirstRadius]
  change nominalLog l.1.1 l.1.2 E Z (volume s) Z+_+_+_+6*amp≤32
  linarith only [hlog,hdiff,hfreq,hreserve,hamp]

theorem actual_first_fourier_child {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(Z ξ amp reserve:ℝ)(hZ:1<Z)
    (N:ℕ)(hN:Fintype.card α≤N)(hupper:s.upper≤2)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin))
    (B:actualAllocations s.pools (columnIdeal reflected s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j))
    (τ:Character)(t:ℝ)
    (hf:frozenCoefficient B.val (columnIdeal reflected s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j)
      R s.ν s.W s.P≠0):
    let l:=firstLabel s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
    let C:=columnIdeal reflected s modifier R seed Z Z ξ (zero_lt_one.trans hZ) bin j
    (volume (child s C R B τ t))^2/firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve l≤
      firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve 2 N l := by
  intro l C
  exact Cycle61FinalRadius.actual_second_radius_admissible N 2 (by norm_num) s hN hupper C R B τ t _
    (first_main_radius_pos reflected Z (volume s) Z ξ (3*amp) reserve (zero_lt_one.trans hZ) l) hf

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_radius_upper
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_fourier_child
