/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal first MAIN radius and padded projector gates. Retained annular support
supplies positivity; no lower bound on the initial volume is substituted. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.ExceptionalInitialSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentLogDyadic
open CenteredMomentFirstPhysicalDyadicAssembly (retainedIndices mem_retainedIndices)
open CenteredMomentSourceInputFirstTailUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile Cycle61Moment Cycle61InitialMass
open High.CoupledFirst Admission.FirstFamily
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance exceptionalGeometryDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

def literalFirstRadius (reflected:Bool)(K V Z ξ reserve:ℝ)(l:FirstSourceLabel):ℝ:=
  nominalLog l.1.1 l.1.2
    (Ideal.span {primeSubsetGenerator (fun p:CommonIndex l.1.1 l.1.2=>p.val) l.2.val}) K V Z+
    max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0+
    frequencyLoss Z 32 ξ+reserve

theorem literal_first_main_radius (reflected:Bool)(K V Z ξ amp reserve:ℝ)(l:FirstSourceLabel):
    Z^(literalFirstRadius reflected K V Z ξ reserve l+6*amp)=
      firstMainRadius reflected K V Z ξ (3*amp) reserve l := by
  unfold literalFirstRadius firstMainRadius CenteredMomentAmplifiedRetainedRadius.mainCommonRadius
  congr 1
  ring

theorem actual_first_H0_and_frequency {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(K Z ξ:ℝ)(hK:0<K)
    (bin:ℤ×(Fin 5→ℤ))(j:FirstColumnIndex (source s modifier R seed K Z ξ hK bin)):
    let l:=firstLabel s modifier R seed K Z ξ hK bin j
    let T:=firstNominalScale l.1.1 l.1.2 (∏p∈l.2.val,p.val) K (volume s)
    1<(source s modifier R seed K Z ξ hK bin j.1).H0 ∧
      (source s modifier R seed K Z ξ hK bin j.1).H0≤4*frequencyRadius T Z ξ := by
  intro l T
  have hn:(j.1.val.2.2 1:ℤ)∈retainedIndices
      (High.CoupledFirst.localRadius s modifier R seed K Z ξ j.1.val.1 j.1.val.2.1.val):=
    (j.1.val.2.2 1).property
  have hr:=((mem_retainedIndices _ _).mp hn).1
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact ⟨hq.trans_lt ((dyadicWeight_support _) hweight).2,retained_scale_le _ _ hr⟩

theorem actual_first_projector_cap {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(K Z ξ Y:ℝ)(hK:0<K)
    (hpool:∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Y)
    (bin:ℤ×(Fin 5→ℤ))(j:FirstColumnIndex (source s modifier R seed K Z ξ hK bin)):
    j.2.1.val≠0 ∧ (j.2.1.val.absNorm:ℝ)≤Y :=
  first_divisor_norm (source s modifier R seed K Z ξ hK bin j.1) Y (by
    intro I hI
    dsimp only [High.CoupledFirst.geometryFirstSource,High.CoupledFirst.originalFirstBlock] at hI
    apply hpool I
    simpa only [finiteColumns,Finset.mem_image,Fintype.mem_piFinset] using hI) j.2.1

theorem actual_first_radius_envelope {α:Type*}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(K Z ξ reserve:ℝ)
    (hK:0<K)(hZ:1<Z)(hreserve:0≤reserve)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s modifier R seed K Z ξ hK bin)):
    let l:=firstLabel s modifier R seed K Z ξ hK bin j
    let radius:=literalFirstRadius reflected K (volume s) Z ξ reserve l
    0≤radius ∧ ∀n∈bands (source s modifier R seed K Z ξ hK bin j.1).H0,
      dyadicScale n≤Z^radius := by
  intro l radius
  let T:=firstNominalScale l.1.1 l.1.2 (∏p∈l.2.val,p.val) K (volume s)
  have hl:=label_supported s modifier R seed K Z ξ hK bin j
  have he:=(subsetGenerator_supported l.1.1 l.1.2 hl.1 l.2.val).1
  have hT:0<T:=by
    have hh:=firstNominalScale_pos l.1.1 l.1.2 _ he K (volume s) hK (volume_pos s)
    simpa only [primeSubsetGenerator,span_idealGenerator] using hh
  have hZ0:=zero_lt_one.trans hZ
  have hfreq:0<frequencyRadius T Z ξ:=mul_pos hT (Real.rpow_pos_of_pos hZ0 _)
  have hnorm:=actual_first_H0_and_frequency s modifier R seed K Z ξ hK bin j
  let difference:=max (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
    Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) 0
  have hd:0≤difference:=le_max_right _ _
  have hrad:Z^radius=(128*frequencyRadius T Z ξ)*Z^(difference+reserve):=by
    change Z^(nominalLog _ _ _ K (volume s) Z+difference+frequencyLoss Z 32 ξ+reserve)=_
    simp only [nominalLog,primeSubsetGenerator,span_idealGenerator]
    change Z^(Real.logb Z T+difference+(ξ/2+Real.logb Z (4*32))+reserve)=_
    rw [show Real.logb Z T+difference+(ξ/2+Real.logb Z (4*32))+reserve=
      (Real.logb Z T+(ξ/2+Real.logb Z (128:ℝ)))+(difference+reserve) by norm_num;ring,
      Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0,
      Real.rpow_logb hZ0 hZ.ne' hT,Real.rpow_logb hZ0 hZ.ne' (by norm_num : (0:ℝ)<128)]
    unfold frequencyRadius
    ring
  have hge:128*frequencyRadius T Z ξ≤Z^radius:=by
    rw [hrad]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ.le (add_nonneg hd hreserve))
  have hH:(source s modifier R seed K Z ξ hK bin j.1).H0≤Z^radius:=
    hnorm.2.trans ((by nlinarith [hfreq]:4*frequencyRadius T Z ξ≤128*frequencyRadius T Z ξ).trans hge)
  constructor
  · by_contra hn
    have hh:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_lt (lt_of_not_ge hn))
    linarith [hnorm.1,hH]
  · intro n hn
    have hb:=bands_scale _ (zero_lt_one.trans hnorm.1) n hn
    have hh:dyadicScale n≤32*frequencyRadius T Z ξ:=by linarith [hb.2,hnorm.2]
    exact hh.trans ((by nlinarith [hfreq]:32*frequencyRadius T Z ξ≤128*frequencyRadius T Z ξ).trans hge)

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.literal_first_main_radius
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_H0_and_frequency
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_projector_cap
#print axioms QRH.Record1252270103Source.ExceptionalPrice.actual_first_radius_envelope
