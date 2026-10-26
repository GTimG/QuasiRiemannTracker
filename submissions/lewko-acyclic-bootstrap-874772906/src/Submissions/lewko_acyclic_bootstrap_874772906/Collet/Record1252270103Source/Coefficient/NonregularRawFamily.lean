/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite-core and tiny-frequency RAW counts for the literal modified first
family, retaining the additional Newton puncture and original marked slots.
The dictionary and geometric counting interfaces derive from Zhongpai Gao,
accepted PR63, source 52419a826d4a8465cdeb56aaa2d471c489221d1d,
and the OpenAI/math and Hailey Collet developments, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.DictionaryExceptionalRaw
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.SharpHighSector
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.VariableJointMarkedBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyNewtonPacket

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.NonregularRawFamily
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource LocalMoment HeckeInverseAmplification
open CenteredMomentFirstPhysicalSource CenteredMomentChildRows RayFourExpansion
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open CanonicalQuadraticSieve IdealMobiusDivisorSum ActualEisensteinCubic
open Cycle61HighProfiles CenteredMomentAmplificationChildInput Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem nonregular_gain_monotone (sector : HighSector) (hne : sector≠.regular)
    (ν S tinyCut : ℝ) (hν : ν≤3/4) :
    Monotone (sectorSharpGain sector ν S tinyCut) := by
  cases sector with
  | regular => exact (hne rfl).elim
  | fixed => exact exceptional_high_gain_monotone true ν S tinyCut hν
  | tiny => exact fun _ _ _=>le_refl _

/-- The genuine finite-core/tiny RAW family estimate. Its constant precedes
the moving source data, full original subsets, punctures and all heights.
The remaining exponent premise is the explicit scalar geometric ledger. -/
theorem actual_modified_nonregular_raw_family {α : Type} [Fintype α] [DecidableEq α]
    (ηanchor η₀ : Character) (W : ℝ→ℂ) (lo hi : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : Continuous W)
    (B loss : ℝ) (hB : 0≤B) (hloss : 0<loss) :
    ∃C : ℝ,0<C ∧∀P : HighSourceParameters,P.Wslot=W→lo≤P.σmin→P.σmax≤hi→
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(_hη : s.η=ηanchor)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=FirstFamily.columnCharacter reflected s modifier R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter)(punctureExtra : κ→Ideal O)(hExtra : ∀l,punctureExtra l≠0),
      let left := !reflected
      let unit := fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
      let hf := fun l=>FirstFamily.first_frequency_ne_zero reflected s modifier R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left 1 unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀(sector : HighSector),sector≠.regular→
      ∀(ν tinyCut rootError Q width Bbox target reserve : ℝ),
      1/2≤ν→ν≤3/4→0≤tinyCut→0≤rootError→Q≤B→0<width→
      Function.Injective key→
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ)
        (slots : κ→Finset α)(w σ v : α→ℝ)(t : κ→ℝ)(θ : α→RayQuotient.Characters M H),
      (∀l∈labels,sector=.fixed→(Record12518109GainWholeGeometry.wholeRegularDictionary M H hH
        (secondFixedDictionary ηanchor (FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)) η₀).exceptionalCore (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1)→
      (∀l∈labels,sector=.tiny → rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^tinyCut)→
      (∀l∈labels,∀j,-Bbox≤x l j ∧ x l j≤Bbox)→
      (∀l∈labels,0≤x l 2 ∧ x l 2+width≤Q)→
      (∀l∈labels,coeff l≤Z^(x l 0))→
      ∀st : κ→NaturalState Z P.Bmask P.bΦ,
      ∀(z : κ→O)(hz : ∀l,(st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=((datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*punctureExtra l)
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^(x l 2))→
      (∀l∈labels,((Ideal.span {jointSourceRow left 1 unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧
        ((key l).val.2.1.2.absNorm:ℝ)≤Z^B)→
      (∀l∈labels,((firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^(x l 1))→
      (∀j,0≤w j)→(∀j,P.σmin≤σ j)→(∀j,σ j≤P.σmax)→
      (∀l∈labels,retainedHighExponent ν
        (fun q=>sectorSharpGain sector ν (∑j∈slots l,w j) tinyCut q) (x l)≤target-reserve)→
      (∑l∈labels,coeff l*Z^(ν*(x l 3-∑j∈slots l,w j))*
        (∏j∈slots l,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
          (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2)≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width+loss+rootError)) := by
  classical
  obtain ⟨Cfixed,hCfixed,hfixed⟩:=actual_dictionary_finite_core_raw_maximum (Slot:=α) M H hH
    (secondFixedDictionary ηanchor) η₀ W lo hi hWs hW
  obtain ⟨Ctiny,hCtiny,htinyCount⟩:=actual_uniform_labeled_tiny_raw_maximum (Slot:=α) M H hH W lo hi hWs hW
  let Craw:=max Cfixed Ctiny
  have hCraw : 0<Craw:=hCfixed.trans_le (le_max_left _ _)
  obtain ⟨Cmult,hCmult,hbins⟩:=Geometry.actual_variable_joint_marked_binned_bound B loss hB hloss
  let Cpart : ℝ:=(Fintype.card (RayCharacter×RayCharacter):ℝ)*(2:ℝ)^Fintype.card α
  refine ⟨Cpart*Cmult*Craw,by dsimp [Cpart];positivity,?_⟩
  intro P hPW hPlo hPhi
  filter_upwards [FirstFamily.eventually_marked_packet_extra ηanchor B P.Bmask P.bΦ,
    eventually_ge_atTop (2:ℝ)] with Z hp hZ2
  refine ⟨hZ2,?_⟩
  intro κ DataLabel _ _ reflected second s modifier hηs R seed K ξ hK bin column datum first row hparent hfirst hR ψ punctureExtra hExtra
    left unit hf rawKey key sector hsector ν tinyCut rootError Q width Bbox target reserve hν hν' htiny hroot hQB hwidth
    hinj labels x coeff slots w σ v t θ hexceptional htinyNorm hx hq hcoeff st z hz hchar hpuncture hrow hraw hsupport hnorm hmissing hw hσlo hσhi hpoint
  have hZ : 1<Z:=by linarith
  have hzpos : 0<Z:=zero_lt_one.trans hZ
  let amplitude:=labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
    (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture)
  let index:=fun l=>(FirstFamily.dictionaryRay reflected s modifier R seed K Z ξ hK bin (column l),ψ l)
  let gain:=fun (ss : Finset α)(q : ℝ)=>sectorSharpGain sector ν (∑j∈ss,w j) tinyCut q
  let energy:=fun l=>coeff l*Z^(ν*(x l 3-∑j∈slots l,w j))*(∏j∈slots l,max 1 ‖amplitude l j‖)^2
  have hfirstcap (l : κ)(hl : l∈labels) :
      ((CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin (column l).1).C.absNorm:ℝ)≤Z^B := by
    have hh:=(hnorm l hl).1
    have hk : (key l).val.1=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin (column l):=by
      cases second <;> exact hfirst l
    rw [hk] at hh
    exact hh
  have hpacket (l : κ)(hl : l∈labels):=hp.2 reflected second s modifier hηs R seed K ξ hK bin (column l)
    datum first (row l) (hparent l) (hfirst l) (hR l) (ψ l) (punctureExtra l) (hExtra l) (hfirstcap l hl)
    (st l) (z l) (hz l) (hchar l) (hpuncture l) (hrow l)
  let holes:=fun l=>(datum (row l).val.1).input.η.modulus*(st l).puncture
  have hcount (j : RayCharacter×RayCharacter)(ss : Finset α)(rows : Finset κ)
      (hrows : rows⊆labels.filter (fun l=>index l=j ∧slots l=ss))
      (hinjrow : Set.InjOn (fun l=>nonzeroJointSourceRow (key l)) (↑rows:Set κ))
      (q : ℝ)(hq0 : 0≤q)(hq1 : q≤Q)
      (hrowq : ∀l∈rows,rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^q) :
      (∑l∈rows,(∏k∈ss,max 1 ‖amplitude l k‖)^2)≤
        Craw*Z^(unmarkedDensity ν*q+ν*(∑k∈ss,w k)-gain ss q+rootError) := by
    have hmem (l : κ)(hl : l∈rows):l∈labels:=(Finset.mem_filter.mp (hrows hl)).1
    let χ:=fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture
    have hcoeffs (l : κ)(hl : l∈rows)(L : Ideal O) : idealCoeff (χ l) L=
        idealCoeff (excluded (naturalRow (secondFixedDictionary ηanchor j)
          (nonzeroJointSourceRow (key l)).val (nonzeroJointSourceRow (key l)).property).character (holes l)) L := by
      have hh:=(hpacket l (hmem l hl)).2.2.1 L
      change idealCoeff (χ l) L=idealCoeff (excluded (naturalRow (secondFixedDictionary ηanchor (index l)) (nonzeroJointSourceRow (key l)).val (nonzeroJointSourceRow (key l)).property).character (holes l)) L at hh
      rw [(Finset.mem_filter.mp (hrows hl)).2.1] at hh
      exact hh
    cases hs : sector with
    | regular => exact (hsector hs).elim
    | fixed =>
      have hfixedgate (l : κ)(hl : l∈rows) :
          (wholeRegularDictionary M H hH (secondFixedDictionary ηanchor j) η₀).exceptionalCore
            (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1 := by
        have hr:=hexceptional l (hmem l hl) hs
        change (wholeRegularDictionary M H hH (secondFixedDictionary ηanchor (index l)) η₀).exceptionalCore
          (sixthFrequencyEquiv.symm (nonzeroJointSourceRow (key l))).1 at hr
        rw [(Finset.mem_filter.mp (hrows hl)).2.1] at hr
        exact hr
      have hb:=hfixed Z q hZ.le hq0 j rows (fun l=>nonzeroJointSourceRow (key l)) hinjrow
        ss w σ v t θ holes χ hrowq hfixedgate hcoeffs (fun k _=>hw k)
        (fun k _=>hPlo.trans (hσlo k)) (fun k _=>(hσhi k).trans hPhi)
      simp only [←hPW] at hb
      have heq : unmarkedDensity ν*q+ν*(∑k∈ss,w k)-gain ss q+rootError=
          q/6+(∑k∈ss,w k)+rootError := by
        simp only [gain,hs,sectorSharpGain,exceptional_high_count_exponent,ite_true]
      rw [heq]
      exact hb.trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hroot]))
        (Real.rpow_nonneg hzpos.le _) hCraw.le)
    | tiny =>
      let qt:=min q tinyCut
      have hqt : 0≤qt:=le_min hq0 htiny
      have hrowqt (l : κ)(hl : l∈rows) : rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^qt := by
        rcases le_total q tinyCut with h|h
        · simpa only [qt,min_eq_left h] using hrowq l hl
        · simpa only [qt,min_eq_right h] using htinyNorm l (hmem l hl) hs
      have hb:=htinyCount Z qt hZ.le hqt (secondFixedDictionary ηanchor j) η₀ rows
        (fun l=>nonzeroJointSourceRow (key l)) hinjrow ss w σ v t θ holes χ hrowqt hcoeffs
        (fun k _=>hw k) (fun k _=>hPlo.trans (hσlo k)) (fun k _=>(hσhi k).trans hPhi)
      simp only [←hPW] at hb
      apply hb.trans
      apply mul_le_mul (le_max_right _ _) _ (Real.rpow_nonneg hzpos.le _) hCraw.le
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hρ0 : 0≤unmarkedDensity ν := (by norm_num : (0:ℝ)≤2/7).trans (unmarkedDensity_ge_two_sevenths hν')
      have hρ1 : unmarkedDensity ν≤1:=unmarkedDensity_le_one (by linarith) (by linarith)
      have hint:=tiny_radial_interpolation (unmarkedDensity ν) q tinyCut hρ0 hρ1
      simp only [gain,hs,sectorSharpGain]
      dsimp only [qt]
      nlinarith only [hint,hroot]
  have hb:=hbins left 1 unit Z hZ2 key hinj labels x energy slots index amplitude w
    ν 0 Q width Bbox Craw rootError target reserve gain hν hν' hCraw.le hwidth
    (fun ss=>nonregular_gain_monotone sector hsector ν _ tinyCut hν')
    hx hq hpoint (fun l hl=>by
      dsimp only [energy]
      rw [Real.rpow_add hzpos]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoeff l hl) (Real.rpow_nonneg hzpos.le _)) (sq_nonneg _))
    hraw (fun l hl=>(hraw l hl).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [(hq l hl).2])))
    (fun l hl=>(hpacket l hl).2.2.2.1) (fun l hl=>(hpacket l hl).2.2.2.2)
    hsupport hnorm hmissing (fun j ss rows hrows hinjrow q hq0 hq1 hr=>hcount j ss rows (by
      intro l hl
      have hm : l∈labels ∧index l=j ∧slots l=ss := by simpa only [Finset.mem_filter] using hrows hl
      simpa only [Finset.mem_filter] using hm) hinjrow q hq0 hq1 hr)
  have heq : (Fintype.card (RayCharacter×RayCharacter):ℝ)*(2:ℝ)^Fintype.card α*
      (((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (Cmult*Craw*Z^(target-reserve+4*width+loss+rootError)))=
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        ((Cpart*Cmult*Craw)*Z^(target-reserve+4*width+loss+rootError)) := by dsimp [Cpart];ring
  exact hb.trans_eq heq

end
end QRH.Record1252270103Source.NonregularRawFamily
#print axioms QRH.Record1252270103Source.NonregularRawFamily.nonregular_gain_monotone
#print axioms QRH.Record1252270103Source.NonregularRawFamily.actual_modified_nonregular_raw_family
