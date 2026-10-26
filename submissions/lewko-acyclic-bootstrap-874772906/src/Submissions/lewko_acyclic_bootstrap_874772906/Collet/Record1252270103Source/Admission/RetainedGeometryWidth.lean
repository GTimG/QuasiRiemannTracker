/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained MAIN width, reusing the generic Cycle61 row conductor budget. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedGeometryBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondOrientedWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization Cycle61InitialMass Record1252270103Second
open Record1252270103Source.Collision QRH.Record1252270103Low
open High.GlobalPhysical CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondCanonical Cycle61FinalNatural
open CenteredMomentCanonicalFirst RayFourExpansion CenteredMomentSecondRadicalBudget
local notation "O"=>ActualEisensteinCubic.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
  (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
  (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key))
local notation "Cj"=>FirstFamily.columnIdeal reflected s modifier R seed K Z ξ hK key j
local notation "τj"=>FirstFamily.columnCharacter reflected s modifier R seed K Z ξ hK key j
variable (A₁ A₂ D Kmark : Ideal O) (F : Ideal O→ℂ) (P : Finset (Ideal O)) (t H Tsec : ℝ)


local notation "SupportedLabels"=>SupportedLabel reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec
variable (V : Fin 4→ℝ→ℂ) (hj : j∈firstLiveColumns (source s modifier R seed K Z ξ hK key) V)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hH : 0<H)
local notation "sdata"=>supportedDatum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec V hj hz₁ hz₂ hH

/-- Actual retained MAIN rows have the conductor/log-width bound in both
orientations. The first character equality is discharged by construction. -/
theorem supported_row_main_width (a reserve b : ℝ) (N : ℕ)
    (hZ : 1<Z) (hb : 0<b)
    (hscale : Tsec=firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      (FirstFamily.firstLabel s modifier R seed K Z ξ hK key j))
    (r : secondLiveRows (fun q=>(sdata q).block))
    (Bmask : ℝ) (χ : RayCharacter) (Q J : Ideal O) (hJ : J≠0) (hJN : (J.absNorm:ℝ)≤Z^Bmask) :
    let src:=source s modifier R seed K Z ξ hK key j.1
    let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
    let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    let d:=sdata r.val.1
    (retainedState Z Bmask hZ (d.τ χ) Q J hJ hJN d.radius d.C d.D d.inactive).width≤
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-Real.logb Z (normValue (commonFrequencyGenerator d.C d.D))+
        Real.logb Z ((∏p∈d.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) := by
  intro src c e d
  have hm : d.input.η.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
        activeConductor src.C src.D} :=
    FirstFamily.column_modulus reflected s modifier R seed K Z ξ hK key j
  have hr : d.radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (FirstFamily.firstLabel s modifier R seed K Z ξ hK key j)) Z ξ := by
    change frequencyRadius Tsec Z ξ=_
    rw [hscale]
  exact actual_second_live_main_width_oriented reflected sdata r s.η src.C src.D src.hC src.hD
    src.sameSupport src.inactive K (volume s) Z a (frequencyLoss Z 32 ξ) reserve ξ b N
    hK (volume_pos s) hZ hb hm Bmask χ Q J hJ hJN hr

/-- Removing allocations with zero literal frozen weight is an exact sum
identity. The complete block/filter can be retained in the arbitrary f. -/
theorem supported_weight_sum
    (f : Label reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec→ℂ) :
    (∑q, (‖frozenCoefficient q.1.val Cj R s.ν s.W s.P‖^2:ℝ)*f q)=
    ∑q : SupportedLabels,(‖frozenCoefficient q.val.1.val Cj R s.ν s.W s.P‖^2:ℝ)*f q.val := by
  classical
  let weight : Label reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec→ℂ :=
    fun q=>(‖frozenCoefficient q.1.val Cj R s.ν s.W s.P‖^2:ℝ)*f q
  let keep : Label reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec→Prop :=
    fun q=>frozenCoefficient q.1.val Cj R s.ν s.W s.P≠0
  change (∑q,weight q)=∑q:SupportedLabels,weight q.val
  calc
    _=∑q∈Finset.univ.filter keep,weight q := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hf : frozenCoefficient q.1.val Cj R s.ν s.W s.P=0
      · simp [keep,weight,hf]
      · simp [keep,hf]
    _=_ := Finset.sum_subtype (Finset.univ.filter keep) (by intro q;simp [keep]) weight

variable (a reserve b : ℝ) (N : ℕ)
local notation "firstLabel"=>FirstFamily.firstLabel s modifier R seed K Z ξ hK key j
local notation "mainH"=>firstMainRadius reflected K (volume s) Z ξ (3*a) reserve firstLabel
local notation "mainTsec"=>firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N firstLabel

abbrev MainLabel := SupportedLabel reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t mainH mainTsec

/-- The actual MAIN radius and Fourier scale are selected here, so callers
need not add a radius-identification premise for these data. -/
abbrev mainDatum (hZ : 0<Z)
    (q : MainLabel reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t a reserve b N) :
    SecondInputDatum ι :=
  supportedDatum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t mainH mainTsec
    V hj hz₁ hz₂ (first_main_radius_pos reflected K (volume s) Z ξ (3*a) reserve hZ firstLabel) q
local notation "mdata"=>mainDatum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t V hj hz₁ hz₂ a reserve b N

theorem main_row_width (hZ : 1<Z) (hb : 0<b)
    (r : secondLiveRows (fun q=>(mdata (zero_lt_one.trans hZ) q).block))
    (Bmask : ℝ) (χ : RayCharacter) (Q J : Ideal O) (hJ : J≠0) (hJN : (J.absNorm:ℝ)≤Z^Bmask) :
    let src:=source s modifier R seed K Z ξ hK key j.1
    let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
    let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    let d:=mdata (zero_lt_one.trans hZ) r.val.1
    (retainedState Z Bmask hZ (d.τ χ) Q J hJ hJN d.radius d.C d.D d.inactive).width≤
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-Real.logb Z (normValue (commonFrequencyGenerator d.C d.D))+
        Real.logb Z ((∏p∈d.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) :=
  supported_row_main_width reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t mainH mainTsec
    V hj hz₁ hz₂ (first_main_radius_pos reflected K (volume s) Z ξ (3*a) reserve
      (zero_lt_one.trans hZ) firstLabel) a reserve b N hZ hb rfl r Bmask χ Q J hJ hJN


/-- MAIN selection discharges the tail's nominal-scale premise using the
original volume and the actual nonzero frozen allocation weight. -/
theorem main_row_nominal (hZ : 0<Z) (hb : 1≤b) (hcard : Fintype.card ι≤N) (he : s.upper≤b)
    (r : secondLiveRows (fun q=>(mdata hZ q).block)) :
    (volume (mdata hZ r.val.1).input)^2/mainH≤mainTsec :=
  supported_row_nominal reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t mainH mainTsec
    V hj hz₁ hz₂ (first_main_radius_pos reflected K (volume s) Z ξ (3*a) reserve hZ firstLabel)
    N b hb hcard he r

theorem main_scale_upper (hZ : 1<Z) (hb : 0<b) (ha : 0≤a) (hξ : 0≤ξ) (hr : 0≤reserve) :
    mainTsec≤b^(2*N)*K := by
  let src:=source s modifier R seed K Z ξ hK key j.1
  exact main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K (volume s) Z (3*a) (frequencyLoss Z 32 ξ) reserve b N
    hK (volume_pos s) hZ hb (by positivity) (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hr

theorem main_row_radius_cap (hZ : 1<Z) (hb : 0<b) (ha : 0≤a) (hξ : 0≤ξ) (hr : 0≤reserve)
    (M : ℝ) (hKM : K≤Z^M) (r : secondLiveRows (fun q=>(mdata (zero_lt_one.trans hZ) q).block)) :
    (mdata (zero_lt_one.trans hZ) r.val.1).radius≤b^(2*N)*Z^(M+ξ/2) := by
  have hh:=main_scale_upper reflected s modifier R seed K Z ξ hK key j a reserve b N hZ hb ha hξ hr
  change frequencyRadius mainTsec Z ξ≤_
  unfold frequencyRadius
  calc
    _≤(b^(2*N)*K)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by linarith) _)
    _≤(b^(2*N)*Z^M)*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKM (pow_nonneg hb.le _)) (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [Real.rpow_add (zero_lt_one.trans hZ)];ring

/-- The fixed first dictionary and accumulated puncture are literal
construction fields, also on MAIN's supported allocation family. -/
theorem main_row_parent (hZ : 0<Z) (hR : R≠0)
    (r : secondLiveRows (fun q=>(mdata hZ q).block)) :
    let d:=mdata hZ r.val.1
    d.input.η=τj ∧ d.R=R*Cj ∧ d.R≠0 ∧ d.seed=j.2.1.val := by
  refine ⟨rfl,rfl,?_,rfl⟩
  exact mul_ne_zero hR (FirstFamily.column_supported reflected s modifier R seed K Z ξ hK key j).1

end
end QRH.Record1252270103Source.Admission.RetainedGeometry
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.supported_row_main_width
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_row_width

#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_row_nominal
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_scale_upper
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_row_radius_cap
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_row_parent

#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.supported_weight_sum
