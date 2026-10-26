/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
First-label geometry is read from the actual modified common-label fiber. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyLabels
import Submissions.hailey_collet_1252270103.Record12518109Raw.NaturalMask
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyDictionary
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryHighSelected
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryMainHighSourceCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentFirstSourceConductorCaps CenteredMomentEnergyState
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentCommonRadialData
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic Cycle61InitialMass
open Record12518109Raw Filter CenteredMomentSectorLocalization LocalMoment ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic label and four dyads recover the literal modified source
coordinate. No extra multiplicity and no unmodified active source is used. -/
theorem coordinate_code_injective (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) :
    Function.Injective (fun q : QRH.Record1252270103Source.High.CoupledFirst.SourceCoordinate s modifier R seed K Z ξ=>
      ((⟨q.1.val,q.2.1⟩ : FirstSourceLabel),fun i=>(q.2.2 i:ℤ))) := by
  rintro ⟨p,E,n⟩ ⟨p',E',n'⟩ h
  have hp : p.val=p'.val := congrArg (fun x=>x.1.1) h
  have hp' : p=p' := Subtype.ext hp
  cases hp'
  have hE : E=E' := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst h)).2
  cases hE
  have hn : n=n' := funext (fun i=>Subtype.ext (congrFun (congrArg Prod.snd h) i))
  cases hn
  rfl

theorem column_code_injective (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ)) :
    Function.Injective (fun j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)=>
      (firstLabel s modifier R seed K Z ξ hK key j,j.2.1.val,
        (fun i=>(j.1.val.2.2 i:ℤ)),j.2.2.1,j.2.2.2)) := by
  rintro ⟨q,L,χ,ψ⟩ ⟨q',L',χ',ψ'⟩ h
  have hq : q=q' := by
    apply Subtype.ext
    apply coordinate_code_injective s modifier R seed K Z ξ
    exact congrArg (fun x=>(x.1,x.2.2.1)) h
  cases hq
  have hL : L=L' := Subtype.ext (congrArg (fun x=>x.2.1) h)
  cases hL
  have hχ : χ=χ' := congrArg (fun x=>x.2.2.2.1) h
  have hψ : ψ=ψ' := congrArg (fun x=>x.2.2.2.2) h
  cases hχ
  cases hψ
  rfl

theorem label_supported (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :
    let l:=firstLabel s modifier R seed K Z ξ hK key j
    Supported l.1.1 ∧ Supported l.1.2 ∧
      CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2 :=
  ⟨(source s modifier R seed K Z ξ hK key j.1).hC,
    (source s modifier R seed K Z ξ hK key j.1).hD,
    (source s modifier R seed K Z ξ hK key j.1).sameSupport⟩

theorem label_common_bounds (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :
    let l:=firstLabel s modifier R seed K Z ξ hK key j
    seed∣l.1.1 ∧ seed∣l.1.2 ∧
      (l.1.1.absNorm:ℝ)≤sourceRadius s ∧ (l.1.2.absNorm:ℝ)≤sourceRadius s := by
  have h:=QRH.Record1252270103Source.High.CoupledFirst.actual_common_gates s modifier R seed hs hz₁ hz₂
    j.1.val.1.val.1 j.1.val.1.val.2 j.1.val.1.property
  exact h.2.2.2

theorem label_missing_nonzero (left : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key)) :
    firstSourceMissing left (firstLabel s modifier R seed K Z ξ hK key j)≠0 := by
  have hn:=(label_supported s modifier R seed K Z ξ hK key j).1.1
  have hd:=first_missing_dvd left (firstLabel s modifier R seed K Z ξ hK key j) hn
  intro hz
  rw [hz] at hd
  exact hn (zero_dvd_iff.mp hd)

theorem live_projector_squarefree (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (V : Fin 4→ℝ→ℂ) (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key))
    (hj : j∈firstLiveColumns (source s modifier R seed K Z ξ hK key) V) :
    Squarefree j.2.1.val := actual_first_live_squarefree _ V j hj

/-- The literal modified first labels supply the frequency coordinate of the
actual retained second rows. The eventual threshold precedes all sources,
characters, labels and moving masks. -/
theorem eventual_literal_high_frequency
    (b εfreq : ℝ)(N : ℕ)(hb : 0<b)(hε : 0<εfreq) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{α DataLabel : Type}[Fintype α][DecidableEq α][Fintype DataLabel],
    ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(R seed : Ideal O)(D ξ : ℝ)(hK : 0<Z^D)
      (bin : ℤ×(Fin 5→ℤ))
      (column : FirstColumnIndex (source s modifier R seed (Z^D) Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : secondLiveRows (fun l=>(datum l).block))
      (hfirst : first row.val.1=firstLabel s modifier R seed (Z^D) Z ξ hK bin column)
      (ampExponent reserveShift εvolume : ℝ),
    ξ≤εfreq →
    (datum row.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) (CenteredMomentAmplificationChildInput.volume s) Z ξ (3*ampExponent) reserveShift b N
        (firstLabel s modifier R seed (Z^D) Z ξ hK bin column)) Z ξ →
    let left:=!reflected
    let unit:=fun l=>(fixedParentUnit left s.η l:O)
    let hf:=first_frequency_ne_zero reflected s modifier R seed (Z^D) Z ξ hK
      bin column datum first row hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left 1 unit hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let d₂:=datum row.val.1
    let x:=childHighCoordinates (actualHighCoordinates reflected left second
      (firstLabel s modifier R seed (Z^D) Z ξ hK bin column) d₂.C d₂.D d₂.inactive
      Z D (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) ampExponent ξ reserveShift εfreq) εvolume
    rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2) := by
  filter_upwards [eventual_actual_child_high_frequency 1 b εfreq N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro α DataLabel _ _ _ reflected second s modifier R seed D ξ hK bin column datum first row hfirst
    ampExponent reserveShift εvolume hξ hradius left unit hf key₀ key d₂ x
  have hC : Supported (first row.val.1).1.1 := hfirst.symm ▸
    (source s modifier R seed (Z^D) Z ξ hK bin column.1).hC
  have hD : Supported (first row.val.1).1.2 := hfirst.symm ▸
    (source s modifier R seed (Z^D) Z ξ hK bin column.1).hD
  have heq : primeSupport (first row.val.1).1.1=primeSupport (first row.val.1).1.2 := hfirst.symm ▸
    (source s modifier R seed (Z^D) Z ξ hK bin column.1).sameSupport
  have hret:=actual_second_live_retained_weight (fun l=>(datum l).block) row.val row.property
  change retainedWeight d₂.radius (normValue
    ((commonFrequencyGenerator d₂.C d₂.D*nonunitFrequencyGenerator d₂.C d₂.D d₂.inactive)*
      row.val.2.2.2.val))≠0 at hret
  rw [hradius] at hret
  have hh:=hz.2 reflected left second (fixedParentUnit left s.η) key₀ hC hD heq
    (CenteredMomentAmplificationChildInput.volume s) D ampExponent reserveShift ξ εvolume (CenteredMomentAmplificationChildInput.volume_pos s) hξ (by
      simpa only [key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
        originalSecondBlock,hfirst] using hret)
  have hfreq : rawFrequencyNorm (nonzeroJointSourceRow key₀)≤Z^(x 2) := by
    simpa only [x,key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
      originalSecondBlock,hfirst,rawFrequencyNorm,nonzeroJointSourceRow,normValue] using hh.2
  cases second
  · exact hfreq
  · exact (reflected_joint_norm key₀).trans_le hfreq

/- Polynomial modulus argument adapted from Zhongpai Gao, accepted PR63,
Apache-2.0; source head 52419a826d4a8465cdeb56aaa2d471c489221d1d. -/
/-- The first geometric character retains the polynomial conductor bound
of its literal fixed pair. No bound on the second character is substituted
for the first modulus. -/
theorem column_modulus_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reflected : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (hK : 0 < K) (bin : ℤ × (Fin 5 → ℤ))
    (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin)) :
    let src := source s modifier R seed K Z ξ hK bin j.1
    ((columnCharacter reflected s modifier R seed K Z ξ hK bin j).modulus.absNorm : ℝ) ≤
      fixedPresentationCost * (s.η.modulus.absNorm : ℝ) * (src.C.absNorm : ℝ)^2 := by
  intro src
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  have hh := fixed_pair_caps s.η src.C src.D src.hC src.inactive
    j.2.2.1 j.2.2.2⁻¹ F
  cases reflected
  · exact hh.1
  · exact hh.2

/-- The hole ideal in the actual two-stage dictionary has polynomial
norm. Its first factor is controlled by the actual first source; its
second factor is exactly the retained state's puncture. -/
theorem eventually_holes_cap (η₀ : Character) (Bfirst Bmask : ℝ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
        (reflected second : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ), s.η = η₀ →
      ∀ (R seed : Ideal O) (K ξ : ℝ) (hK : 0 < K) (bin : ℤ × (Fin 5 → ℤ))
        (j : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
        (d : SecondInputDatum α) {bΦ : ℝ} (st : NaturalState Z Bmask bΦ),
      d.input.η = columnCharacter reflected s modifier R seed K Z ξ hK bin j →
      st.puncture = d.R * (if second then d.D else d.C) →
      ((source s modifier R seed K Z ξ hK bin j.1).C.absNorm : ℝ) ≤ Z^Bfirst →
      let holes := d.input.η.modulus * (d.R * (if second then d.D else d.C))
      holes ≠ 0 ∧ (holes.absNorm : ℝ) ≤ Z^(2*Bfirst+Bmask+1) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (fixedPresentationCost * (η₀.modulus.absNorm : ℝ))]
    with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro ι α _ _ _ _ reflected second s modifier hη R seed K ξ hK bin j d bΦ st hparent hpuncture hfirst holes
  have hholes : holes = d.input.η.modulus * st.puncture := by
    dsimp [holes]
    rw [hpuncture]
  rw [hholes]
  refine ⟨mul_ne_zero d.input.η.modulus_ne_bot st.puncture_ne_zero,?_⟩
  have hcap := column_modulus_cap reflected s modifier R seed K Z ξ hK bin j
  rw [←hparent,hη] at hcap
  have hZp : 0 < Z := zero_lt_one.trans hZ
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ (fixedPresentationCost * (η₀.modulus.absNorm : ℝ) *
        ((source s modifier R seed K Z ξ hK bin j.1).C.absNorm : ℝ)^2) *
        Z^Bmask := mul_le_mul hcap st.puncture_bound (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)) (sq_nonneg _))
    _ ≤ (Z * (Z^Bfirst)^2) * Z^Bmask := by gcongr
    _ = Z^(1:ℝ) * (Z^Bfirst)^2 * Z^Bmask := by rw [Real.rpow_one]
    _ = Z^(2*Bfirst+Bmask+1) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le,
        ←Real.rpow_add hZp,←Real.rpow_add hZp]
      congr 1
      norm_num
      ring

end
end QRH.Record1252270103Source.Admission.FirstFamily
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.coordinate_code_injective
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.column_code_injective
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.label_supported
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.label_common_bounds
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.label_missing_nonzero
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.live_projector_squarefree

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventual_literal_high_frequency

#print axioms QRH.Record1252270103Source.Admission.FirstFamily.column_modulus_cap
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventually_holes_cap
