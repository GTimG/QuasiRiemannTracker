/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorRatioPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorPuncture
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalizedMenuPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLossParameters
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorScalarTransport

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle63Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeElements
open CenteredMomentHeckeColumnWindow CenteredMomentSlotRatios CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource
open RayFourExpansion CenteredMomentSecondRadicalBudget CenteredMomentAmplificationRadicalFamily
open CenteredMomentSecondHeightFamily
open Cycle63InitialSource CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary

/-- Both second ideals are bounded for every literal raw block, including
rows with zero first allocation coefficient. The only allocation premise is
that every original slot scale is at least one. Fourier data uses card α. -/
theorem eventual_actual_geometry_error_second_caps_of_scales (N : ℕ)(b bs : ℝ)
    (hb : 1≤b)(hbs : 1≤bs) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp ξ reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → (∀j,1≤ s.P j) → volume s≤Z^(2:ℝ) →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
        (bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      ∀(p : O)(i : Fin 3),
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ)
        (n : GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
          (Fintype.card α) hZ bin q p i Bp υ v),
      let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hz₁ hz₂ n
      (d.C.absNorm:ℝ)≤Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤Z^(3:ℝ) := by
  filter_upwards [eventual_geometry_error_child_source_cap_of_scales N b bs 1 hb hbs (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hP hvolume hz₁ hz₂ bin q p i Bp υ v n d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  dsimp only [geometryLowFirstChild] at Bp
  have hchild := hz.2 s 2 hn hend hP hvolume _ R q.2 _ t (Ideal.span {p}) (errorIndex i+1)
    (errorActiveAllocation _ _ Bp) υ v
  have hchild3 : sourceRadius (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)≤Z^(3:ℝ) := by
    convert hchild using 1 <;> norm_num
    rfl
  have hseed1 := actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  have hrad := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  have hg := actual_retained_block_gates _
    (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)
    ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
    q.1.val.2.1.val hseed1 hz₁ hz₂
    (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)
    (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i)
    Z ξ hrad n
  exact ⟨hg.2.2.1.trans hchild3,hg.2.2.2.trans hchild3⟩

variable [Cycle63.AffineLedger] in
/-- Genuine affine source gates give the error mask `28 + Rcap` for every raw block of a
parent with first puncture of norm at most `Z^Rcap`, before any first-coefficient support
selection. The prime norm bound is arithmetic; no normalized energy estimate is assumed. -/
theorem eventual_actual_geometry_affine_error_puncture_of_scales (N : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (profile : Profiles (1/4) (9/4))(Cs M amp ξ reserve t Rcap : ℝ)(hZ : 1<Z)
      (caps : GeometryAffineExceptionalSourceGates s profile N Cs Z)
      (_hR : R≠0)(_hRcap : (R.absNorm:ℝ)≤Z^Rcap)(_hseed : Squarefree seed)(key : ℤ×(Fin 5→ℤ))
      (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
      (prime : O)(_hp : prime≠0)(_hpN : ((Ideal.span {prime}).absNorm:ℝ)≤Z^(3:ℝ))
      (i : Fin 3)
      (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)).pools
        ((Ideal.span {prime})^(errorIndex i+1))) (υ : Character)(v : ℝ)
      (n : GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve (9/4) t
        (Fintype.card α) hZ key q prime i Bp υ v)(second : Bool),
      let d:=geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve (9/4) t
        (Fintype.card α) hZ key q prime i Bp υ v caps.zero₁ caps.zero₂ n
      let puncture:=d.R*(if second then d.D else d.C)
      puncture≠0 ∧ (puncture.absNorm:ℝ)≤Z^(28+Rcap) := by
  filter_upwards [eventual_actual_geometry_error_second_caps_of_scales N (9/4) (9/4)
    (by norm_num) (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed profile Cs M amp ξ reserve t Rcap hZ caps hR hRcap hseed key q prime
    hp hpN i Bp υ v n second
  have hsecond:=hz.2 reflected s R seed M amp ξ reserve t hZ
    caps.card caps.endpoints caps.scales caps.volume caps.zero₁ caps.zero₂ key q prime i Bp υ v n
  exact actual_geometry_error_puncture reflected s R seed Z M amp ξ reserve (9/4) t Rcap hZ
    hR hRcap hseed caps.zero₁ caps.zero₂ caps.sourceCap key q prime hp hpN i Bp υ v n second hsecond

variable [Cycle63.AffineLedger] in
/-- The actual amplifier pool supplies both prime gates at every scale
above one. The cutoff exponent is independent of the live slot count. -/
theorem actual_affine_error_prime_norm_cap
    (rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (Z : ℝ)(hZ : 1<Z)(beta : ℝ)
    (hbeta : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop) :
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
      (Z^(Cycle63.AffineLedger.amp beta))
    ∀q : elementPool P,q.val≠0 ∧ ((Ideal.span {q.val}).absNorm:ℝ)≤Z^(3:ℝ) := by
  intro P q
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hgood q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (Finset.mem_sdiff.mp hq.2.1).1
  have hamp : Cycle63.AffineLedger.amp beta≤(3:ℝ) :=
    (Cycle63.AffineLedger.amp_bounds hbeta).2.trans (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  refine ⟨hq.1.ne_zero,?_⟩
  have hnorm : ((Ideal.span {q.val}).absNorm:ℝ)≤Z^(Cycle63.AffineLedger.amp beta) := by
    simpa only [one_mul,mul_one] using hn.2
  exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hamp)

variable [Cycle63.AffineLedger] in
/-- The actual annular pool supplies the extracted-error prime width.
The threshold is common to every amplifier cell and every prime element. -/
theorem eventual_actual_affine_error_prime_width
    (rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀beta : ℝ,
      Cycle63.AffineLedger.firstCellTop≤beta → beta≤Cycle63.AffineLedger.slotTop →
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
        (Z^(Cycle63.AffineLedger.amp beta))
      ∀q : elementPool P,
        Cycle63.AffineLedger.primeFraction*Cycle63.AffineLedger.amp beta≤Real.logb Z (normValue q.val) := by
  filter_upwards [Cycle63.Physical.actual_amplifier_prime_width rayM H Sbad 1 (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro beta hb₁ hb₂ P q
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hgood q.val q.property
  have hmem : Ideal.span {q.val}∈CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
      (Z^(1*Cycle63.AffineLedger.amp beta)) := by
    simpa only [one_mul] using hq.2.1
  simpa only [one_mul,normValue] using (hz.2 1 beta le_rfl hb₁ hb₂ (Ideal.span {q.val}) hmem).1

/-- Zero original first coefficients keep their first labels and contribute
zero undivided allocation weight. No support filter is introduced. -/
theorem actual_geometry_error_first_weight_zero
    {ι : Type*}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)
    (K Z ξ M A : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)(N : ℕ)(b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (alloc : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (hzero : frozenCoefficient alloc.val
      (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R s.ν s.W s.P=0) :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j alloc=0 := by
  simp only [geometryAllocationWeight,hzero,ne_eq,not_true_eq_false,ite_false]

/-- All raw second labels remain in the normalized sum when their common
first coefficient vanishes. The effective-weight filter still tests the
original full physical block. -/
theorem actual_geometry_error_zero_normalized_sum
    {ι Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
    (side : Bool)(datum : Label→SecondInputDatum ι)
    (windowProfile : 𝓢(ℝ,ℂ))(t u : ℝ) :
    secondNormalizedSum side datum
      (secondEffectiveWeight (fun n=>(datum n).block) (fun _=>0) windowProfile) t u=0 := by
  simp only [secondEffectiveWeight,ite_self,secondNormalizedSum,norm_zero,zero_mul,
    Finset.sum_const_zero]

variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorNormalizedFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

omit [DecidableEq α] in
/-- The actual constructor supplies the source scales and exact ray dictionary
needed by the normalized consumer. These gates precede error extraction. -/
theorem actual_affine_error_auxiliary_gates
    (η₀ : Character)(θ : α→RayQuotient.Characters rayM H)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : α→ℝ)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ}(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(hZ : 1<Z)
    (hw : ∀j,0≤w j)(hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    inp.b₁=9/4 ∧ inp.b₂=9/4 ∧
      (∀side j,Cycle63.Physical.sourcePlainScales inp.toData.toSource side j≤Z^(1:ℝ)) ∧
      (∀j,inp.P j≤Z^(1:ℝ)) ∧ (∀j,logWindow (inp.lo j) (inp.hi j)≤Real.log 2) ∧
      Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
  intro inp
  have hvol:=hwin.volume_le (Finset.sum_nonneg (fun i _=>hw i))
  have hplain:=affine_plain_caps rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) 1 t X₁ X₂ hX₁ hX₂
    1 hZ (by norm_num) le_rfl (Cycle63.AffineLedger.comparisonLength_nonneg _ _ _ hwin)
    (Cycle63.AffineLedger.comparisonLength_le _ _ _ hwin)
    (by linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hw i)])
  refine ⟨rfl,rfl,hplain,?_,?_,?_⟩
  · intro j
    have hj : w j≤1 := (Finset.single_le_sum (fun k _=>hw k) (Finset.mem_univ j)).trans
      (hwin.slots_le.trans Cycle63.AffineLedger.slotTop_le_one)
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hj
  · intro j
    change max |Real.log (1:ℝ)| |Real.log (2:ℝ)|≤Real.log 2
    simp only [Real.log_one,abs_zero,abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)),
      max_eq_right (Real.log_nonneg (by norm_num : (1:ℝ)≤2))]
    exact le_rfl
  · constructor <;> intros <;> rfl

section ErrorProjector
local instance affineErrorProjectorSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedPaymentSumDecidableEq

/-- The raw block pool is the literal twice-extracted dictionary. Every
stored squarefree projector inherits the original pool cap. -/
theorem actual_geometry_error_block_projector_cap
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(N Ncap : ℕ)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (prime : O)(i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first)).pools
      ((Ideal.span {prime})^(errorIndex i+1)))(υ : Character)(v : ℝ)
    (hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations (geometryErrorChild reflected s R seed Z Mrow ξ t hZ key first prime i Bp υ v).pools E₂)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key first prime i Bp υ v)
    (hN : Fintype.card α≤Ncap)(hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^(3:ℝ)) :
    let d:=geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key first prime i Bp υ v hw₁ hw₂ n
    ∀L∈d.block.divisors,L≠0 ∧ (L.absNorm:ℝ)≤Z^(((Ncap:ℝ)+2)*3) := by
  intro d L hL
  let chain:=geometryErrorChain reflected s R seed Z Mrow ξ t hZ key first prime i Bp υ v hp hcop E₂ R₂ B₂
  have hb : d.block.pool=finiteColumns (Fintype.piFinset chain.extracted.pools) := by
    rfl
  exact actual_error_extracted_projector_cap s chain Ncap Z 3 hN hZ.le (by norm_num) hpool d.block hb L hL

end ErrorProjector

attribute [local irreducible] geometryErrorSecondDatum affineInput

set_option linter.style.haveILetI false in
variable [Cycle63.AffineLedger] in
omit [DecidableEq α] in
/-- The original finite Fourier carrier is fixed before density degrees and
control profiles, at the puncture mask `Bmask`. Ambient cardinality chooses scalar
fees only; all actual source data in the normalized consumer continue to use card T. -/
theorem actual_finiteT_affine_error_normalized_menu
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (T : Finset α)(μ Cs Bmask : ℝ)(hμ : 0<μ)(hCs : 1≤Cs)(hBmask : 0≤Bmask)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) :
    letI : DecidableEq T := Classical.decEq T
    let N:=Fintype.card α
    let L₂:=3*((N:ℝ)+2)
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 L₂ N
    ∃degree : ℕ,∃Sp : Finset (ℕ×ℕ),∀η₀ : Character,∀Q : Ideal O,
      Q≤ rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃Cg : ℝ,0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
        geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=↥T) rayM H hH W 2 (1/4) (9/4) Bmask 1
          (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N)
          (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs L₂ δ Cg Sp degree η₀ Q Z := by
  letI : DecidableEq T := Classical.decEq T
  intro N L₂ δ
  have hδ : 0<δ := (geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).1
  have hdict : 0<geometryFinalErrorDictionaryRate μ N :=
    (geometry_final_error_dictionary_budget μ N hμ).1
  exact actual_geometry_error_paid_normalized_menu (α:=↥T) rayM H hH W
    1 2 (1/4) (9/4) Bmask 1 (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N) 1
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hBmask (by norm_num) (by norm_num) (by positivity) hdict (by norm_num) hbeta
    (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ
    (Real.log_nonneg (by norm_num)) hδ hδ (by norm_num) (by positivity) (by positivity) (by norm_num)
    N Cs L₂ δ hCs (by dsimp [L₂];positivity) hδ

variable [Cycle63.AffineLedger] in
/-- The scalar shell payment uses the exact frequency radius and common
error fee of the normalized menu. The ambient rate pays allocation and
shell losses once, after the original first weight has been retained. -/
theorem eventual_actual_affine_error_normalized_scalar_schedule
    (Cs εaffine : ℝ)(hCs : 1≤Cs)(hεaffine : 0<εaffine) :
    let μ:=geometryLossUnit 1 εaffine
    let N:=Fintype.card α
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      AffineErrorFrequencyLossScalarBound (α:=α) Cs (μ/8) (μ/8) εaffine δ (μ/64) δ K Z := by
  intro μ N δ
  have hμ : 0<μ := geometry_loss_unit_pos 1 εaffine (by norm_num) hεaffine
  have hδ : 0<δ := (geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)).1
  exact eventual_actual_affine_error_frequency_loss_payment (α:=α)
    Cs (μ/8) (μ/8) εaffine δ (μ/64) δ hCs (by positivity) (by positivity) hδ
    (by positivity) hδ

section NormalizedMenuSuffix
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorMenuSuffixSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

variable [Cycle63.AffineLedger] in
/-- The original normalized menu after the source prefix of a parent input, at ledger unit
one, radial scale `Mrow` and puncture mask `Bmask`. -/
def GeometryAffineErrorNormalizedMenuSuffix
    (s : Input α)(Z μ δ amp Cg : ℝ)(N : ℕ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (η₀ : Character)(Q : Ideal O)(height mesh Mrow Bmask : ℝ)(hZ : 1<Z) : Prop :=
  ∀(reserve : ℝ)(_hreserve : 0≤frequencyLoss Z 32 (μ/64)+reserve)
    (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
    (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
    (_hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (_hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
    (_hprime : Cycle63.AffineLedger.primeFraction*amp≤Real.logb Z (normValue prime)),
  ∀{Menu : Type}[Fintype Menu]{Blocks : Menu→Type}[∀j,Fintype (Blocks j)],
  let Label:=Sigma Blocks
  ∀(index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀),
  let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
  ∀(hne : ∀n : Label,(datum n).block.value ballProfile≠0)(_hinj : Function.Injective index)(second : Bool),
  let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
  let chains := fun n=>geometryErrorChain reflected s R seed Z Mrow (μ/64) t₀ hZ bin first prime i Bp υ v₀ hp hcop
    (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)

  ∀(_hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
    (_hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤Z^Bmask)
    (p : Profiles (1/4:ℝ) (9/4:ℝ))(_hp₁ : s.W₁=p.profile 0)(_hp₂ : s.W₂=p.profile 1)
    (a : ℝ)(_ha : 0<a)(_hlower : a≤ s.lower)
    (_hW₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤x)(_hW₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤x)
    (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→RayCharacter)
    (P : Finset (Ideal O))(weight : ℝ)(_hwgt : 0≤weight)
    (_hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤Z^(3*((N:ℝ)+2)))
    (tₑ u : ℝ),
  ∀(box : Finset (Fin 4→ℤ))
    (_hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow (μ/64) t₀ hZ bin first prime i Bp υ v₀)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*
          (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z Mrow amp (μ/64) reserve hZ bin first prime i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp (μ/64) reserve (9/4:ℝ) (Fintype.card α) hZ bin first prime i)
      Z (μ/64) (index n)∈box),
  let error:=(μ/8)*(1:ℝ)+(μ/64)/2+(μ/8)+(geometryFinalErrorDictionaryRate μ N)*(Fintype.card α:ℝ)+
    (frequencyLoss Z 32 (μ/64)+reserve+(μ/8)*(1:ℝ))/6+Cycle63.Optimization.slotPrice*mesh+δ
  geometryErrorNormalizedMenuLabelsConclusion reflected s R seed Z Mrow amp (μ/64) reserve (9/4:ℝ) t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile
    (Menu:=Menu) (Blocks:=Blocks) index χ₀ (internalQ Q η₀) second tₑ u N a (1/4:ℝ) Cg (p.control Sp) height
    δ (3*((N:ℝ)+2)) δ 1 error degree box
end NormalizedMenuSuffix

set_option linter.defProp false in
variable [Cycle63.AffineLedger] in
/-- A parent input with the source gates of the affine step supplies the normalized
consumer's source prefix at ledger unit one and radial scale `Mrow`. The remaining binders
are its original extraction and label gates. -/
def actual_affine_error_normalized_menu_parent_prefix
    (W : ℝ→ℂ)(N : ℕ)(μ δ Cs Cg Bmask : ℝ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (η₀ : Character)(Q : Ideal O)(Z : ℝ)(hZ : 1<Z)
    (hpaid : geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=α) rayM H hH W 2 (1/4) (9/4) Bmask 1
      (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N)
      (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs (3*((N:ℝ)+2)) δ Cg Sp degree η₀ Q Z)
    (s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z)
    (hb₁ : s.b₁=9/4)(hb₂ : s.b₂=9/4)
    (hplain : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^(1:ℝ))
    (hwindows : ∀j,logWindow (s.lo j) (s.hi j)≤Real.log 2)
    (θ : α→RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (Mrow : ℝ)(hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16)
    (height mesh : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 Bmask 1 (μ/8))
    (hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B) :=
  hpaid hZ s θ w σ freq height mesh caps.card caps.controls hm caps.endpoints.1 hb₁ hb₂
    hw hwL hmesh hwm (fun j=>(hσ j).1) (fun j=>(hσ j).2) hheight hfreq hplain hwindows
    1 Mrow (μ/64) le_rfl (by positivity) (by linarith only [hμcap,hμ])
    (by linarith only [hfit]) (by simpa only [mul_one] using hzslot)
    (by simpa only [mul_one] using haff)

section AlignedMenu
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorAlignedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

variable [Cycle63.AffineLedger] in
/-- The normalized menu of a parent input, with the amplifier of its own original cell
`beta`. -/
theorem actual_affine_error_normalized_menu_parent_aligned
    (W : ℝ→ℂ)(N : ℕ)(μ δ Cs Cg Bmask : ℝ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (η₀ : Character)(Q : Ideal O)(Z : ℝ)(hZ : 1<Z)
    (hpaid : geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=α) rayM H hH W 2 (1/4) (9/4) Bmask 1
      (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N)
      (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs (3*((N:ℝ)+2)) δ Cg Sp degree η₀ Q Z)
    (s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z)
    (hb₁ : s.b₁=9/4)(hb₂ : s.b₂=9/4)
    (hplain : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^(1:ℝ))
    (hwindows : ∀j,logWindow (s.lo j) (s.hi j)≤Real.log 2)
    (θ : α→RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (Mrow : ℝ)(hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16)
    (height mesh : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 Bmask 1 (μ/8))
    (hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (beta : ℝ)(hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))) :
    GeometryAffineErrorNormalizedMenuSuffix s Z μ δ (Cycle63.AffineLedger.amp beta)
      Cg N Sp degree η₀ Q height mesh Mrow Bmask hZ := by
  have paid:=actual_affine_error_normalized_menu_parent_prefix rayM H hH W N μ δ Cs Cg Bmask Sp degree
    η₀ Q Z hZ hpaid s p caps hb₁ hb₂ hplain hwindows θ w σ freq hm Mrow hfit height mesh hμ hμcap
    hw hwL hmesh hwm hσ hheight hfreq hzslot haff
  have hr : (1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))=
      Cycle63.AffineLedger.amp beta := by
    rw [div_one,one_mul,hbeta]
  -- Transport the complete amplifier before the dependent allocation and
  -- label binders. Only this small scalar equality needs unification.
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let paid ← Lean.Meta.getFVarFromUserName `paid
      let hr ← Lean.Meta.getFVarFromUserName `hr
      let tp ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← Lean.Meta.inferType paid))
      let isAmpMul := fun e : Lean.Expr => e.isAppOf ``HMul.hMul && e.getAppArgs.size == 6 &&
        e.getAppArgs[5]?.any (fun a=>a.isAppOf ``Cycle63.AffineLedger.amp)
      let some candidate := tp.find? isAmpMul
        | throwError "source amplitude expression absent"
      let ht ← Lean.Meta.whnf (← Lean.Meta.inferType hr)
      let some (_, lhs, rhs) := ht.eq? | throwError "source amplifier equality expected"
      unless ← Lean.Meta.isDefEq candidate lhs do
        throwError "source amplitude mismatch: {candidate} / {lhs}"
      Lean.Meta.withLocalDeclD `amplitude (Lean.mkConst ``Real) fun rate => do
        let body := (tp.replace fun e => if e == candidate then some rate else none).abstract #[rate]
        unless body.hasLooseBVars do throwError "source amplifier was not syntactically present"
        let fn := Lean.mkLambda `amplitude .default (Lean.mkConst ``Real) body
        let congr := Lean.mkAppN (Lean.mkConst ``congrArg [Lean.Level.succ Lean.Level.zero,
          Lean.Level.succ Lean.Level.zero]) #[Lean.mkConst ``Real,Lean.mkSort Lean.Level.zero,candidate,rhs,fn,hr]
        let proof := Lean.mkAppN (Lean.mkConst ``Eq.mp [Lean.Level.zero])
          #[body.instantiate1 candidate,body.instantiate1 rhs,congr,paid]
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []

end AlignedMenu

section NormalizedLabelGates
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorFullSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

/-- Selected allocation transport preserves the literal raw puncture and
original projector pool. The nonzero premise tests the full physical block. -/
theorem actual_geometry_error_normalized_label_gates
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t Bmask : ℝ)(N Ncap : ℕ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (prime : O)(i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first)).pools
      ((Ideal.span {prime})^(errorIndex i+1)))(υ : Character)(v : ℝ)
    (hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hN : Fintype.card α≤Ncap)(hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^(3:ℝ))
    {Label : Type*}[Fintype Label]
    (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v)
    (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n)).block.value ballProfile≠0)
    (side : Bool)
    (hpuncture : ∀n : Label,
      let d:=geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
        hZ key first prime i Bp υ v hz₁ hz₂ (index n)
      d.R*(if side then d.D else d.C)≠0 ∧
        ((d.R*(if side then d.D else d.C)).absNorm:ℝ)≤Z^Bmask) :
    let datum:=fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n)
    let alloc:=fun n : Label=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n) (hne n) side
    let chains:=fun n : Label=>geometryErrorChain reflected s R seed Z Mrow ξ t hZ key first prime i Bp υ v hp hcop
      (if side then (datum n).D else (datum n).C) (datum n).R (alloc n)
    (∀n : Label,(chains n).R₂*(chains n).E₂≠0 ∧
      (((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤Z^Bmask) ∧
      (∀n : Label,∀D∈(datum n).block.divisors.filter Squarefree,
        (D.absNorm:ℝ)≤Z^(3*((Ncap:ℝ)+2))) := by
  intro datum alloc chains
  refine ⟨?_,?_⟩
  · intro n
    exact hpuncture n
  · intro n D hD
    have hdiv:=Finset.mem_filter.mp hD
    have hc:=actual_geometry_error_block_projector_cap reflected s R seed Z Mrow amp ξ reserve b t N Ncap
      hZ key first prime i Bp υ v hp hcop (if side then (datum n).D else (datum n).C)
      (datum n).R (alloc n) hz₁ hz₂ (index n) hN hpool D hdiv.1
    simpa only [mul_comm] using hc.2

end NormalizedLabelGates

section RawAffineMenu
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorRawMenuSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

set_option linter.defProp false in
variable [Cycle63.AffineLedger] in
/-- The whole original nonzero second-block filter of a parent is one menu. No menu
cardinality fee is introduced, and its first allocation weight stays undivided. -/
def actual_geometry_affine_error_raw_normalized_menu
    (s : Input α)(R seed : Ideal O)(Z μ δ amp Cs Cg Mrow Bmask : ℝ)(N : ℕ)(Sp : Finset (ℕ×ℕ))
    (degree : ℕ)(η₀ : Character)(Q : Ideal O)(height mesh : ℝ)(hZ : 1<Z)
    (p : Profiles (1/4) (9/4))(caps : GeometryAffineExceptionalSourceGates s p N Cs Z)
    (hpaid : GeometryAffineErrorNormalizedMenuSuffix s Z μ δ amp Cg N Sp degree η₀ Q height mesh
      Mrow Bmask hZ)
    (hreserve : 0≤frequencyLoss Z 32 (μ/64)+μ/8)
    (reflected : Bool)(t : ℝ)(key : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first)).pools
      ((Ideal.span {prime})^(errorIndex i+1)))(υ : Character)(v : ℝ)(ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val) R s.ν s.W s.P≠0)
    (hprime : Cycle63.AffineLedger.primeFraction*amp≤Real.logb Z (normValue prime))
    (hpuncture : ∀n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
      (Fintype.card α) hZ key first prime i Bp υ v,∀side : Bool,
      let d:=geometryErrorSecondDatum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
        (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂ n
      d.R*(if side then d.D else d.C)≠0 ∧
        ((d.R*(if side then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤weight)
    (windowProfile : 𝓢(ℝ,ℂ))(side : Bool)(tₑ u : ℝ)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
      (Fintype.card α) hZ key first prime i Bp υ v,
      actualSecondDyad (geometryErrorChild reflected s R seed Z Mrow (μ/64) t hZ key first prime i Bp υ v)
        ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val)*
            (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
        (geometryErrorSourceRadius reflected s R seed Z Mrow amp (μ/64) (μ/8) hZ key first prime i)
        (geometryErrorFourierScale reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4)
          (Fintype.card α) hZ key first prime i) Z (μ/64) n∈box) :=
  let Label:=geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂
  let index:=fun n : Sigma (fun _ : Unit=>↥Label)=>n.2.val
  let hne : ∀n : Sigma (fun _ : Unit=>↥Label),
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
        (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂ (index n)).block.value ballProfile≠0:=
    fun n=>(Finset.mem_filter.mp n.2.property).2
  let hinj : Function.Injective index:=by
    intro a b hab
    cases a with | mk a an=>
      cases b with | mk b bn=>
        cases a;cases b
        exact congrArg (fun n : ↥Label=>@Sigma.mk Unit (fun _=>↥Label) () n) (Subtype.ext hab)
  let gates:=actual_geometry_error_normalized_label_gates reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
    Bmask (Fintype.card α) N hZ key first prime i Bp υ v hp hcop caps.zero₁ caps.zero₂ caps.card caps.poolCap
    index hne side (fun n=>hpuncture (index n) side)
  hpaid (μ/8) hreserve reflected R seed t key first prime i hp hcop Bp υ v caps.zero₁ caps.zero₂ ψ hυ hf₁ hprime
    (Menu:=Unit) (Blocks:=fun _=>↥Label) index hne hinj side
    (fun n=>(gates.1 n).1) (fun n=>(gates.1 n).2) p caps.profile₁ caps.profile₂ 1 (by norm_num)
    (by rw [caps.lower]) caps.support₁ caps.support₂ windowProfile (fun _=>(1:RayCharacter)) P weight hwgt
    gates.2 tₑ u box (fun n=>hbox (index n))

end RawAffineMenu

end
end OAI.SevenEighths.Cycle63InitialMass
