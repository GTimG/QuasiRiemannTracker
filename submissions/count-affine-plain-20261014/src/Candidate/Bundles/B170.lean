/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B090
import Candidate.Bundles.B135
import Candidate.Bundles.B140
import Candidate.Bundles.B155
import Candidate.Bundles.B159
import Candidate.Bundles.B162
import Candidate.Bundles.B163
import Candidate.Bundles.B164
import Candidate.Bundles.B165
import Candidate.Bundles.B168
import Candidate.Bundles.B169

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorNormalized; sha256 7e52c13b7409196741b6b972f17467454215143ea82c1a1d03217e4f4ba318f9 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                   
                                                               
                                                                  
                                                              
                                                            
                                                                  
                                        
                                                                      
                                                               

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeElements
open CenteredMomentHeckeColumnWindow CenteredMomentSlotRatios CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource
open RayFourExpansion CenteredMomentSecondRadicalBudget CenteredMomentAmplificationRadicalFamily
open CenteredMomentSecondHeightFamily
open Cycle61InitialSource CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

/-- Both second ideals are bounded for every literal raw block, including
rows with zero first allocation coefficient. The only allocation premise is
that every original slot scale is at least one. Fourier data uses card α. -/
theorem eventual_actual_geometry_error_second_caps_of_scales (N : ℕ)(b bs : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp ξ reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → (∀j,1≤ s.P j) → volume s≤ Z^(2:ℝ) →
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
      (d.C.absNorm:ℝ)≤ Z^(3:ℝ) ∧ (d.D.absNorm:ℝ)≤ Z^(3:ℝ) := by
  filter_upwards [eventual_geometry_error_child_source_cap_of_scales N b bs 1 hb hbs (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s R seed M amp ξ reserve t hZ hn hend hP hvolume hz₁ hz₂ bin q p i Bp υ v n d
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  dsimp only [geometryLowFirstChild] at Bp
  have hchild := hz.2 s 2 hn hend hP hvolume _ R q.2 _ t (Ideal.span {p}) (errorIndex i+1)
    (errorActiveAllocation _ _ Bp) υ v
  have hchild3 : sourceRadius (geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v)≤ Z^(3:ℝ) := by
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

/-- Genuine affine source gates give the common error mask for every raw
block before any first-coefficient support selection. The prime norm bound
is arithmetic; no normalized energy estimate is assumed. -/
theorem eventual_actual_geometry_affine_error_puncture_of_scales (N : ℕ) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (reflected : Bool)(s : Input α)(seed : Ideal O)
      (profile : Profiles (1/4) (9/4))(Cs amp ξ reserve t : ℝ)(hZ : 1< Z)
      (caps : GeometryAffineExceptionalSourceGates s profile N Cs Z)
      (_hseed : Squarefree seed)(key : ℤ×(Fin 5→ℤ))
      (q : GeometryLowFirstIndex reflected s 1 seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
      (prime : O)(_hp : prime≠0)(_hpN : ((Ideal.span {prime}).absNorm:ℝ)≤ Z^(3:ℝ))
      (i : Fin 3)
      (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s 1 seed (Z^(1:ℝ)) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)).pools
        ((Ideal.span {prime})^(errorIndex i+1))) (υ : Character)(v : ℝ)
      (n : GeometryErrorSecondIndex reflected s 1 seed Z 1 amp ξ reserve (9/4) t
        (Fintype.card α) hZ key q prime i Bp υ v)(second : Bool),
      let d:=geometryErrorSecondDatum reflected s 1 seed Z 1 amp ξ reserve (9/4) t
        (Fintype.card α) hZ key q prime i Bp υ v caps.zero₁ caps.zero₂ n
      let puncture:=d.R*(if second then d.D else d.C)
      puncture≠0 ∧ (puncture.absNorm:ℝ)≤ Z^(28:ℝ) := by
  filter_upwards [eventual_actual_geometry_error_second_caps_of_scales N (9/4) (9/4)
    (by norm_num) (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ _ reflected s seed profile Cs amp ξ reserve t hZ caps hseed key q prime hp hpN i Bp υ v n second
  have hsecond:=hz.2 reflected s 1 seed (1:ℝ) amp ξ reserve t hZ
    caps.card caps.endpoints caps.scales caps.volume caps.zero₁ caps.zero₂ key q prime i Bp υ v n
  exact actual_geometry_error_puncture reflected s seed Z 1 amp ξ reserve (9/4) t hZ
    hseed caps.zero₁ caps.zero₂ caps.sourceCap key q prime hp hpN i Bp υ v n second hsecond

/-- The actual amplifier pool supplies both prime gates at every scale
above one. The cutoff exponent is independent of the live slot count. -/
theorem actual_affine_error_prime_norm_cap
    (rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (Z : ℝ)(hZ : 1< Z)(beta : ℝ)
    (hbeta : 3401/100000≤ beta ∧ beta≤1/25) :
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
      (Z^(Cycle61.Arithmetic.amp beta))
    ∀q : elementPool P,q.val≠0 ∧ ((Ideal.span {q.val}).absNorm:ℝ)≤ Z^(3:ℝ) := by
  intro P q
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hgood q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (Finset.mem_sdiff.mp hq.2.1).1
  have hamp : Cycle61.Arithmetic.amp beta≤(3:ℝ) :=
    (Cycle61.Arithmetic.amp_bounds hbeta).2.trans (by norm_num)
  refine ⟨hq.1.ne_zero,?_⟩
  have hnorm : ((Ideal.span {q.val}).absNorm:ℝ)≤ Z^(Cycle61.Arithmetic.amp beta) := by
    simpa only [one_mul,mul_one] using hn.2
  exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hamp)


/-- The actual annular pool supplies the extracted-error prime width.
The threshold is common to every amplifier cell and every prime element. -/
theorem eventual_actual_affine_error_prime_width
    (rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀beta : ℝ,
      3401/100000≤ beta → beta≤1/25 →
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
        (Z^(Cycle61.Arithmetic.amp beta))
      ∀q : elementPool P,
        3*Cycle61.Arithmetic.amp beta/4≤ Real.logb Z (normValue q.val) := by
  filter_upwards [Cycle61.Physical.actual_amplifier_prime_width rayM H Sbad 1 (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro beta hb₁ hb₂ P q
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hgood q.val q.property
  have hmem : Ideal.span {q.val}∈CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
      (Z^(1*Cycle61.Arithmetic.amp beta)) := by
    simpa only [one_mul] using hq.2.1
  simpa only [one_mul,normValue] using (hz.2 1 beta le_rfl hb₁ hb₂ (Ideal.span {q.val}) hmem).1


/-- Zero original first coefficients keep their first labels and contribute
zero undivided allocation weight. No support filter is introduced. -/
theorem actual_geometry_error_first_weight_zero
    {ι : Type*}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)
    (K Z ξ M A : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)(N : ℕ)(b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (alloc : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (hzero : frozenCoefficient alloc.val
      (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R s.ν s.W s.P=0) :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j alloc=0 := by
  simp only [geometryAllocationWeight,hzero,ne_eq,not_true_eq_false,ite_false]

/-- The original zero first weight survives the single prime normalization
and child-volume division without discarding a label. -/
theorem actual_geometry_error_normalized_coefficient_zero
    (P : Finset (Ideal O))(V : ℝ)(prime : O)(i : Fin 3) :
    errorNormalizedCoefficient P 0 V prime i=0 := by
  simp only [errorNormalizedCoefficient,mul_zero,zero_mul,zero_div]


/-- All raw second labels remain in the normalized sum when their common
first coefficient vanishes. The effective-weight filter still tests the
original full physical block. -/
theorem actual_geometry_error_zero_normalized_sum
    {ι Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
    (side : Bool)(datum : Label→ SecondInputDatum ι)
    (windowProfile : 𝓢(ℝ,ℂ))(t u : ℝ) :
    secondNormalizedSum side datum
      (secondEffectiveWeight (fun n=>(datum n).block) (fun _=>0) windowProfile) t u=0 := by
  simp only [secondEffectiveWeight,ite_self,secondNormalizedSum,norm_zero,zero_mul,
    Finset.sum_const_zero]


variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorNormalizedFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤ H)


omit [DecidableEq α] in
/-- The actual constructor supplies the source scales and exact ray dictionary
needed by the normalized consumer. These gates precede error extraction. -/
theorem actual_affine_error_auxiliary_gates
    (η₀ : Character)(θ : α→ RayQuotient.Characters rayM H)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : α→ℝ)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ}(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)(hZ : 1< Z)
    (hw : ∀j,0≤ w j)(hslots : (∑j,w j)≤1/25)
    (hhi₁ : length Z X₁≤44/100)(hhi₂ : length Z X₂≤44/100) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    inp.b₁=9/4 ∧ inp.b₂=9/4 ∧
      (∀side j,Cycle61.Physical.sourcePlainScales inp.toData.toSource side j≤ Z^(1:ℝ)) ∧
      (∀j,inp.P j≤ Z^(1:ℝ)) ∧ (∀j,logWindow (inp.lo j) (inp.hi j)≤ Real.log 2) ∧
      Matches rayM H hH inp η₀ θ w σ freq W 2 Z := by
  intro inp
  have hplain:=affine_plain_caps rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hZ (by norm_num) le_rfl (by simpa using hhi₁) (by simpa using hhi₂)
  refine ⟨rfl,rfl,hplain,?_,?_,?_⟩
  · intro j
    have hj : w j≤1 := (Finset.single_le_sum (fun k _=>hw k) (Finset.mem_univ j)).trans
      (hslots.trans (by norm_num))
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hj
  · intro j
    change max |Real.log (1:ℝ)| |Real.log (2:ℝ)|≤ Real.log 2
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
    (Z Mrow amp ξ reserve b t : ℝ)(N Ncap : ℕ)(hZ : 1< Z)
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
    (hN : Fintype.card α≤ Ncap)(hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^(3:ℝ)) :
    let d:=geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key first prime i Bp υ v hw₁ hw₂ n
    ∀L∈d.block.divisors,L≠0 ∧ (L.absNorm:ℝ)≤ Z^(((Ncap:ℝ)+2)*3) := by
  intro d L hL
  let chain:=geometryErrorChain reflected s R seed Z Mrow ξ t hZ key first prime i Bp υ v hp hcop E₂ R₂ B₂
  have hb : d.block.pool=finiteColumns (Fintype.piFinset chain.extracted.pools) := by
    rfl
  exact actual_error_extracted_projector_cap s chain Ncap Z 3 hN hZ.le (by norm_num) hpool d.block hb L hL

end ErrorProjector


omit [DecidableEq α] in
/-- The normalized slot rate and amplifier cell are read from the original
affine scales. Extraction never replaces the cell's input rate. -/
theorem actual_affine_error_cell_gates
    (η₀ : Character)(θ : α→ RayQuotient.Characters rayM H)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : α→ℝ)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ}(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)(hZ : 1< Z)
    (hslots : (17/500:ℝ)≤∑j,w j ∧ (∑j,w j)≤1/25)
    (haff : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑j,w j)≤ Cycle61.Arithmetic.B) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let rate:=∑j,Real.logb Z (inp.P j)
    rate=∑j,w j ∧ ((17/500:ℝ)≤ rate ∧ rate≤1/25) ∧
      (length Z inp.X₁+length Z inp.X₂+Cycle61.Arithmetic.lambda*rate≤ Cycle61.Arithmetic.B) ∧
      (3401/100000≤ Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell rate) ∧
        Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell rate)≤1/25) := by
  intro inp rate
  have hr : rate=∑j,w j := by
    apply Finset.sum_congr rfl
    intro j _
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hcell:=Cycle61.Moment.originalCell_mem hslots
  have hb:=Cycle61.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  refine ⟨hr,?_,?_,?_⟩
  · simpa only [hr] using hslots
  · rw [hr]
    change length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑j,w j)≤ Cycle61.Arithmetic.B
    exact haff
  · simpa only [hr] using hb

attribute [local irreducible] geometryErrorSecondDatum affineInput

/-- The actual finite Fourier family supplies every raw error puncture.
The common threshold precedes the live subset, parent state, first label,
amplifier prime and second label; no coefficient support is assumed. -/
theorem eventual_actual_affine_error_source_and_puncture
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2) :
    ∃Cs : ℝ,1≤ Cs ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→ RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
        (η : Character)(Q : Ideal O)(Φ : 𝓢(ℝ,ℂ))(bΦ : ℝ)
        (hs : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp : ∀x,0≤(Φ x).re)
        (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)(hZ : 1< Z),
      (∀j,0≤ w j) → (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
      length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑j,w j)≤(1/25:ℝ) →
      let state:=fixedParentState η Q Φ bΦ Z 1 hZ (by norm_num) hs hp
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      ∃caps : GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z,
        inp.η=η ∧ ∀(beta : ℝ)(_hbeta : 3401/100000≤ beta ∧ beta≤1/25)
          (reflected : Bool)(ξ reserve : ℝ)(key : ℤ×(Fin 5→ℤ))
          (first : GeometryLowFirstIndex reflected inp 1 1 (Z^(1:ℝ)) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
        let pool:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
          (Z^(Cycle61.Arithmetic.amp beta))
        ∀(prime : elementPool pool)(i : Fin 3)
          (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected inp 1 1 (Z^(1:ℝ)) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first)).pools
            ((Ideal.span {prime.val})^(errorIndex i+1))) (υ : Character)(v : ℝ)
          (n : GeometryErrorSecondIndex reflected inp 1 1 Z 1 (Cycle61.Arithmetic.amp beta) ξ reserve (9/4) t
            (Fintype.card T) hZ key first prime.val i Bp υ v)(second : Bool),
        let d:=geometryErrorSecondDatum reflected inp 1 1 Z 1 (Cycle61.Arithmetic.amp beta) ξ reserve (9/4) t
          (Fintype.card T) hZ key first prime.val i Bp υ v caps.zero₁ caps.zero₂ n
        let puncture:=d.R*(if second then d.D else d.C)
        puncture≠0 ∧ (puncture.absNorm:ℝ)≤ Z^(28:ℝ) := by
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW hWs
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [hcaps,eventual_actual_geometry_affine_error_puncture_of_scales (Fintype.card α)] with Z hc he
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ η Q Φ bΦ hs hp p t X₁ X₂ hX₁ hX₂ hZ hw hlo₁ hlo₂ hhi₁ hhi₂ hsum state inp
  have caps:=hc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hsum
  have heta : inp.η=η := by
    unfold inp affineInput
    rfl
  refine ⟨caps,heta,?_⟩
  intro beta hbeta reflected ξ reserve key first pool prime i Bp υ v n second
  have hprime:=actual_affine_error_prime_norm_cap rayM H Sbad hbad Z hZ beta hbeta prime
  exact he.2 (α:=↥T) reflected inp 1 p Cs (Cycle61.Arithmetic.amp beta) ξ reserve t hZ caps
    squarefree_one key first prime.val hprime.1 hprime.2 i Bp υ v n second


set_option linter.style.haveILetI false in
/-- The original finite Fourier carrier is fixed before density degrees and
control profiles. Ambient cardinality chooses scalar fees only; all actual
source data in the normalized consumer continue to use card T. -/
theorem actual_finiteT_affine_error_normalized_menu
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (T : Finset α)(ηseed : Character)(μ Cs : ℝ)(hμ : 0<μ)(hCs : 1≤ Cs)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta) :
    letI : DecidableEq T := Classical.decEq T
    let N:=Fintype.card α
    let L₂:=3*((N:ℝ)+2)
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 L₂ N
    ∃degree : ℕ,∃Sp : Finset (ℕ×ℕ),∀η₀ : Character,∀Q : Ideal O,
      Q≤ rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
      ∃Cg : ℝ,0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
        geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=↥T) rayM H hH W 2 (1/4) (9/4) 28 1
          (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N) ηseed
          (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs L₂ δ Cg Sp degree η₀ Q Z := by
  letI : DecidableEq T := Classical.decEq T
  intro N L₂ δ
  have hδ : 0<δ := (geometry_final_dictionary_budgets μ 31 3 4 3 130 L₂ N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by dsimp [L₂];positivity)).1
  have hdict : 0< geometryFinalErrorDictionaryRate μ N :=
    (geometry_final_error_dictionary_budget μ N hμ).1
  exact actual_geometry_error_paid_normalized_menu (α:=↥T) rayM H hH W
    1 2 (1/4) (9/4) 28 1 (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N) 1
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) hdict (by norm_num) hbeta
    ηseed (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ
    (Real.log_nonneg (by norm_num)) hδ hδ (by norm_num) (by positivity) (by positivity) (by norm_num)
    N Cs L₂ δ hCs (by dsimp [L₂];positivity) hδ



/-- The scalar shell payment uses the exact frequency radius and common
error fee of the normalized menu. The ambient rate pays allocation and
shell losses once, after the original first weight has been retained. -/
theorem eventual_actual_affine_error_normalized_scalar_schedule
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εaffine mesh : ℝ)(hεaffine : 0<εaffine)
    (hmesh : mesh<(62485051/9854400000:ℝ)/2) :
    let μ:=geometryLossUnit 1 εaffine
    let N:=Fintype.card α
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      AffineErrorFrequencyLossScalarBound (α:=α) rayM H hH Sbad W hW hWs
        (μ/8) (μ/8) εaffine δ (μ/64) δ mesh K Z := by
  intro μ N δ
  have hμ : 0<μ := geometry_loss_unit_pos 1 εaffine (by norm_num) hεaffine
  have hδ : 0<δ := (geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((N:ℝ)+2)) N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)).1
  exact eventual_actual_affine_error_frequency_loss_payment (α:=α) rayM H hH Sbad hbad W hW hWs
    (μ/8) (μ/8) εaffine δ (μ/64) δ mesh (by positivity) (by positivity) hδ
    (by positivity) hδ hmesh


section NormalizedMenuSuffix
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorMenuSuffixSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

/-- The original normalized menu after its actual affine source prefix. -/
def GeometryAffineErrorNormalizedMenuSuffix
    (s : Input α)(Z μ δ amp Cg : ℝ)(N : ℕ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (η₀ : Character)(Q : Ideal O)(height mesh : ℝ)(hZ : 1< Z) : Prop :=
  ∀(reserve : ℝ)(hreserve : 0≤ frequencyLoss Z 32 (μ/64)+reserve)
    (reflected : Bool)(R seed : Ideal O)(t₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t₀ first)).pools ((Ideal.span {prime})^(errorIndex i+1)))
    (υ : Character)(v₀ : ℝ)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val) R s.ν s.W s.P≠0)
    (hprime : 3*amp/4≤ Real.logb Z (normValue prime)),
  ∀{Menu : Type}[Fintype Menu]{Blocks : Menu→ Type}[∀j,Fintype (Blocks j)],
  let Label:=Sigma Blocks
  ∀(index : Label→ GeometryErrorSecondIndex reflected s R seed Z (1:ℝ) amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀),
  let datum := fun n : Label=>geometryErrorSecondDatum reflected s R seed Z (1:ℝ) amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n)
  ∀(hne : ∀n : Label,(datum n).block.value ballProfile≠0)(hinj : Function.Injective index)(second : Bool),
  let alloc := fun n=>geometryErrorSelectedAllocation reflected s R seed Z (1:ℝ) amp (μ/64) reserve (9/4:ℝ) t₀ (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ (index n) (hne n) second
  let chains := fun n=>geometryErrorChain reflected s R seed Z (1:ℝ) (μ/64) t₀ hZ bin first prime i Bp υ v₀ hp hcop
    (if second then (datum n).D else (datum n).C) (datum n).R (alloc n)

  ∀(hP : ∀n,(chains n).R₂*(chains n).E₂≠0)
    (hPN : ∀n,(((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤ Z^(28:ℝ))
    (p : Profiles (1/4:ℝ) (9/4:ℝ))(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
    (a : ℝ)(ha : 0< a)(hlower : a≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤ x)(hW₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤ x)
    (windowProfile : 𝓢(ℝ,ℂ))(χ₀ : Label→ RayCharacter)
    (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤ weight)
    (hcap : ∀n D,D∈(datum n).block.divisors.filter Squarefree→(D.absNorm:ℝ)≤ Z^(3*((N:ℝ)+2)))
    (tₑ u : ℝ),
  ∀(box : Finset (Fin 4→ℤ))
    (hbox : ∀n : Label,actualSecondDyad
      (geometryErrorChild reflected s R seed Z (1:ℝ) (μ/64) t₀ hZ bin first prime i Bp υ v₀)
      ((R*geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin first.1.val)*
          (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z (1:ℝ) amp (μ/64) reserve hZ bin first prime i)
      (geometryErrorFourierScale reflected s R seed Z (1:ℝ) amp (μ/64) reserve (9/4:ℝ) (Fintype.card α) hZ bin first prime i)
      Z (μ/64) (index n)∈box),
  let error:=(μ/8)*(1:ℝ)+(μ/64)/2+(μ/8)+(geometryFinalErrorDictionaryRate μ N)*(Fintype.card α:ℝ)+
    (frequencyLoss Z 32 (μ/64)+reserve+(μ/8)*(1:ℝ))/6+(3/4)*mesh+δ
  geometryErrorNormalizedMenuLabelsConclusion reflected s R seed Z (1:ℝ) amp (μ/64) reserve (9/4:ℝ) t₀
    (Fintype.card α) hZ bin first prime i Bp υ v₀ hw₁ hw₂ P weight windowProfile
    (Menu:=Menu) (Blocks:=Blocks) index χ₀ (internalQ Q η₀) second tₑ u N a (1/4:ℝ) Cg (p.control Sp) height
    δ (3*((N:ℝ)+2)) δ error degree box
end NormalizedMenuSuffix
set_option linter.defProp false in
/-- The actual affine constructor supplies the normalized consumer's source
prefix. The remaining binders are its original extraction and label gates. -/
def actual_affine_error_normalized_menu_source_prefix
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (N : ℕ)(μ δ Cs Cg : ℝ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (ηseed η₀ : Character)(Q : Ideal O)(Z : ℝ)(hZ : 1< Z)
    (hpaid : geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=α) rayM H hH W 2 (1/4) (9/4) 28 1
      (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N) ηseed
      (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs (3*((N:ℝ)+2)) δ Cg Sp degree η₀ Q Z)
    (θ : α→ RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    {bΦ : ℝ}(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8))
    (hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
    (hslots : (17/500:ℝ)≤∑j,w j ∧ (∑j,w j)≤1/25)
    (hhi₁ : length Z X₁≤44/100)(hhi₂ : length Z X₂≤44/100)
    (haff : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑j,w j)≤ Cycle61.Arithmetic.B)
    (caps : GeometryAffineExceptionalSourceGates
      (affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂) p N Cs Z) :=
  let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
  let aux:=actual_affine_error_auxiliary_gates rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hw hslots.2 hhi₁ hhi₂
  let cell:=actual_affine_error_cell_gates rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hslots haff
  hpaid hZ inp θ w σ freq height mesh caps.card caps.controls aux.2.2.2.2.2
    (by unfold inp affineInput;exact hη) caps.endpoints.1 aux.1 aux.2.1
    hw hwL hmesh hwm (fun j=>(hσ j).1) (fun j=>(hσ j).2) hheight hfreq
    aux.2.2.1 aux.2.2.2.2.1 1 (μ/64) (by norm_num) (by positivity)
    (by linarith only [hμcap]) (by simpa only [mul_one] using cell.2.1)
    (by simpa only [mul_one] using cell.2.2.1)


section AlignedMenu
attribute [local semireducible] geometryErrorSecondDatum
local instance affineErrorAlignedSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) :=
  errorNormalizedFullFamilySumDecidableEq

theorem actual_affine_error_normalized_menu_source_aligned
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (N : ℕ)(μ δ Cs Cg : ℝ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (ηseed η₀ : Character)(Q : Ideal O)(Z : ℝ)(hZ : 1< Z)
    (hpaid : geometryErrorNormalizedMenuDynamicSpec.{0,0} (α:=α) rayM H hH W 2 (1/4) (9/4) 28 1
      (33/50) (33/50) 2 (μ/8) (geometryFinalErrorDictionaryRate μ N) ηseed
      (9/4) (μ/8) (μ/8) 1 (Real.log 2) δ δ N Cs (3*((N:ℝ)+2)) δ Cg Sp degree η₀ Q Z)
    (θ : α→ RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    {bΦ : ℝ}(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)
    (hw : ∀j,0≤ w j)(hwL : ∀j,w j≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8))
    (hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)(hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)
    (hslots : (17/500:ℝ)≤∑j,w j ∧ (∑j,w j)≤1/25)
    (hhi₁ : length Z X₁≤44/100)(hhi₂ : length Z X₂≤44/100)
    (haff : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑j,w j)≤ Cycle61.Arithmetic.B)
    (caps : GeometryAffineExceptionalSourceGates
      (affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂) p N Cs Z) :
    let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    GeometryAffineErrorNormalizedMenuSuffix inp Z μ δ
      (Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑j,w j))))
      Cg N Sp degree η₀ Q height mesh hZ := by
  intro inp
  have paid:=actual_affine_error_normalized_menu_source_prefix rayM H hH W hW hWs
    N μ δ Cs Cg Sp degree ηseed η₀ Q Z hZ hpaid θ w σ freq hσ state hη p
    t X₁ X₂ hX₁ hX₂ height mesh hμ hμcap hw hwL hmesh hwm hheight hfreq
    hslots hhi₁ hhi₂ haff caps
  have cell:=actual_affine_error_cell_gates rayM H hH η₀ θ W hW hWs w σ freq hσ
    state p t X₁ X₂ hX₁ hX₂ hZ hslots haff
  have hr : (1:ℝ)*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑j,Real.logb Z (inp.P j))/(1:ℝ)))) =
      Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell (∑j,w j))) := by
    rw [div_one,cell.1,one_mul]
  -- Transport the complete amplifier before the dependent allocation and
  -- label binders. Only this small scalar equality needs unification.
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let paid ← Lean.Meta.getFVarFromUserName `paid
      let hr ← Lean.Meta.getFVarFromUserName `hr
      let tp ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← Lean.Meta.inferType paid))
      let isAmpMul := fun e : Lean.Expr => e.isAppOf ``HMul.hMul && e.getAppArgs.size == 6 &&
        e.getAppArgs[5]?.any (fun a=>a.isAppOf ``Cycle61.Arithmetic.amp)
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
    (Z Mrow amp ξ reserve b t : ℝ)(N Ncap : ℕ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))
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
    (hN : Fintype.card α≤ Ncap)(hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^(3:ℝ))
    {Label : Type*}[Fintype Label]
    (index : Label→ GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v)
    (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n)).block.value ballProfile≠0)
    (side : Bool)
    (hpuncture : ∀n : Label,
      let d:=geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
        hZ key first prime i Bp υ v hz₁ hz₂ (index n)
      d.R*(if side then d.D else d.C)≠0 ∧
        ((d.R*(if side then d.D else d.C)).absNorm:ℝ)≤ Z^(28:ℝ)) :
    let datum:=fun n : Label=>geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n)
    let alloc:=fun n : Label=>geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N
      hZ key first prime i Bp υ v hz₁ hz₂ (index n) (hne n) side
    let chains:=fun n : Label=>geometryErrorChain reflected s R seed Z Mrow ξ t hZ key first prime i Bp υ v hp hcop
      (if side then (datum n).D else (datum n).C) (datum n).R (alloc n)
    (∀n : Label,(chains n).R₂*(chains n).E₂≠0 ∧
      (((chains n).R₂*(chains n).E₂).absNorm:ℝ)≤ Z^(28:ℝ)) ∧
      (∀n : Label,∀D∈(datum n).block.divisors.filter Squarefree,
        (D.absNorm:ℝ)≤ Z^(3*((Ncap:ℝ)+2))) := by
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
/-- The whole original nonzero second-block filter is one menu. No menu
cardinality fee is introduced, and its first allocation weight stays undivided. -/
def actual_geometry_affine_error_raw_normalized_menu
    (s : Input α)(Z μ δ amp Cs Cg : ℝ)(N : ℕ)(Sp : Finset (ℕ×ℕ))(degree : ℕ)
    (η₀ : Character)(Q : Ideal O)(height mesh : ℝ)(hZ : 1< Z)
    (p : Profiles (1/4) (9/4))(caps : GeometryAffineExceptionalSourceGates s p N Cs Z)
    (hpaid : GeometryAffineErrorNormalizedMenuSuffix s Z μ δ amp Cg N Sp degree η₀ Q height mesh hZ)
    (hreserve : 0≤ frequencyLoss Z 32 (μ/64)+μ/8)
    (reflected : Bool)(t : ℝ)(key : ℤ×(Fin 5→ℤ))
    (first : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (prime : O)(i : Fin 3)(hp : prime≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first).slots j→ IsCoprime (Ideal.span {prime}) I)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t first)).pools
      ((Ideal.span {prime})^(errorIndex i+1)))(υ : Character)(v : ℝ)(ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val) ψ)
      fixedBadMask prime (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient first.2.val
      (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val) 1 s.ν s.W s.P≠0)
    (hprime : 3*amp/4≤ Real.logb Z (normValue prime))
    (hpuncture : ∀n : GeometryErrorSecondIndex reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
      (Fintype.card α) hZ key first prime i Bp υ v,∀side : Bool,
      let d:=geometryErrorSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
        (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂ n
      d.R*(if side then d.D else d.C)≠0 ∧
        ((d.R*(if side then d.D else d.C)).absNorm:ℝ)≤ Z^(28:ℝ))
    (P : Finset (Ideal O))(weight : ℝ)(hwgt : 0≤ weight)
    (windowProfile : 𝓢(ℝ,ℂ))(side : Bool)(tₑ u : ℝ)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀n : GeometryErrorSecondIndex reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
      (Fintype.card α) hZ key first prime i Bp υ v,
      actualSecondDyad (geometryErrorChild reflected s 1 1 Z 1 (μ/64) t hZ key first prime i Bp υ v)
        ((1*geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key first.1.val)*
            (Ideal.span {prime})^(errorIndex i+1)) first.1.val.2.1.val
        (geometryErrorSourceRadius reflected s 1 1 Z 1 amp (μ/64) (μ/8) hZ key first prime i)
        (geometryErrorFourierScale reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4)
          (Fintype.card α) hZ key first prime i) Z (μ/64) n∈box) :=
  let Label:=geometryErrorNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂
  let index:=fun n : Sigma (fun _ : Unit=>↥Label)=>n.2.val
  let hne : ∀n : Sigma (fun _ : Unit=>↥Label),
      (geometryErrorSecondDatum reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
        (Fintype.card α) hZ key first prime i Bp υ v caps.zero₁ caps.zero₂ (index n)).block.value ballProfile≠0:=
    fun n=>(Finset.mem_filter.mp n.2.property).2
  let hinj : Function.Injective index:=by
    intro a b hab
    cases a with | mk a an=>
      cases b with | mk b bn=>
        cases a;cases b
        exact congrArg (fun n : ↥Label=>@Sigma.mk Unit (fun _=>↥Label) () n) (Subtype.ext hab)
  let gates:=actual_geometry_error_normalized_label_gates reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) N hZ key first prime i Bp υ v hp hcop caps.zero₁ caps.zero₂ caps.card caps.poolCap
    index hne side (fun n=>hpuncture (index n) side)
  hpaid (μ/8) hreserve reflected 1 1 t key first prime i hp hcop Bp υ v caps.zero₁ caps.zero₂ ψ hυ hf₁ hprime
    (Menu:=Unit) (Blocks:=fun _=>↥Label) index hne hinj side
    (fun n=>(gates.1 n).1) (fun n=>(gates.1 n).2) p caps.profile₁ caps.profile₂ 1 (by norm_num)
    (by rw [caps.lower]) caps.support₁ caps.support₂ windowProfile (fun _=>(1:RayCharacter)) P weight hwgt
    gates.2 tₑ u box (fun n=>hbox (index n))

end RawAffineMenu

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_second_caps_of_scales
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_affine_error_puncture_of_scales
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_prime_norm_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_source_and_puncture

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_auxiliary_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_block_projector_cap

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_cell_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_prime_width

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_first_weight_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_normalized_coefficient_zero

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_zero_normalized_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finiteT_affine_error_normalized_menu

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_affine_error_normalized_scalar_schedule

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_normalized_menu_source_prefix

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_normalized_label_gates

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_error_normalized_menu_source_aligned

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_affine_error_raw_normalized_menu

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorNormalized -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCostReduction; sha256 265450bcb69532e1e3cf5bd82d455db93c2ee73e244ba0cee084d5d0c0ef8932 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The complete positive column cost of one physical datum. Both ray
indices and the entire retained frequency set remain inside this cost. -/
def mainNormalizedBlockCost {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (a ap : ℝ) (reflected : Bool) (d : SecondInputDatum α) (t u : ℝ) : ℝ :=
  (d.K/lowerFactor N a ap)*normalizer d.C d.D d.inactive*
    (∑χ : RayCharacter,∑ψ : RayCharacter,
      ∑D∈d.block.divisors.filter Squarefree,∑z∈secondLiveColumnRows d.block,
        if reflected then
          ‖normalizedColumn (withHeight d.input (d.τ ψ⁻¹)
            (d.input.t+2*Real.pi*(u-(-t)))) d.D d.hD d.R d.seed D (-z.val)‖^2
        else
          ‖normalizedColumn (withHeight d.input (d.τ χ)
            (d.input.t+2*Real.pi*(u-t))) d.C d.hC d.R d.seed D z.val‖^2)

theorem main_normalized_block_cost_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (reflected : Bool) (d : SecondInputDatum α) (t u : ℝ) :
    0≤ mainNormalizedBlockCost N a ap reflected d t u := by
  unfold mainNormalizedBlockCost
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg d.K_pos.le (lowerFactor_pos N a ap ha hap).le)
      (normalizer_pos d.C d.D d.hC d.inactive).le
  · apply Finset.sum_nonneg; intro χ _
    apply Finset.sum_nonneg; intro ψ _
    apply Finset.sum_nonneg; intro D _
    apply Finset.sum_nonneg; intro z _
    split_ifs <;> exact sq_nonneg _

/-- Pay the actual effective weight once, leaving a complete block cost
which can be selected before any row, projector or frequency choice. -/
theorem actual_main_normalized_block_cost {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ ap≤ x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,‖w l‖*mainNormalizedBlockCost N a ap reflected (d l) t u := by
  apply (actual_main_effective_normalized_columns N a ap ha hap d w W
    hcard hlower hW₁ hW₂ reflected t u).trans_eq
  simp only [mainNormalizedBlockCost,Finset.mul_sum,mul_assoc]

/-- A nonnegative physical coefficient majorant can replace the norm
of the original complex block weight without changing the column cost. -/
theorem actual_main_normalized_coefficient_cost {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (coefficient : Label→ℝ) (hw : ∀l,‖w l‖≤ coefficient l)
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ ap≤ x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,coefficient l*mainNormalizedBlockCost N a ap reflected (d l) t u := by
  apply (actual_main_normalized_block_cost N a ap ha hap d w W
    hcard hlower hW₁ hW₂ reflected t u).trans
  exact Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_right (hw l)
    (main_normalized_block_cost_nonneg N a ap ha hap reflected (d l) t u))

/-- Finite disintegration keeps an arbitrary original-block filter inside
each complete first-index cost. -/
theorem filtered_sigma_weighted_cost {I : Type*} [Fintype I]
    {J : I→ Type*} [∀i,Fintype (J i)] [DecidableEq (Sigma J)]
    (live : Finset (Sigma J)) (weight vol : I→ℝ) (cost : Sigma J→ℝ) :
    (∑q : live,weight q.val.1/vol q.val.1*cost q.val)=
      ∑i,weight i*((∑j : J i,if (⟨i,j⟩ : Sigma J)∈live then cost ⟨i,j⟩ else 0)/vol i) := by
  classical
  rw [Finset.sum_coe_sort live (fun q=>weight q.1/vol q.1*cost q)]
  calc
    _=(∑q : Sigma J,if q∈live then weight q.1/vol q.1*cost q else 0) := by
      rw [←Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    _=_ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring

/-- The fixed cardinality bound can replace the actual slot count in an
allocation weight. This leaves the underlying allocation and filter intact. -/
theorem geometry_allocation_weight_mono {α : Type*} [Fintype α] [DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤ N) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B ≤
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (le_max_left 1 b) hn) (Nat.cast_nonneg _)
  · exact le_rfl

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainCostSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)

/-- All original-nonzero second blocks belonging to one first allocation
are kept together. The original nonzero test precedes the ordinary filter. -/
def geometryMainFirstCost (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) : ℝ :=
  (∑n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key j,
    if (⟨j,n⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
        geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
    then mainNormalizedBlockCost N slotlo plainlo second
      (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        hz₁ hz₂ χ Q m ⟨j,n⟩) t₀ u
    else 0) /
    volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j)

theorem geometry_main_first_cost_nonneg (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo)
    (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    0≤ geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j := by
  apply div_nonneg _ (CenteredMomentAmplificationChildInput.volume_pos _).le
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact main_normalized_block_cost_nonneg N slotlo plainlo hslot hplain second _ t₀ u
  · exact le_refl _

/-- Exact first-allocation disintegration of the complete positive cost.
No count of first ideal labels, allocations or second labels is introduced. -/
theorem actual_main_first_cost_disintegration
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (second : Bool) (t₀ u : ℝ) :
    (∑j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂,
      geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.val.1 *
      mainNormalizedBlockCost N slotlo plainlo second
        (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m j.val) t₀ u) =
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  let live := geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
  let weights := fun j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
    geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.1.val j.2
  let vol := fun j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
    CenteredMomentAmplificationChildInput.volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j)
  let cost := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    mainNormalizedBlockCost N slotlo plainlo second
      (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        hz₁ hz₂ χ Q m j) t₀ u
  let First := GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
  let Second := fun j : First=>GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key j
  have hh : (∑q : live,weights q.val.1/vol q.val.1*cost q.val)=
      ∑j : First,weights j*((∑n : Second j,if (⟨j,n⟩ : Sigma Second)∈live then cost ⟨j,n⟩ else 0)/vol j) :=
    @filtered_sigma_weighted_cost First (inferInstance : Fintype First)
      Second (fun j=>inferInstance) (inferInstance : DecidableEq (Sigma Second)) live weights vol cost
  calc
    _ = ∑j : First,weights j*((∑n : Second j,if (⟨j,n⟩ : Sigma Second)∈live then cost ⟨j,n⟩ else 0)/vol j) := hh
    _ = _ := by
      rw [Fintype.sum_sigma]
      rfl

/-- The original-nonzero ordinary main family is reduced to one complete
cost per first allocation. The standard first-allocation mass selector can
now choose allocations and injective first labels using exactly this cost. -/
theorem actual_geometry_main_first_cost
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤ N) (hlower : slotlo≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ plainlo≤ x) (hW₂ : ∀x,s.W₂ x≠0→ plainlo≤ x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :
    let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
    let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
    secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  intro datum w
  have hh := actual_main_normalized_coefficient_cost N slotlo plainlo hslot hplain datum w W
    (fun j=>geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.val.1)
    (fun j=>actual_geometry_main_block_weight_norm reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key Mprice Aprice weight j.val)
    hcard (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) second t₀ u
  exact hh.trans_eq (actual_main_first_cost_disintegration reflected s R seed Z Mrow amp ξ
    reserve b t N hZ key hz₁ hz₂ χ Q m slotlo plainlo Mprice Aprice weight second t₀ u)

/-- Uniform-slot-count form for the fixed first-allocation selector. -/
theorem actual_geometry_main_first_cost_uniform
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤ N) (hlower : slotlo≤ s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→ plainlo≤ x) (hW₂ : ∀x,s.W₂ x≠0→ plainlo≤ x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :
    let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
    let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
    secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight N b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  intro datum w
  apply (actual_geometry_main_first_cost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ χ Q m Mprice Aprice slotlo plainlo hslot hplain weight hcard hlower hW₁ hW₂ W second t₀ u).trans
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_right
    (geometry_allocation_weight_mono reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) N hcard b j.val B)
    (geometry_main_first_cost_nonneg reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo hslot hplain second t₀ u ⟨j,B⟩)

end Literal

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_normalized_block_cost_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_normalized_block_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_normalized_coefficient_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_main_first_cost_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_first_cost_disintegration
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_first_cost

#print axioms OAI.SevenEighths.Cycle61InitialMass.filtered_sigma_weighted_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_allocation_weight_mono
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_first_cost_uniform

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCostReduction -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainSelectedCost; sha256 82146f28cef888abda5b4b0ca7f1023956f4614b79e0d8f68cd9f45d1658d9a0 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance mainSelectedSumDecidable {α : Type*} [DecidableEq α] :
    DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The literal original-nonzero main family is paid by complete selected
first-allocation costs. The remaining premise is precisely the selected
analytic family estimate; there is no independent label-count loss. -/
theorem actual_geometry_main_selected_cost {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (Cs b ε Amax Dmax B ξ slotlo plainlo : ℝ)
    (hCs : 1≤ Cs) (hε : 0<ε) (hA : 0≤ Amax) (hD : 0≤ Dmax)
    (hB : 0≤ B) (hξ : 0≤ξ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow amp reserve t Mprice Aprice : ℝ),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → (Z^Mrow)⁻¹≤ Z^Dmax →
      slotlo≤ s.lower → (∀x,s.W₁ x≠0→ plainlo≤ x) → (∀x,s.W₂ x≠0→ plainlo≤ x) →
      ∀(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed (Z^Mrow) Z ξ Mprice Aprice hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨column j,alloc j⟩)≤ E) →
      let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
      let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
      secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
        (K₀*Z^ε)*E := by
  obtain ⟨K₀,hK₀,hselection⟩ := actual_geometry_weighted_selected_cost (ι:=α)
    N Cs b ε Amax Dmax B ξ hCs hε hA hD hB hξ
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hselection] with Z hsel
  intro hZ reflected s R seed Mrow amp reserve t Mprice Aprice hn hM hseed hz₁ hz₂
    hsource hcap hV hKi hlo hW₁ hW₂ key weight χ Q m W second t₀ u E hK rows C mass hselected datum w
  apply (actual_geometry_main_first_cost_uniform reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ χ Q m Mprice Aprice slotlo plainlo hslot hplain weight hn hlo hW₁ hW₂ W second t₀ u).trans
  exact hsel.2 s hn hM reflected R seed (Z^Mrow) Mprice Aprice hK key weight hseed hz₁ hz₂
    hsource hcap hV hKi rows E
    (fun j alloc=>geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,alloc⟩)
    (fun j alloc=>geometry_main_first_cost_nonneg reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo hslot hplain second t₀ u ⟨j,alloc⟩)
    (by
      intro j
      cases reflected
      · exact (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key j.val.1).hC.1
      · exact (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key j.val.1).hD.1)
    hselected

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_selected_cost

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainSelectedCost -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainPhysicalSelection; sha256 6dd0a2d466b21be9f13b058062d14023d7dcc72668865c3754fdb4733b80e58a -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                            
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance mainPhysicalSelectionSumDecidable {α : Type*} [DecidableEq α] :
    DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Physical phase-weight specialization. Its selected mass is exactly the
mass used by the genuine low, high and coarse analytic family bounds. -/
theorem actual_geometry_main_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (Cs b ε Amax Dmax B ξ slotlo plainlo : ℝ)
    (hCs : 1≤ Cs) (hε : 0<ε) (hA : 0≤ Amax) (hD : 0≤ Dmax)
    (hB : 0≤ B) (hξ : 0≤ξ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow amp reserve t : ℝ),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → (Z^Mrow)⁻¹≤ Z^Dmax →
      slotlo≤ s.lower → (∀x,s.W₁ x≠0→ plainlo≤ x) → (∀x,s.W₂ x≠0→ plainlo≤ x) →
      ∀(key : ℤ×(Fin 5→ℤ))
        (Ψ : 𝓢(ℝ,ℂ))
        (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=>logAnnulus)
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
      let mass := fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hK key j.val
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨column j,alloc j⟩)≤ E) →
      let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
      let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mrow (Real.logb Z (volume s.toData))
          (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
      secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
        (K₀*Z^ε)*E := by
  obtain ⟨K₀,hK₀,hselection⟩ := actual_geometry_main_selected_cost (α:=α)
    N Cs b ε Amax Dmax B ξ slotlo plainlo hCs hε hA hD hB hξ hslot hplain
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hselection] with Z hsel
  intro hZ reflected s R seed Mrow amp reserve t hn hM hseed hz₁ hz₂
    hsource hcap hV hKi hlo hW₁ hW₂ key Ψ χ Q m W second t₀ u E hK rows C mass hselected datum w
  exact hsel hZ reflected s R seed Mrow amp reserve t Mrow (Real.logb Z (volume s.toData))
    hn hM hseed hz₁ hz₂ hsource hcap hV hKi hlo hW₁ hW₂ key
    (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) χ Q m W second t₀ u E hselected

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_physical_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainPhysicalSelection -/
