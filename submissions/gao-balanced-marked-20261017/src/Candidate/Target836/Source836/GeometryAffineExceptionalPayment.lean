import Candidate.Target836.Source836.GlobalNamed
import Candidate.Target836.Source836.GeometryAffineExceptionalGates
import Candidate.Target836.Source836.GeometryExceptionalNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalPhaseNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryUniformControls
import Candidate.Target836.Source836.GeometryAffineAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryBudgetContraction

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Cycle63Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSecondEnergySplit RayFourExpansion
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentSecondExceptionalFamily
open CenteredMomentCommonProfile ConcretePrimeRowBridge CenteredMomentActive
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildSourceCaps
open Filter CenteredMomentLogDyadic CenteredMomentFirstAnnularInput CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentAllocationCost
local notation "O" => HeckeFamily.O
open CenteredMomentPrimeElements CenteredMomentEnergyFirstAnnularAdmission
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance affineExceptionalPaymentSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The complete literal extracted exceptional source mass. The first detector
is independent of the second ball profile, and 56/P is included in each term. -/
def geometryAffineErrorExceptionalMass (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t v : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O)) (Qfix : Ideal O) (m : O)
    (υ : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let rows := firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hK key)
    (fun _=>logAnnulus)
  ∑j : rows,∑B : actualAllocations s.pools
      (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key j.val),
    ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s 1 1
        (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s 1 1 Ψ
          Z 1 amp ξ reserve (9/4) t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀

/-- The physical D shell remains outside the scalar saving. -/
def geometryAffineExceptionalShell (reflected : Bool) (Z : ℝ) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
  if reflected then 1/Hshell else 8192*Hshell

/-- The original-full-zero-filtered main exceptional remainder, with an
arbitrary first detector and block-dependent inducing ray. -/
def geometryAffineMainExceptionalNorm (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve firstHeight : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (Qfix : Ideal O) (m : O)
    (χ : geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key hz₁ hz₂→RayCharacter) : ℝ :=
  let phase:=fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
  ∑j : geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key hz₁ hz₂,
    ‖geometryMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key 1 (Real.logb Z (volume s)) phase j.val*
      (mainExceptionalDatum (geometryLowSecondDatum reflected s 1 1 Z 1 amp ξ reserve (9/4)
        firstHeight (Fintype.card ι) hZ key j.val.1 hz₁ hz₂ j.val.2) (χ j) Qfix m).block.value ballProfile‖

private theorem affine_exceptional_plain_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

open Cycle63InitialSource QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalPaymentFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

/-- Literal affine inputs, fixed parent character, true extracted dictionaries
and independent first/second heights. Every source estimate is constructed by
the saved kernel; no energy bound is a premise. -/
def GeometryAffineExceptionalErrorSpec
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (Qfix : Ideal O) (m : O)
    (C : ℝ) (Sp : Finset (ℕ×ℕ)) (degree : ℕ) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=η)
    (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
    length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+GlobalNamed.lambda*(∑i,w i)≤GlobalNamed.B →
    let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let beta:=GlobalNamed.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
    let amp:=GlobalNamed.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight secondHeight : ℝ),
    let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
    let firsts:=GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key
    ∀(υ : firsts→elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key q.1.val) ψ)
          fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      geometryAffineErrorExceptionalMass s Ψ Z amp (μ/64) (μ/8) firstHeight secondHeight
        hZ reflected key P Qfix m υ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖secondHeight‖)^degree*Z^(-(1/100:ℝ))

private theorem affine_exceptional_fold
    (Cd fee shell fixed A coef lower control height mass massCap bro Da power target : ℝ)
    (h : mass≤ massCap) (hCd : 0≤Cd) (hfee : 0≤fee) (hs : 0≤ shell)
    (hf : 0≤fixed) (hA : 0≤A) (hc : 0≤coef) (hl : 0≤lower)
    (hcontrol : 0≤control) (hh : 0≤height) (hm : 0≤ mass)
    (hb : 0≤bro) (_hd : 0≤Da) (hp : 0≤power) (hpow : power≤target) :
    Cd*(fee*shell*fixed*A*coef*lower*(control*height*mass^6)*bro*Da^2)*power≤
      (Cd*fee*fixed*A*coef*lower*massCap^6*bro*Da^2)*control*height*shell*target := by
  have hm6:=pow_le_pow_left₀ hm h 6
  have h₁:=mul_le_mul hm6 hpow hp (pow_nonneg (hm.trans h) 6)
  convert mul_le_mul_of_nonneg_left h₁
    (by positivity : 0≤Cd*fee*fixed*A*coef*lower*control*height*shell*bro*Da^2) using 1 <;> ring

set_option maxHeartbeats 600000 in
/-- Actual affine error exceptional payment with one profile union and one
height degree for every finite original slot subset. The whole budget uses
its actual slot cardinality; the ambient prefactor is paid separately. -/
theorem actual_affine_error_exceptional_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalErrorSpec (α:=α)
        rayM H hH Sbad W hW hWs η εaffine mesh Qfix m C Sp degree Z := by
  classical
  have hfixed:=fixedPresentationCost_pos
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((7/30000000)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have hξ : 0≤μ/64 := by positivity
  have hξ₁ : μ/64≤1 := by linarith
  have data (T : Finset α) : ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck Kfix Cd Da : ℝ),
      0<Kfix ∧ 0<Cd ∧ 0<Da ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryExceptionalErrorNormFullSpec (ι:=T) (1/4) (9/4) (fun _=>1) (fun _=>2)
          (μ/128) (μ/128) (μ/2048) η (9/4) (9/4) 1 (μ/128) (μ/128) (μ/64)
          J Sp Ck Qfix Kfix Cd Da Z := by
    obtain ⟨J,Sp,Ck,hfull⟩:=actual_geometry_error_exceptional_norm_full (ι:=T)
      (1/4) (9/4) (by norm_num) (by norm_num) (fun _=>1) (fun _=>2)
      (μ/128) (μ/128) (μ/2048) (by positivity) (by positivity) (by positivity)
      η (9/4) (9/4) (by norm_num) (by norm_num) 1 (μ/128) (μ/128) (μ/64)
      (by norm_num) (by positivity) (by positivity) hξ hξ₁
    obtain ⟨Kfix,Cd,Da,hK,hCd,hDa,hfull⟩:=hfull Qfix hQ hQt hQ72
    exact ⟨J,Sp,Ck,Kfix,Cd,Da,hK,hCd,hDa,hfull⟩
  choose J Sp Ck Kfix Cd Da hK hCd hDa kernels using data
  obtain ⟨Cs,hCs,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  let coef (T : Finset α):=max 1 (Ck T*CenteredMomentFirstChildProfileControl.exceptionalConstant
    (Fintype.card T) (9/4) (J T) Qfix (Kfix T))
  let Cbase (T : Finset α):=Cd T*(56*128*3*8*(Fintype.card RayCharacter:ℝ)^2)*
    (fixedPresentationCost*(η.modulus.absNorm:ℝ))*(max 1 (9/4:ℝ))^(Fintype.card T)*
    coef T*geometryExceptionalLowerConstant (Fintype.card T) 1 (1/4)*
    (Cs^(Fintype.card T))^6*((9/4:ℝ)^(Fintype.card T))^(1/3:ℝ)*(Da T)^2
  have hCbase (T : Finset α) : 0≤Cbase T := by
    have hcd:=(hCd T).le
    have hcoef : 0≤coef T := le_trans (by norm_num) (le_max_left _ _)
    dsimp only [Cbase,geometryExceptionalLowerConstant]
    positivity
  obtain ⟨C,hC,S,jdeg,kdeg,ldeg,huniform⟩:=geometry_uniform_profile_controls
    Cbase Sp (fun _=>0) (fun T=>2*J T) (fun _=>0) hCbase
  refine ⟨C,hC,S,kdeg,?_⟩
  filter_upwards [Filter.eventually_all.mpr kernels,hsources,
    eventual_actual_affine_exceptional_child_coprime rayM H hH Sbad hbad W hW hWs mesh hmesh,
    eventual_geometry_small_frequency μ hμ] with Z hk hs hc hfreq
  refine ⟨hs.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone s beta amp P μ' Ψ reflected key firstHeight secondHeight hK' firsts υ hυ
  have hηs : s.η=η := hη
  have caps:=hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hcell:=Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  have hbeta:=GlobalNamed.cellUpper_bounds hcell.1 hcell.2.1
  have hamp : 0≤amp := (GlobalNamed.amp_pos hbeta).le
  have hamp₁ : amp≤1 := (GlobalNamed.amp_bounds hbeta).2.trans (by norm_num)
  have hω : frequencyLoss Z 32 (μ/64)+μ/8≤3 := hfreq.2.2.trans (by linarith)
  have hcop : ∀q : firsts,∀p∈elementPool P,∀j I,
      I∈(geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK' key firstHeight q).slots j→
        IsCoprime (Ideal.span {p}) I := by
    intro q prime hp j I hI
    exact hc.2 η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hwm
      beta hbeta.1 hbeta.2 ⟨prime,hp⟩
      (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK' key q.1.val) 1 q.2
      (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK' key q.1.val) firstHeight j I hI
  have hraw:=(hk T).2 hZ s caps.lo caps.hi hηs caps.endpoints
    (by rw [caps.lower]) caps.scales p caps.profile₁ caps.profile₂
    1 1 one_ne_zero squarefree_one one_ne_zero caps.zero₁ caps.zero₂ caps.volume
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap (by simpa using hZ.le)
    amp (μ/8) firstHeight secondHeight (Real.logb Z (s.η.modulus.absNorm:ℝ)/4)
    hamp hamp₁ (by positivity) hω caps.plain₁ caps.plain₂ caps.plain₃ caps.plain₄
    (1/4) (1/4) (by norm_num) (by norm_num) caps.support₁ caps.support₂
    reflected Ψ key rayM inferInstance H Sbad hbad υ hcop hυ m hm hml hm2
  have hlog:=actual_affine_exceptional_volume_cell rayM H hH η₀ θ W hW hWs
    w σ freq hσ state p t X₁ X₂ hX₁ hX₂ hZ hlo₁ hlo₂ ⟨hwlo,hwhi⟩ hcone
  have hell : 0≤Real.logb Z (s.η.modulus.absNorm:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast norm_at_least_one s.η.modulus s.η.modulus_ne_bot)
  have hloss:=(affine_exceptional_small_loss εaffine
    (frequencyLoss Z 32 (μ/64)+μ/8) 0 0 hε hfreq.2.2 (by positivity) (by positivity)).2.2
  have hexp:=(affine_exceptional_exponent_saving beta (Real.logb Z (volume s))
    (Real.logb Z (s.η.modulus.absNorm:ℝ))
    (2*(μ/128)+2*(μ/128)+252*(μ/2048)+5*(frequencyLoss Z 32 (μ/64)+μ/8)/6+
      3*(μ/128)+3*(μ/128)) hbeta hlog hell (by linarith)).2
  have hpower:=Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  rw [hηs] at hpower
  have hprod : (∏i,s.M i)≤Cs^(Fintype.card T) := by
    calc
      _≤∏_i : T,Cs := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.M_ge_one i))
        (fun i _=>caps.controls i)
      _=_ := by simp only [Finset.prod_const,Finset.card_univ]
  have hmass : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell];split_ifs <;> positivity
  have hcontrol := huniform T p 1 (1+‖secondHeight‖) 1 (by norm_num) (by linarith [norm_nonneg secondHeight]) (by norm_num)
  simp only [one_pow,mul_one] at hcontrol
  have hbound := affine_exceptional_fold (Cd T) (56*128*3*8*(Fintype.card RayCharacter:ℝ)^2)
    (geometryAffineExceptionalShell reflected Z key) (fixedPresentationCost*(η.modulus.absNorm:ℝ))
    ((max 1 (9/4:ℝ))^(Fintype.card T)) (coef T)
    (geometryExceptionalLowerConstant (Fintype.card T) 1 (1/4)) (p.control (Sp T)^2)
    ((1+‖secondHeight‖)^(2*J T)) (∏i,s.M i) (Cs^(Fintype.card T))
    (((9/4:ℝ)^(Fintype.card T))^(1/3:ℝ)) (Da T) _ _ hprod (hCd T).le
    (by positivity) hshell (by positivity) (by positivity) (by dsimp [coef];positivity)
    (by unfold geometryExceptionalLowerConstant;positivity) (sq_nonneg _) (by positivity)
    hmass (by positivity) (hDa T).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hpower
  have hpaid : geometryAffineErrorExceptionalMass s Ψ Z amp (μ/64) (μ/8) firstHeight secondHeight
      hZ reflected key P Qfix m υ≤
      Cbase T*(p.control (Sp T))^2*(1+‖secondHeight‖)^(2*J T)*
        geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)) := by
    have hplo : (∏i,s.lo i)=1 := by
      change (∏_i : T,(1:ℝ))=1
      simp only [Finset.prod_const,one_pow]
    have hseed : ((1:Ideal O).absNorm:ℝ)=1 := by norm_num
    have hveq : geometryExceptionalVolume s=volume s := rfl
    have hsheq : (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
      else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))=
        geometryAffineExceptionalShell reflected Z key := by
      rw [hplo]
      unfold geometryAffineExceptionalShell
      split_ifs <;> ring
    dsimp only at hraw
    conv_rhs at hraw => rw [hηs,hveq,hsheq,hseed,div_one]
    apply hraw.trans
    convert hbound using 1 <;> congr 1 <;> congr 1 <;> dsimp only [amp] <;> ring
  convert hpaid.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcontrol hshell) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) using 1 <;> ring

/-- Actual filtered main remainder, after its one prime-average cancellation. -/
def GeometryAffineExceptionalMainSpec
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (Qfix : Ideal O) (m : O)
    (C : ℝ) (Sp : Finset (ℕ×ℕ)) (degree : ℕ) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=η)
    (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (41/100:ℝ)≤length Z X₁ → (41/100:ℝ)≤length Z X₂ →
    length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+GlobalNamed.lambda*(∑i,w i)≤GlobalNamed.B →
    let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    let beta:=GlobalNamed.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
    let amp:=GlobalNamed.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
    ∀χ : geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
      (Fintype.card T) hZ key (affine_exceptional_plain_zero p 0) (affine_exceptional_plain_zero p 1)→RayCharacter,
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      geometryAffineMainExceptionalNorm s Ψ Z amp (μ/64) (μ/8) firstHeight hZ reflected key
        (affine_exceptional_plain_zero p 0) (affine_exceptional_plain_zero p 1) Qfix m χ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖firstHeight‖)^degree*Z^(-(1/100:ℝ))

private theorem affine_exceptional_split_power (Z a b : ℝ) (hZ : 0<Z) :
    Z^a*Z^b=Z^(a+b) := (Real.rpow_add hZ a b).symm

private theorem affine_exceptional_post_coefficient (Z a b ray cap Cd factor : ℝ)
    (hZ : 0<Z) :
    ray*(16800*(cap+1)*(Cd*factor*Z^a)*Z^b)=
      Cd*((ray*16800*(cap+1))*factor)*Z^(a+b) := by
  rw [Real.rpow_add hZ]
  ring

private theorem affine_exceptional_main_exponent (ε δ θ amp V ell ω plain ea ec loss : ℝ) :
    (2*ε+2*δ+2*41*θ+(3*amp)/3+V-(1+ell)+4*(3*amp)/3+5*ω/6+2*plain/3+3*ea+
      3*ec-(3*amp)/3)+loss=
    2*ε+2*δ+82*θ+V-(1+ell)+4*amp+5*ω/6+2*plain/3+3*ea+3*ec+loss := by ring

private theorem affine_exceptional_post_normalization
    (Z ε δ θ amp Vold Vnew ell ω plain ea ec loss ray cap Cd shellOld shellNew
      fixed normOld normNew A coef lower control bro Da seedNorm : ℝ)
    (hZ : 0<Z)(hV : Vold=Vnew)(hshell : shellOld=shellNew)
    (hnorm : normOld=normNew)(hseed : seedNorm=1) :
    ray*(16800*(cap+1)*(Cd*(shellOld*(fixed*normOld)*A*coef*lower*control*bro*Da^2)*
      Z^(2*ε+2*δ+2*41*θ+(3*amp)/3+Vold-(1+ell)+4*(3*amp)/3+5*ω/6+2*plain/3+3*ea+
        3*ec-(3*amp)/3)/seedNorm)*Z^loss)=
    Cd*((ray*16800*(cap+1))*shellNew*(fixed*normNew)*A*coef*lower*control*bro*Da^2)*
      Z^(2*ε+2*δ+82*θ+Vnew-(1+ell)+4*amp+5*ω/6+2*plain/3+3*ea+3*ec+loss) := by
  rw [hV,hshell,hnorm,hseed,div_one,
    affine_exceptional_post_coefficient Z _ _ _ _ _ _ hZ,
    affine_exceptional_main_exponent]
  ring

/-- An explicit source kernel boundary: the output constants occur in the
predicate itself, so choosing a finite family never unfolds a proof-valued tuple. -/
private def AffineMainExceptionalKernelSpec
    (μ : ℝ) (η : Character) (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ)
    (Qfix : Ideal O) (Kfix Cd Da Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input ι)(hlo : s.lo=fun _=>1)(hhi : s.hi=fun _=>2)
    (hη : s.η=η)(hend : Endpoints (9/4) (9/4) (9/4) s)(hlower : 1≤ s.lower)
    (hsP : ∀i,1≤ s.P i)(p : Profiles (1/4) (9/4))
    (hW₁ : s.W₁=p.profile 0)(hW₂ : s.W₂=p.profile 1)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hV : volume s≤Z^(2:ℝ))(hsourcepos : 0< sourceRadius s)
    (hsource : sourceRadius s≤Z^(3:ℝ))
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
    (amp reserve t : ℝ)(hamp : 0≤amp)(hreserve : 0≤reserve),
    let ell:=Real.logb Z (s.η.modulus.absNorm:ℝ)
    ∀(hX₁ : Z^((1+ell)/4-ell/4)≤ s.X₁)(hX₂ : Z^((1+ell)/4-ell/4)≤ s.X₂)
      (hY₁ : Z^((1+ell)/4-ell/4)≤ s.Y₁)(hY₂ : Z^((1+ell)/4-ell/4)≤ s.Y₂)
      (hs₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤x)(hs₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤x)
      (reflected : Bool)(Ψ : 𝓢(ℝ,ℂ))(key : ℤ×(Fin 5→ℤ))
      (m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)
      (χ : geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) reserve (9/4) t
        (Fintype.card ι) hZ key hz₁ hz₂→RayCharacter)
      (P : Finset (Ideal O))(beta cap : ℝ)(hbeta : 3401/100000≤beta ∧ beta≤1/25)
      (hcap : 0≤cap)(hampEq : amp=GlobalNamed.amp beta)
      (hprime : Z^(GlobalNamed.amp beta-μ/128)≤(P.card:ℝ)),
    let fee:=(Fintype.card RayCharacter:ℝ)*16800*(cap+1)
    let coef:=max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
      (Fintype.card ι) (9/4) J Qfix Kfix)
    (56/(P.card:ℝ))*((cap+6*GlobalNamed.amp beta)/(GlobalNamed.amp beta/2))*
      geometryAffineMainExceptionalNorm s Ψ Z amp (μ/64) reserve t hZ reflected key hz₁ hz₂ Qfix m χ≤
    Cd*(fee*geometryAffineExceptionalShell reflected Z key*
      (fixedPresentationCost*(η.modulus.absNorm:ℝ))*(max 1 (9/4:ℝ))^(Fintype.card ι)*
      coef*geometryExceptionalLowerConstant (Fintype.card ι) 1 (1/4)*
      (p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6)*
      ((9/4:ℝ)^(Fintype.card ι))^(1/3:ℝ)*Da^2)*
      Z^(2*(μ/128)+2*(μ/128)+82*(μ/2048)+Real.logb Z (volume s)-(1+ell)+4*amp+
        5*(frequencyLoss Z 32 (μ/64)+reserve)/6+2*(ell/4)/3+3*(μ/128)+3*(μ/128)+μ/128)

set_option maxHeartbeats 500000 in
private theorem affine_main_exceptional_kernel
    (μ : ℝ)(hμ : 0<μ)(hξ₁ : μ/64≤1)(η : Character)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)}) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck Kfix Cd Da : ℝ),
      0<Cd ∧ 0<Da ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
        AffineMainExceptionalKernelSpec (ι:=ι) μ η J Sp Ck Qfix Kfix Cd Da Z := by
  let full:=actual_geometry_main_exceptional_norm_payment (ι:=ι)
    (1/4) (9/4) (by norm_num) (by norm_num) (fun _=>1) (fun _=>2)
    (μ/128) (μ/128) (μ/2048) (by positivity) (by positivity) (by positivity)
    η (9/4) (9/4) (by norm_num) (by norm_num) 1 (μ/128) (μ/128) (μ/64)
    (by norm_num) (by positivity) (by positivity) (by positivity) hξ₁
  let saved:=full.2.2.2 Qfix hQ hQt hQ72
  refine ⟨full.1,full.2.1,full.2.2.1,saved.1,saved.2.1,saved.2.2.1,
    saved.2.2.2.down.2.1,saved.2.2.2.down.2.2.1,?_⟩
  filter_upwards [saved.2.2.2.down.2.2.2] with Z hk
  refine ⟨hk.1,?_⟩
  intro hZ s hlo hhi hη hend hlower hsP p hW₁ hW₂ hz₁ hz₂ hV hspos hsource hpool
    amp reserve t hamp hreserve ell hX₁ hX₂ hY₁ hY₂ hs₁ hs₂ reflected Ψ key m hm hml hm2 χ
    P beta cap hbeta hcap hampEq hprime fee coef
  have hraw:=hk.2 hZ s hlo hhi hη hend hlower hsP p hW₁ hW₂
    1 1 one_ne_zero squarefree_one one_ne_zero hz₁ hz₂ hV hspos hsource hpool
    (by simpa using hZ.le) 1 amp reserve t (ell/4) (by norm_num)
    (by simpa only [Real.rpow_one] using (le_rfl : Z≤Z)) hamp hreserve hX₁ hX₂ hY₁ hY₂
    (1/4) (1/4) (by norm_num) (by norm_num) hs₁ hs₂ reflected Ψ key m hm hml hm2 χ
  have hpost:=hraw.2 P beta (μ/128) cap hbeta hcap
    (by rw [←hampEq];ring) hprime
  have hplo : (∏i,s.lo i)=1 := by rw [hlo];simp only [Finset.prod_const,one_pow]
  have hseed : ((1:Ideal O).absNorm:ℝ)=1 := by norm_num
  have hveq : geometryExceptionalVolume s=volume s := rfl
  have hsheq : (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
    else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))=
      geometryAffineExceptionalShell reflected Z key := by
    rw [hplo];unfold geometryAffineExceptionalShell;split_ifs <;> ring
  dsimp (config := { zetaDelta := false }) only at hpost
  have hn : (s.η.modulus.absNorm:ℝ)=(η.modulus.absNorm:ℝ) :=
    congrArg (fun η : Character=>(η.modulus.absNorm:ℝ)) hη
  have hscalar:=affine_exceptional_post_normalization Z (μ/128) (μ/128) (μ/2048)
    amp (Real.logb Z (geometryExceptionalVolume s)) (Real.logb Z (volume s)) ell
    (frequencyLoss Z 32 (μ/64)+reserve) (ell/4) (μ/128) (μ/128) (μ/128)
    (Fintype.card RayCharacter:ℝ) cap saved.2.1
    (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
      else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))
    (geometryAffineExceptionalShell reflected Z key) fixedPresentationCost
    (s.η.modulus.absNorm:ℝ) (η.modulus.absNorm:ℝ)
    ((max 1 (9/4:ℝ))^(Fintype.card ι)) coef
    (geometryExceptionalLowerConstant (Fintype.card ι) 1 (1/4))
    (p.control full.2.1^2*(1+‖t‖)^(2*full.1)*(∏i,s.M i)^6)
    (((9/4:ℝ)^(Fintype.card ι))^(1/3:ℝ)) saved.2.2.1 ((1:Ideal O).absNorm:ℝ)
    (zero_lt_one.trans hZ) (congrArg (Real.logb Z) hveq) hsheq hn hseed
  exact hpost.trans_eq hscalar

private theorem affine_exceptional_coefficient_nonneg
    (a b c d e f g h k : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hd : 0≤d) (he : 0≤e) (hf : 0≤f) (hg : 0≤g) (hh : 0≤h) (hk : 0≤k) :
    0≤a*b*c*d*e*f*g*h*k := by positivity

set_option maxHeartbeats 600000 in
/-- One actual filtered main exceptional bound covers all finite slot subsets,
all original detectors and all inducing rays, preserving the physical H or1/H. -/
theorem actual_affine_main_exceptional_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalMainSpec (α:=α)
        rayM H hH Sbad W hW hWs η εaffine mesh Qfix m C Sp degree Z := by
  classical
  have hfixed:=fixedPresentationCost_pos
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((7/30000000)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have hξ : 0≤μ/64 := by positivity
  have hξ₁ : μ/64≤1 := by linarith
  have data (T : Finset α):=affine_main_exceptional_kernel (ι:=T) μ hμ hξ₁ η Qfix hQ hQt hQ72
  choose J Sp Ck Kfix Cd Da hCd hDa kernels using data
  obtain ⟨Cs,hCs,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  let coef (T : Finset α):=max 1 (Ck T*CenteredMomentFirstChildProfileControl.exceptionalConstant
    (Fintype.card T) (9/4) (J T) Qfix (Kfix T))
  let fee:=(Fintype.card RayCharacter:ℝ)*16800*(amplifierCap 2 0 1+1)
  let Cbase (T : Finset α):=Cd T*fee*
    (fixedPresentationCost*(η.modulus.absNorm:ℝ))*(max 1 (9/4:ℝ))^(Fintype.card T)*
    coef T*geometryExceptionalLowerConstant (Fintype.card T) 1 (1/4)*
    (Cs^(Fintype.card T))^6*((9/4:ℝ)^(Fintype.card T))^(1/3:ℝ)*(Da T)^2
  have hfee : 0≤fee := by dsimp only [fee,amplifierCap];positivity
  have hCbase (T : Finset α) : 0≤Cbase T := by
    have hcoef : 0≤coef T := le_trans (by norm_num) (le_max_left _ _)
    exact affine_exceptional_coefficient_nonneg (Cd T) fee
      (fixedPresentationCost*(η.modulus.absNorm:ℝ))
      ((max 1 (9/4:ℝ))^(Fintype.card T)) (coef T)
      (geometryExceptionalLowerConstant (Fintype.card T) 1 (1/4))
      ((Cs^(Fintype.card T))^6) (((9/4:ℝ)^(Fintype.card T))^(1/3:ℝ)) ((Da T)^2)
      (hCd T).le hfee (by positivity) (by positivity) hcoef
      (by unfold geometryExceptionalLowerConstant;positivity) (by positivity)
      (by positivity) (sq_nonneg _)
  obtain ⟨C,hC,S,jdeg,kdeg,ldeg,huniform⟩:=geometry_uniform_profile_controls
    Cbase Sp (fun _=>0) (fun T=>2*J T) (fun _=>0) hCbase
  refine ⟨C,hC,S,kdeg,?_⟩
  filter_upwards [Filter.eventually_all.mpr kernels,hsources,
    actual_affine_geometry_amplification (α:=α) rayM H hH Sbad hbad W hW hWs
      (μ/128) mesh (μ/64) (μ/8) (by positivity) hmesh hξ hξ₁ (by positivity),
    eventual_geometry_small_frequency μ hμ] with Z hk hs ha hfreq
  refine ⟨hs.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone s beta amp P μ' Ψ reflected key firstHeight χ
  have hηs : s.η=η := hη
  have caps:=hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hlo₁ hlo₂ hhi₁ hhi₂ hwhi
  have hcell:=Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  have hbeta:=GlobalNamed.cellUpper_bounds hcell.1 hcell.2.1
  have hamp : 0≤amp := (GlobalNamed.amp_pos hbeta).le
  have hprime:= (ha.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi).2.1
  have hpost:=(hk T).2 hZ s caps.lo caps.hi hηs caps.endpoints
    (by rw [caps.lower]) caps.scales p caps.profile₁ caps.profile₂ caps.zero₁ caps.zero₂
    caps.volume caps.sourcePositive caps.sourceCap caps.poolCap
    amp (μ/8) firstHeight hamp (by positivity)
    caps.plain₁ caps.plain₂ caps.plain₃ caps.plain₄ caps.support₁ caps.support₂
    reflected Ψ key m hm hml hm2 χ P beta (amplifierCap 2 0 1) hbeta
    (by norm_num [amplifierCap]) rfl hprime
  have hlog:=actual_affine_exceptional_volume_cell rayM H hH η₀ θ W hW hWs
    w σ freq hσ state p t X₁ X₂ hX₁ hX₂ hZ hlo₁ hlo₂ ⟨hwlo,hwhi⟩ hcone
  have hell : 0≤Real.logb Z (s.η.modulus.absNorm:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast norm_at_least_one s.η.modulus s.η.modulus_ne_bot)
  have hloss:=(affine_exceptional_small_loss εaffine
    (frequencyLoss Z 32 (μ/64)+μ/8) 0 (μ/128) hε hfreq.2.2 (by positivity) (by linarith)).2.2
  have hexp:=(affine_exceptional_exponent_saving beta (Real.logb Z (volume s))
    (Real.logb Z (s.η.modulus.absNorm:ℝ))
    (2*(μ/128)+2*(μ/128)+82*(μ/2048)+5*(frequencyLoss Z 32 (μ/64)+μ/8)/6+
      3*(μ/128)+3*(μ/128)+μ/128) hbeta hlog hell (by linarith)).1
  have hexp' : 2*(μ/128)+2*(μ/128)+82*(μ/2048)+Real.logb Z (volume s)-
      (1+Real.logb Z (s.η.modulus.absNorm:ℝ))+4*amp+
      5*(frequencyLoss Z 32 (μ/64)+μ/8)/6+2*(Real.logb Z (s.η.modulus.absNorm:ℝ)/4)/3+
      3*(μ/128)+3*(μ/128)+μ/128≤-(1/100:ℝ) := by
    convert hexp using 1 <;> dsimp only [amp] <;> ring
  have hpower:=Real.rpow_le_rpow_of_exponent_le hZ.le hexp'
  rw [hηs] at hpower
  dsimp only at hpost
  conv_rhs at hpost => rw [hηs]
  have hprod : (∏i,s.M i)≤Cs^(Fintype.card T) := by
    calc
      _≤∏_i : T,Cs := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.M_ge_one i))
        (fun i _=>caps.controls i)
      _=_ := by simp only [Finset.prod_const,Finset.card_univ]
  have hmass : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell];split_ifs <;> positivity
  have hcontrol := huniform T p 1 (1+‖firstHeight‖) 1 (by norm_num)
    (by linarith [norm_nonneg firstHeight]) (by norm_num)
  simp only [one_pow,mul_one] at hcontrol
  have hbound := affine_exceptional_fold (Cd T) fee
    (geometryAffineExceptionalShell reflected Z key) (fixedPresentationCost*(η.modulus.absNorm:ℝ))
    ((max 1 (9/4:ℝ))^(Fintype.card T)) (coef T)
    (geometryExceptionalLowerConstant (Fintype.card T) 1 (1/4)) (p.control (Sp T)^2)
    ((1+‖firstHeight‖)^(2*J T)) (∏i,s.M i) (Cs^(Fintype.card T))
    (((9/4:ℝ)^(Fintype.card T))^(1/3:ℝ)) (Da T) _ _ hprod (hCd T).le
    hfee hshell (by positivity) (by positivity) (by dsimp [coef];positivity)
    (by unfold geometryExceptionalLowerConstant;positivity) (sq_nonneg _) (by positivity)
    hmass (by positivity) (hDa T).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hpower
  have hpaid : (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      geometryAffineMainExceptionalNorm s Ψ Z amp (μ/64) (μ/8) firstHeight hZ reflected key
        (affine_exceptional_plain_zero p 0) (affine_exceptional_plain_zero p 1) Qfix m χ≤
      Cbase T*(p.control (Sp T))^2*(1+‖firstHeight‖)^(2*J T)*
        geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)) := by
    apply hpost.trans
    exact hbound
  convert hpaid.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcontrol hshell) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) using 1 <;> ring

/-- Either reflection sign preserves independent original and Mellin height
weights. Its fixed scale factor can be absorbed into the saved constant. -/
theorem geometry_affine_exceptional_mellin_weight (degree : ℕ)
    (base height t u : ℝ)(reflected : Bool)(hh : 0≤height) :
    (1+‖base+2*Real.pi*(u-(if reflected then -t else t))‖)^degree≤
      (1+|2*Real.pi|)^degree*(1+|base|+height)^degree*
        (1+‖t‖)^degree*(1+‖u‖)^degree := by
  have h:=geometry_mellin_height base height (if reflected then -t else t) u (2*Real.pi) hh
  have hn : ‖(if reflected then -t else t)‖=‖t‖ := by split_ifs <;> simp only [norm_neg]
  rw [hn] at h
  have hbase : 1+‖base+2*Real.pi*(u-(if reflected then -t else t))‖≤
      1+|base+2*Real.pi*(u-(if reflected then -t else t))|+height := by
    rw [Real.norm_eq_abs];linarith
  have hp:=pow_le_pow_left₀ (by positivity)
    (hbase.trans h) degree
  simpa only [mul_pow,mul_assoc,mul_comm,mul_left_comm] using hp

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_affine_error_exceptional_payment
#print axioms OAI.SevenEighths.Target836SourceAssembly.actual_affine_main_exceptional_payment

#print axioms OAI.SevenEighths.Target836SourceAssembly.geometry_affine_exceptional_mellin_weight
