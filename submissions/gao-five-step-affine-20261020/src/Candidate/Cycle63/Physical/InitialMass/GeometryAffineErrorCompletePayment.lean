/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorPayment
import Candidate.Cycle63.Arithmetic.Constants
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentAmplificationErrorEnergy CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeElements CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentLogDyadic RayFourExpansion
open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentFiniteProfileExceptional CenteredMomentSlotRatios
attribute [local instance] geometryErrorOrdinaryContractionDecidable

variable {α : Type}[Fintype α]

/-- Increasing the positive numerator preserves the exact ratio-fiber bound. -/
theorem affine_error_second_normalized_envelope_mono
    {Label : Type*}[Fintype Label][DecidableEq α]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E E' Hratio : ℤ→ℝ)
    (hH : ∀r∈secondRatioBins (fun l=>(d l).block),0<Hratio r)
    (hE : ∀r∈secondRatioBins (fun l=>(d l).block),E r≤E' r)
    (h : SecondNormalizedBound W degree windowDegree d w E Hratio) :
    SecondNormalizedBound W degree windowDegree d w E' Hratio := by
  intro r hr reflected t u
  have he : (if reflected then E r/Hratio r else E r*Hratio r)≤
      (if reflected then E' r/Hratio r else E' r*Hratio r) := by
    cases reflected
    · exact mul_le_mul_of_nonneg_right (hE r hr) (hH r hr).le
    · exact div_le_div_of_nonneg_right (hE r hr) (hH r hr).le
  exact (h r hr reflected t u).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity))

/-- The original selected datum and coefficient are preserved by an envelope increase. -/
theorem geometry_affine_error_normalized_receipt_mono
    (degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator numerator' : ℝ)
    (hle : numerator≤numerator')
    (h : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ
      Z Mrow amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator) :
    GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ
      Z Mrow amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator' := by
  obtain ⟨χ,Hratio,hH,hn⟩:=h
  refine ⟨χ,Hratio,hH,?_⟩
  exact affine_error_second_normalized_envelope_mono _ degree windowDegree _ _ _ _ _
    hH (fun _ _=>hle) hn

/-- A larger profile union and height degree enlarge the control of a normalized
callback. -/
theorem geometry_affine_error_control_mono (p : Profiles (1/4) (9/4))
    (SN S : Finset (ℕ×ℕ))(dN D : ℕ)(hSN : SN⊆S)(hdN : dN≤D)(n : ℕ)
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ)(hheight : 0≤height) :
    (p.control SN)^2*geometryHighFactor reflected
        (geometrySupportConstant n 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dN≤
      (p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant n 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D := by
  have hside : 0≤geometryHighFactor reflected (geometrySupportConstant n 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hprofile := pow_le_pow_left₀ (p.control_nonneg SN) (Cycle63Physical.profile_control_mono p hSN) 2
  have hbase : (1+|firstHeight|+height)^dN≤(1+|firstHeight|+height)^D :=
    pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdN
  exact mul_le_mul (mul_le_mul_of_nonneg_right hprofile hside) hbase
    (pow_nonneg (by positivity) _) (by positivity)

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorCompleteFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

set_option linter.unusedVariables false in
variable [Cycle63.AffineLedger] in
/-- Explicit conditional callback at a parent: the uniform exact normalized-family
estimate. Constants and profiles precede every parent input with source gates of profile
cap `Cs`, first puncture of norm at most `Z^Rcap`, seed, radial scale `Mrow` and original
character family. -/
def GeometryAffineErrorNormalizedParentSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(Ψ : 𝓢(ℝ,ℂ))(η₀ : Character)(mesh εaffine Rcap Cs : ℝ)
    (T : Finset α)(degree windowDegree : ℕ)(Qfix : Ideal O)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cn Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input T)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
    (hb₁ : s.b₁=9/4)(hb₂ : s.b₂=9/4)
    (hplain : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^(1:ℝ))
    (hwindows : ∀j,logWindow (s.lo j) (s.hi j)≤Real.log 2)
    (θ : T→RayQuotient.Characters rayM H)(w σ freq : T→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRcap : (R.absNorm:ℝ)≤Z^Rcap)(hMrow : 0≤ Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16)
    (hw : ∀j,0≤w j)(hwm : ∀j,w j≤ mesh)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (beta : ℝ)(hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ)
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height),
    let μ:=geometryLossUnit 1 εaffine
    let N:=Fintype.card α
    let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))+(1-Mrow)
    ∀(υ : GeometryLowFirstIndex (α:=T) reflected s R seed
      (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character),
    (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
      (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val) ψ)
      fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
    letI : DecidableEq T:=Classical.decEq T;
    GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s R seed Ψ Z Mrow amp (μ/64) (μ/8)
      firstHeight hZ key P υ caps.zero₁ caps.zero₂ Qfix fixedBadMask (Cn*control*Z^exponent/(seed.absNorm:ℝ))

set_option linter.unusedVariables false in
variable [Cycle63.AffineLedger] in
/-- The original retained error of a parent, paid by its prime average exactly once. -/
def GeometryAffineErrorPaidParentSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(Ψ : 𝓢(ℝ,ℂ))(η₀ : Character)(mesh εaffine Rcap Cs : ℝ)
    (T : Finset α)(S : Finset (ℕ×ℕ))(D : ℕ)(Ce Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input T)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
    (hb₁ : s.b₁=9/4)(hb₂ : s.b₂=9/4)
    (hplain : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^(1:ℝ))
    (hwindows : ∀j,logWindow (s.lo j) (s.hi j)≤Real.log 2)
    (θ : T→RayQuotient.Characters rayM H)(w σ freq : T→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRcap : (R.absNorm:ℝ)≤Z^Rcap)(hMrow : 0≤ Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16)
    (hw : ∀j,0≤w j)(hwm : ∀j,w j≤ mesh)(hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (beta : ℝ)(hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))
    (reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ)
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height),
    let μ:=geometryLossUnit 1 εaffine
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    ∀(υ : GeometryLowFirstIndex (α:=T) reflected s R seed
      (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character),
    (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
      (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val) ψ)
      fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
    letI : DecidableEq T:=Classical.decEq T;
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s R seed Ψ Z Mrow amp (μ/64) (μ/8) firstHeight
      hZ reflected key P υ‖≤
      Ce*control*Z^(-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow))/(seed.absNorm:ℝ)

set_option maxHeartbeats 400000 in
variable [Cycle63.AffineLedger] in
/-- Conditional adapter at a parent from the exact uniform normalized-family callback
to paid original retained error. The callback is the remaining analytic obligation. -/
theorem actual_affine_error_complete_parent_payment
    (T : Finset α)(A degree windowDegree dN : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)(W : ℝ→ℂ)
    (Ψ : 𝓢(ℝ,ℂ))(η₀ : Character)(εaffine mesh Rcap Cs : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)(hRcap20 : Rcap≤20)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (SN : Finset (ℕ×ℕ))(Cn : ℝ)(hCn : 0≤Cn)
    (hnormalized : ∀ᶠZ : ℝ in atTop,
      GeometryAffineErrorNormalizedParentSpec rayM H hH Sbad W Ψ η₀ mesh εaffine Rcap Cs T
        degree windowDegree Qfix SN dN Cn Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidParentSpec rayM H hH Sbad W Ψ η₀ mesh εaffine Rcap Cs T S D Ce Z := by
  obtain ⟨K,hK,SE,dE,hpaid⟩:=actual_affine_error_uniform_component_payment (α:=α) rayM H hH
    A degree windowDegree hc hs Sbad hbad W εaffine mesh Cs hε hmesh Qfix hQ hQt hQ72 Cn hCn
  let S:=SE∪SN
  let D:=max dE dN
  have hSE : SE⊆S := Finset.subset_union_left
  have hSN : SN⊆S := Finset.subset_union_right
  have hdE : dE≤D := le_max_left _ _
  have hdN : dN≤D := le_max_right _ _
  refine ⟨S,D,K,hK,?_⟩
  filter_upwards [hpaid,hnormalized] with Z hp hn
  refine ⟨hp.1,?_⟩
  intro hZ s p caps hb₁ hb₂ hplain hwindows θ w σ freq hm R seed Mrow hR hseed hRcap hMrow hMrow1
    hfit hw hwm hσ hzslot haff beta hbeta reflected key firstHeight height hheight hfreq μ amp P control
    υ hυ
  let : DecidableEq T:=Classical.decEq T
  have hsource:=hn hZ s p caps hb₁ hb₂ hplain hwindows θ w σ freq hm R seed Mrow hR hseed hRcap
    hMrow hMrow1 hfit hw hwm hσ hzslot haff beta hbeta reflected key firstHeight height hheight hfreq
    υ hυ
  have hcontrol:=geometry_affine_error_control_mono p SN S dN D hSN hdN (Fintype.card T) reflected key
    firstHeight height hheight
  let N:=Fintype.card α
  let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
  let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))+(1-Mrow)
  have hnum : Cn*((p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN)*Z^exponent/(seed.absNorm:ℝ)≤
      Cn*control*Z^exponent/(seed.absNorm:ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrol hCn)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (Nat.cast_nonneg _)
  have hreceipt := geometry_affine_error_normalized_receipt_mono degree windowDegree reflected s R seed Ψ
    Z Mrow amp (μ/64) (μ/8) firstHeight hZ key P υ caps.zero₁ caps.zero₂ Qfix fixedBadMask _ _ hnum
    hsource
  have hR20 : (R.absNorm:ℝ)≤Z^(20:ℝ):=hRcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hRcap20)
  exact hp.2 hZ T s p caps η₀ θ w σ freq hm R seed Mrow hR hseed hR20 hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta S D hSE hdE Ψ reflected key firstHeight height hheight υ hυ hreceipt

variable [Cycle63.AffineLedger] in
/-- Conditional finite-carrier adapter at a parent. Each exact normalized callback fixes
its constants before Z and all moving sources, then the original error is paid. -/
theorem actual_affine_error_parent_paid_of_normalized
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)(W : ℝ→ℂ)
    (Ψ : 𝓢(ℝ,ℂ))(η₀ : Character)(εaffine mesh Rcap Cs : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)(hRcap20 : Rcap≤20)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (hnormalized : ∀T : Finset α,∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedParentSpec rayM H hH Sbad W Ψ η₀ mesh εaffine Rcap Cs T
          degree windowDegree Qfix SN dN Cn Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidParentSpec rayM H hH Sbad W Ψ η₀ mesh εaffine Rcap Cs T S D Ce Z := by
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hn⟩:=hnormalized T
  exact actual_affine_error_complete_parent_payment rayM H hH T A degree windowDegree dN hc hs
    Sbad hbad W Ψ η₀ εaffine mesh Rcap Cs hε hmesh hRcap20 Qfix hQ hQt hQ72 SN Cn hCn hn

/-- Explicit conditional callback: the uniform exact normalized-family estimate.
Constants and profiles precede every actual moving source and original character family. -/
def GeometryAffineErrorNormalizedSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (degree windowDegree : ℕ)(Qfix : Ideal O)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cn Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height → (∀i,|freq i|≤height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i)))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s 1 1 Ψ Z 1 amp (μ/64) (μ/8)
        firstHeight hZ key P υ (affine_profile_zero p 0) (affine_profile_zero p 1)
        Qfix fixedBadMask (Cn*control*Z^exponent)

/-- The original retained error paid by its prime average exactly once. -/
def GeometryAffineErrorPaidSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Ce Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height → (∀i,|freq i|≤height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i)))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s 1 1 Ψ Z 1 amp (μ/64) (μ/8) firstHeight
        hZ reflected key P υ‖≤Ce*control*Z^(-((Cycle63.AffineLedger.lowReserve/4):ℝ))

set_option maxHeartbeats 400000 in
/-- Conditional adapter from the exact uniform normalized-family callback to
paid original retained error. The callback is the remaining analytic obligation:
the parent payment at the unit puncture and seed and the radial scale one. -/
theorem actual_affine_error_complete_payment
    (T : Finset α)(A degree windowDegree dN : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (SN : Finset (ℕ×ℕ))(Cn : ℝ)(hCn : 0≤Cn)
    (hnormalized : ∀ᶠZ : ℝ in atTop,
      GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
        degree windowDegree Qfix SN dN Cn Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  obtain ⟨Cs,_,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) rayM H hH W hW hWs
  obtain ⟨K,hK,SE,dE,hpaid⟩:=actual_affine_error_uniform_component_payment (α:=α) rayM H hH
    A degree windowDegree hc hs Sbad hbad W εaffine mesh Cs hε hmesh Qfix hQ hQt hQ72 Cn hCn
  let S:=SE∪SN
  let D:=max dE dN
  have hSE : SE⊆S := Finset.subset_union_left
  have hSN : SN⊆S := Finset.subset_union_right
  have hdE : dE≤D := le_max_left _ _
  have hdN : dN≤D := le_max_right _ _
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  refine ⟨S,D,K,hK,?_⟩
  filter_upwards [hpaid,hnormalized,hsources,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>ηseed) 1 (geometryLossUnit 1 εaffine/16)
      one_pos (by positivity)] with Z hp hn hsrc hanchor
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hwin reflected key firstHeight height
    hheight hfreq s μ N δ amp P control υ hυ
  let : DecidableEq T:=Classical.decEq T
  have hsource:=hn hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hwin reflected key firstHeight height hheight hfreq υ hυ
  have hcontrol:=geometry_affine_error_control_mono p SN S dN D hSN hdN (Fintype.card T) reflected key
    firstHeight height hheight
  let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-((Cycle63.AffineLedger.lowReserve/2):ℝ))
  have hnum : Cn*((p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN)*Z^exponent≤
      Cn*control*Z^(exponent+(1-1))/((1:Ideal O).absNorm:ℝ) := by
    rw [sub_self,add_zero,show ((1:Ideal O).absNorm:ℝ)=1 by simp,div_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrol hCn)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hreceipt := geometry_affine_error_normalized_receipt_mono degree windowDegree reflected s 1 1 Ψ
    Z 1 amp (μ/64) (μ/8) firstHeight hZ key P υ (affine_profile_zero p 0)
    (affine_profile_zero p 1) Qfix fixedBadMask _ _ hnum hsource
  obtain ⟨hmatch,hfit,hzslot,haff,hbeta⟩:=affine_exceptional_first_level_data rayM H hH
    W hW hWs η₀ ηseed θ w σ freq hσ state hη p t X₁ X₂ hX₁ hX₂ hZ (geometryLossUnit 1 εaffine) hwin
    (hanchor.2 () 1 le_rfl)
  have caps:=hsrc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have h:=hp.2 hZ T s p {caps with card:=le_rfl} η₀ θ w σ freq hmatch 1 1 1 one_ne_zero
    squarefree_one (by simpa using Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤20)) zero_le_one
    le_rfl hfit hwm hzslot haff _ hbeta S D hSE hdE Ψ reflected key firstHeight height hheight υ hυ
    hreceipt
  refine h.trans_eq ?_
  rw [sub_self,add_zero,show ((1:Ideal O).absNorm:ℝ)=1 by simp,div_one]

/-- Conditional finite-carrier adapter. Each exact normalized callback fixes
its constants before Z and all moving sources, then the original error is paid. -/
theorem actual_affine_error_uniform_paid_of_normalized
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (hnormalized : ∀T : Finset α,∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0≤Ce ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineErrorPaidSpec rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hn⟩:=hnormalized T
  exact actual_affine_error_complete_payment rayM H hH T A degree windowDegree dN hc hs
    Sbad hbad W hW hWs Ψ ηseed η₀ εaffine mesh hε hmesh Qfix hQ hQt hQ72 SN Cn hCn hn

end
end OAI.SevenEighths.Cycle63InitialMass
