import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryUniformControls
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineAmplification
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.AffineProfileZero
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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
open CenteredMomentPrimeElements CenteredMomentEnergyFirstAnnularAdmission
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance affineExceptionalPaymentSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The complete literal extracted exceptional source mass of a parent with first-stage
puncture `R`, seed `seed` and radial scale `Z^Mrow`. The first detector is independent
of the second ball profile, and 56/P is included in each term. -/
def geometryAffineErrorExceptionalMass (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t v : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O)) (Qfix : Ideal O) (m : O)
    (υ : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key)
    (fun _=>logAnnulus)
  ∑j : rows,∑B : actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val),
    ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
        (Z^Mrow) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
          Z Mrow amp ξ reserve (9/4) t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀

/-- The physical D shell remains outside the scalar saving. -/
def geometryAffineExceptionalShell (reflected : Bool) (Z : ℝ) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
  if reflected then 1/Hshell else 8192*Hshell

/-- The original-full-zero-filtered main exceptional remainder of a parent with first-stage
puncture `R`, seed `seed` and radial scale `Z^Mrow`, with an arbitrary first detector and
block-dependent inducing ray. The radial exponent `Mrow` is also the price of the second weight. -/
def geometryAffineMainExceptionalNorm (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve firstHeight : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (Qfix : Ideal O) (m : O)
    (χ : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key hz₁ hz₂→RayCharacter) : ℝ :=
  let phase:=fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)
  ∑j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key hz₁ hz₂,
    ‖geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve (9/4) firstHeight
      (Fintype.card ι) hZ key Mrow (Real.logb Z (volume s)) phase j.val*
      (mainExceptionalDatum (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve (9/4)
        firstHeight (Fintype.card ι) hZ key j.val.1 hz₁ hz₂ j.val.2) (χ j) Qfix m).block.value ballProfile‖

open Cycle63InitialSource QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineExceptionalPaymentFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

private theorem affine_conductor_power_le (Z N E target : ℝ) (hZ : 1<Z) (hN : 0<N)
    (h : Real.logb Z N+E≤target) : N*Z^E≤Z^target := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  calc N*Z^E=Z^(Real.logb Z N)*Z^E := by rw [Real.rpow_logb hZ0 hZ.ne' hN]
    _=Z^(Real.logb Z N+E) := (Real.rpow_add hZ0 _ _).symm
    _≤Z^target := Real.rpow_le_rpow_of_exponent_le hZ.le h

private theorem affine_exceptional_parent_fold
    (Cd fee shellRaw shell fixed cond A coef lower control height mass massCap bro Da power
      target seed : ℝ)
    (hshell : shellRaw=shell) (hmass : mass≤ massCap) (hpow : cond*power≤target)
    (hCd : 0≤Cd) (hfee : 0≤fee) (hs : 0≤ shell) (hf : 0≤fixed) (hA : 0≤A) (hc : 0≤ coef)
    (hl : 0≤lower) (hcontrol : 0≤ control) (hh : 0≤height) (hm : 0≤ mass) (hb : 0≤bro)
    (hcp : 0≤ cond*power) (hseed : 0≤ seed) :
    Cd*(fee*shellRaw*(fixed*cond)*A*coef*lower*(control*height*mass^6)*bro*Da^2)*power/seed≤
      (Cd*fee*fixed*A*coef*lower*massCap^6*bro*Da^2)*shell*control*height*target/seed := by
  subst shell
  have h₁:=mul_le_mul (pow_le_pow_left₀ hm hmass 6) hpow hcp (pow_nonneg (hm.trans hmass) 6)
  have hK : 0≤Cd*fee*fixed*A*coef*lower*bro*Da^2*shellRaw*control*height := by positivity
  calc Cd*(fee*shellRaw*(fixed*cond)*A*coef*lower*(control*height*mass^6)*bro*Da^2)*power/seed
      =(Cd*fee*fixed*A*coef*lower*bro*Da^2*shellRaw*control*height)*(mass^6*(cond*power))/seed := by
        ring
    _≤(Cd*fee*fixed*A*coef*lower*bro*Da^2*shellRaw*control*height)*(massCap^6*target)/seed :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hK) hseed
    _=_ := by ring

private theorem affine_exceptional_main_exponent (ε δ θ amp V M ell ω plain ea ec loss : ℝ) :
    (2*ε+2*δ+2*116*θ+(3*amp)/3+V-(M+ell)+4*(3*amp)/3+5*ω/6+2*plain/3+3*ea+
      3*ec-(3*amp)/3)+loss=
    2*ε+2*δ+232*θ+V-(M+ell)+4*amp+5*ω/6+2*plain/3+3*ea+3*ec+loss := by ring

section Parent
variable [Cycle63.AffineLedger]

/-- The logarithmic volume of an input is paid by the cell of its slot sum: the slot window and
the plane in the unit one bound it by the total length of that cell. -/
theorem input_log_volume_cell_bound {κ : Type*} [Fintype κ] (s : Input κ) (Z : ℝ) (hZ : 1<Z)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B) :
    Real.logb Z (volume s)≤Cycle63.AffineLedger.totalA
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))) := by
  have hh:=Cycle63.AffineLedger.normalized_cell_bounds (M:=1) (n₁:=length Z s.X₁)
    (n₂:=length Z s.X₂) (z:=∑j,Real.logb Z (s.P j)) (by norm_num)
    (by simpa only [mul_one] using hzslot) (by simpa only [mul_one] using haff)
  have htotal:=hh.2.2.2.1
  simp only [div_one,one_mul] at htotal
  rw [CenteredMomentEnergyInputParentCapacity.input_volume_log]
  linarith [CenteredMomentEnergyInputParentCapacity.raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    CenteredMomentEnergyInputParentCapacity.raw_log_le_length Z s.X₂ hZ s.X₂_pos]

private theorem affine_exceptional_post_coefficient (Z a b ray cap Cd factor seedNorm : ℝ)
    (hZ : 0<Z) :
    ray*(Cycle63.AffineLedger.primePaymentConstant*(cap+1)*(Cd*factor*Z^a/seedNorm)*Z^b)=
      Cd*((ray*Cycle63.AffineLedger.primePaymentConstant*(cap+1))*factor)*Z^(a+b)/seedNorm := by
  rw [Real.rpow_add hZ]
  ring

private theorem affine_exceptional_post_normalization
    (Z ε δ θ amp Vold Vnew M ell ω plain ea ec loss ray cap Cd shellOld shellNew
      fixed norm A coef lower control bro Da seedNorm : ℝ)
    (hZ : 0<Z)(hV : Vold=Vnew)(hshell : shellOld=shellNew) :
    ray*(Cycle63.AffineLedger.primePaymentConstant*(cap+1)*(Cd*(shellOld*(fixed*norm)*A*coef*lower*control*bro*Da^2)*
      Z^(2*ε+2*δ+2*116*θ+(3*amp)/3+Vold-(M+ell)+4*(3*amp)/3+5*ω/6+2*plain/3+3*ea+
        3*ec-(3*amp)/3)/seedNorm)*Z^loss)=
    Cd*((ray*Cycle63.AffineLedger.primePaymentConstant*(cap+1))*shellNew*(fixed*norm)*A*coef*lower*control*bro*Da^2)*
      Z^(2*ε+2*δ+232*θ+Vnew-(M+ell)+4*amp+5*ω/6+2*plain/3+3*ea+3*ec+loss)/seedNorm := by
  rw [hV,hshell,affine_exceptional_post_coefficient Z _ _ _ _ _ _ _ hZ,
    affine_exceptional_main_exponent]
  ring

/-- An explicit source kernel boundary: the output constants occur in the
predicate itself, so choosing them never unfolds a proof-valued tuple. -/
private def AffineMainExceptionalKernelSpec
    (μ : ℝ) (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ)
    (Qfix : Ideal O) (Kfix Cd Da Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input ι)(hlo : s.lo=fun _=>1)(hhi : s.hi=fun _=>2)
    (hη : (s.η.modulus.absNorm:ℝ)≤Z^(2:ℝ))(hend : Endpoints (9/4) (9/4) (9/4) s)
    (hlower : 1≤ s.lower)(hsP : ∀i,1≤ s.P i)(p : Profiles (1/4) (9/4))
    (hW₁ : s.W₁=p.profile 0)(hW₂ : s.W₂=p.profile 1)
    (R seed : Ideal O)(hR : R≠0)(hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hV : volume s≤Z^(2:ℝ))(hsourcepos : 0<sourceRadius s)
    (hsource : sourceRadius s≤Z^(3:ℝ))
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
    (hRN : (R.absNorm:ℝ)≤Z^(20:ℝ))
    (M amp reserve t plainLoss : ℝ)(hM : 0≤M)(hKM : Z^M≤Z^(2:ℝ))
    (hamp : 0≤amp)(hreserve : 0≤ reserve)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
    (hs₁ : ∀x,s.W₁ x≠0→(1/4:ℝ)≤x)(hs₂ : ∀x,s.W₂ x≠0→(1/4:ℝ)≤x)
    (reflected : Bool)(Ψ : 𝓢(ℝ,ℂ))(key : ℤ×(Fin 5→ℤ))
    (m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (χ : geometryMainNonzeroBlocks reflected s R seed Z M amp (μ/64) reserve (9/4) t
      (Fintype.card ι) hZ key hz₁ hz₂→RayCharacter)
    (P : Finset (Ideal O))(beta cap : ℝ)
    (hbeta : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop)
    (hcap : 0≤ cap)(hampEq : amp=Cycle63.AffineLedger.amp beta)
    (hprime : Z^(Cycle63.AffineLedger.amp beta-μ/128)≤(P.card:ℝ)),
    let fee:=(Fintype.card RayCharacter:ℝ)*Cycle63.AffineLedger.primePaymentConstant*(cap+1)
    let coef:=max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
      (Fintype.card ι) (9/4) J Qfix Kfix)
    (56/(P.card:ℝ))*((cap+6*Cycle63.AffineLedger.amp beta)/(Cycle63.AffineLedger.amp beta/2))*
      geometryAffineMainExceptionalNorm s R seed Ψ Z M amp (μ/64) reserve t hZ reflected key hz₁ hz₂
        Qfix m χ≤
    Cd*(fee*geometryAffineExceptionalShell reflected Z key*
      (fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 (9/4:ℝ))^(Fintype.card ι)*
      coef*geometryExceptionalLowerConstant (Fintype.card ι) 1 (1/4)*
      (p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6)*
      ((9/4:ℝ)^(Fintype.card ι))^(1/3:ℝ)*Da^2)*
      Z^(2*(μ/128)+2*(μ/128)+232*(μ/2048)+Real.logb Z (volume s)-
        (M+Real.logb Z (s.η.modulus.absNorm:ℝ))+4*amp+
        5*(frequencyLoss Z 32 (μ/64)+reserve)/6+2*plainLoss/3+3*(μ/128)+3*(μ/128)+μ/128)/
      (seed.absNorm:ℝ)

set_option maxHeartbeats 500000 in
private theorem affine_main_exceptional_kernel
    (μ : ℝ)(hμ : 0<μ)(hξ₁ : μ/64≤1)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)}) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck Kfix Cd Da : ℝ),
      0<Cd ∧ 0<Da ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
        AffineMainExceptionalKernelSpec (ι:=ι) μ J Sp Ck Qfix Kfix Cd Da Z := by
  let full:=actual_geometry_main_exceptional_norm_payment (ι:=ι)
    (1/4) (9/4) (by norm_num) (by norm_num) (fun _=>1) (fun _=>2)
    (μ/128) (μ/128) (μ/2048) (by positivity) (by positivity) (by positivity)
    (9/4) (9/4) (by norm_num) (by norm_num) 1 (μ/128) (μ/128) (μ/64)
    (by norm_num) (by positivity) (by positivity) (by positivity) hξ₁
  let saved:=full.2.2.2 Qfix hQ hQt hQ72
  refine ⟨full.1,full.2.1,full.2.2.1,saved.1,saved.2.1,saved.2.2.1,
    saved.2.2.2.down.2.1,saved.2.2.2.down.2.2.1,?_⟩
  filter_upwards [saved.2.2.2.down.2.2.2] with Z hk
  refine ⟨hk.1,?_⟩
  intro hZ s hlo hhi hη hend hlower hsP p hW₁ hW₂ R seed hR hs hz₁ hz₂ hV hspos hsource hpool hRN
    M amp reserve t plainLoss hM hKM hamp hreserve hX₁ hX₂ hY₁ hY₂ hs₁ hs₂ reflected Ψ key
    m hm hml hm2 χ P beta cap hbeta hcap hampEq hprime fee coef
  have hraw:=hk.2 hZ s hlo hhi hη hend hlower hsP p hW₁ hW₂
    R seed hR hs hs.ne_zero hz₁ hz₂ hV hspos hsource hpool hRN M amp reserve t plainLoss hM hKM
    hamp hreserve hX₁ hX₂ hY₁ hY₂ (1/4) (1/4) (by norm_num) (by norm_num) hs₁ hs₂ reflected Ψ key
    m hm hml hm2 χ
  have hpost:=hraw.2 P beta (μ/128) cap hbeta hcap (by rw [←hampEq];ring) hprime
  have hplo : (∏i,s.lo i)=1 := by rw [hlo];simp only [Finset.prod_const,one_pow]
  have hveq : geometryExceptionalVolume s=volume s := rfl
  have hsheq : (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
    else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))=
      geometryAffineExceptionalShell reflected Z key := by
    rw [hplo];unfold geometryAffineExceptionalShell;split_ifs <;> ring
  dsimp (config := { zetaDelta := false }) only at hpost
  have hscalar:=affine_exceptional_post_normalization Z (μ/128) (μ/128) (μ/2048)
    amp (Real.logb Z (geometryExceptionalVolume s)) (Real.logb Z (volume s)) M
    (Real.logb Z (s.η.modulus.absNorm:ℝ)) (frequencyLoss Z 32 (μ/64)+reserve) plainLoss
    (μ/128) (μ/128) (μ/128) (Fintype.card RayCharacter:ℝ) cap saved.2.1
    (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
      else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))
    (geometryAffineExceptionalShell reflected Z key) fixedPresentationCost
    (s.η.modulus.absNorm:ℝ) ((max 1 (9/4:ℝ))^(Fintype.card ι)) coef
    (geometryExceptionalLowerConstant (Fintype.card ι) 1 (1/4))
    (p.control full.2.1^2*(1+‖t‖)^(2*full.1)*(∏i,s.M i)^6)
    (((9/4:ℝ)^(Fintype.card ι))^(1/3:ℝ)) saved.2.2.1 (seed.absNorm:ℝ)
    (zero_lt_one.trans hZ) (congrArg (Real.logb Z) hveq) hsheq
  exact hpost.trans_eq hscalar

/-- The extracted exceptional error mass of a parent input `s` with its source gates,
first-stage puncture `R`, seed `seed` and radial scale `Z^Mrow`, for every first detector
and admissible extracted character. The constant does not depend on the character of the
parent: its conductor enters only through `hfit`, and the bound carries the radial
deficit `Z^(1-Mrow)`. -/
def GeometryAffineExceptionalErrorParentSpec
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ) (εaffine mesh : ℝ) (Qfix : Ideal O) (m : O)
    (Cs C : ℝ) (Sp : Finset (ℕ×ℕ)) (degree : ℕ) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (η₀ : Character)(θ : α→RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRcap : (R.absNorm:ℝ)≤Z^(20:ℝ))(hMrow : 0≤ Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16)
    (hwm : ∀j,w j≤ mesh)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (beta : ℝ)(hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))),
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight secondHeight : ℝ),
    let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let firsts:=GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64) hK key
    ∀(υ : firsts→elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64) hK key q.1.val) ψ)
          fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      geometryAffineErrorExceptionalMass s R seed Ψ Z Mrow amp (μ/64) (μ/8) firstHeight secondHeight
        hZ reflected key P Qfix m υ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖secondHeight‖)^degree*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)

set_option maxHeartbeats 600000 in
private theorem affine_error_exceptional_parent_bound
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad) (W : ℝ→ℂ)
    (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Cs : ℝ) :
    ∃C : ℝ,0≤C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalErrorParentSpec (α:=α)
        rayM H hH Sbad W εaffine mesh Qfix m Cs C Sp degree Z := by
  classical
  have hfixed:=fixedPresentationCost_pos
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((Cycle63.AffineLedger.lowReserve)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have hμdef : geometryLossUnit 1 εaffine=μ := rfl
  have hξ : 0≤μ/64 := by positivity
  have hξ₁ : μ/64≤1 := by linarith
  obtain ⟨J,Sp,Ck,hfull⟩:=actual_geometry_error_exceptional_norm_full (ι:=α)
    (1/4) (9/4) (by norm_num) (by norm_num) (fun _=>1) (fun _=>2)
    (μ/128) (μ/128) (μ/2048) (by positivity) (by positivity) (by positivity)
    (9/4) (9/4) (by norm_num) (by norm_num) 1 (μ/128) (μ/128) (μ/64)
    (by norm_num) (by positivity) (by positivity) hξ hξ₁
  obtain ⟨Kfix,Cd,Da,hK,hCd,hDa,hkernel⟩:=hfull Qfix hQ hQt hQ72
  let coef:=max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
    (Fintype.card α) (9/4) J Qfix Kfix)
  have hcoef : 0≤ coef := le_trans (by norm_num) (le_max_left _ _)
  have hlower : 0≤geometryExceptionalLowerConstant (Fintype.card α) 1 (1/4) := by
    unfold geometryExceptionalLowerConstant; positivity
  let C:=Cd*(56*128*3*8*(Fintype.card RayCharacter:ℝ)^2)*fixedPresentationCost*
    (max 1 (9/4:ℝ))^(Fintype.card α)*coef*geometryExceptionalLowerConstant (Fintype.card α) 1 (1/4)*
    ((max 1 Cs)^(Fintype.card α))^6*((9/4:ℝ)^(Fintype.card α))^(1/3:ℝ)*Da^2
  have hC : 0≤C := by
    have hCd0 : 0≤Cd := hCd.le
    dsimp only [C]; positivity
  refine ⟨C,hC,Sp,2*J,?_⟩
  filter_upwards [hkernel,
    eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh,
    eventual_geometry_small_frequency μ hμ] with Z hk hc hfreq
  refine ⟨hk.1,?_⟩
  intro hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta
  subst hbeta
  intro amp P μ' Ψ reflected key firstHeight secondHeight hK' firsts υ hυ
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb:=Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hampeq : amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))) := rfl
  have hamp : 0≤amp := (Cycle63.AffineLedger.amp_pos hb).le
  have hamp₁ : amp≤1 := (Cycle63.AffineLedger.amp_bounds hb).2.trans
    (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have hω : frequencyLoss Z 32 (μ/64)+μ/8≤3 := hfreq.2.2.trans (by linarith)
  have hN1 : (1:ℝ)≤(s.η.modulus.absNorm:ℝ) := by
    exact_mod_cast norm_at_least_one s.η.modulus s.η.modulus_ne_bot
  have hNpos : (0:ℝ)<(s.η.modulus.absNorm:ℝ) := zero_lt_one.trans_le hN1
  have hell : 0≤Real.logb Z (s.η.modulus.absNorm:ℝ) := Real.logb_nonneg hZ hN1
  have hMrow2 : Mrow≤2 := by linarith
  have hηZ : (s.η.modulus.absNorm:ℝ)≤Z^(2:ℝ) := by
    rw [←Real.rpow_logb hZ0 hZ.ne' hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hcop : ∀q : firsts,∀p∈elementPool P,∀j I,
      I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64) hK' key firstHeight q).slots j→
        IsCoprime (Ideal.span {p}) I := by
    intro q prime hp j I hI
    have hslots:=actual_child_full_slot_coprime s (Ideal.span {prime})
      (hc.2 _ hb.1 hb.2 s η₀ θ w σ freq W hmatch hwm ⟨prime,hp⟩)
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64) hK' key q.1.val) R q.2
      (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64) hK' key q.1.val) firstHeight
    exact hslots j I hI
  have hplain (X : ℝ) (hX : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
      (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤X) :
      Z^((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/4+
        Cycle63.AffineLedger.plainLossCap))≤X := by
    convert hX using 2; ring
  have hraw:=hk.2 hZ s caps.lo caps.hi hηZ caps.endpoints
    (by rw [caps.lower]) caps.scales p caps.profile₁ caps.profile₂
    R seed hR hseed hseed.ne_zero caps.zero₁ caps.zero₂ caps.volume
    caps.sourcePositive caps.sourceCap caps.volumeLog caps.poolCap hRcap
    Mrow amp (μ/8) firstHeight secondHeight
    ((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/4+Cycle63.AffineLedger.plainLossCap)
    hMrow hMrow2 hamp hamp₁ (by positivity) hω
    (hplain _ caps.plain₁) (hplain _ caps.plain₂) (hplain _ caps.plain₃) (hplain _ caps.plain₄)
    (1/4) (1/4) (by norm_num) (by norm_num) caps.support₁ caps.support₂
    reflected Ψ key rayM inferInstance H Sbad hbad υ hcop hυ m hm hml hm2
  have hlog:=input_log_volume_cell_bound s Z hZ hzslot haff
  have hsave:=(affine_exceptional_exponent_saving _ (Real.logb Z (volume s)) 0
    (2*(μ/128)+2*(μ/128)+442*(μ/2048)+5*(frequencyLoss Z 32 (μ/64)+μ/8)/6+
      3*(μ/128)+3*(μ/128)+(Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/6)
    hb hlog le_rfl (by linarith [hfreq.2.2])).2
  have hplo : (∏i,s.lo i)=1 := by rw [caps.lo]; simp only [Finset.prod_const,one_pow]
  have hsheq : (if reflected then 1/(Z^((key.2 1:ℝ)*Real.logb Z 2))
      else (4/((∏i,s.lo i)*(1/4)*(1/4)))^2*(2*Z^((key.2 1:ℝ)*Real.logb Z 2)))=
        geometryAffineExceptionalShell reflected Z key := by
    rw [hplo]; unfold geometryAffineExceptionalShell; split_ifs <;> ring
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell]; split_ifs <;> positivity
  have hprod : (∏i,s.M i)≤(max 1 Cs)^(Fintype.card α) := by
    calc
      _≤∏_i : α,max 1 Cs := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.M_ge_one i))
        (fun i _=>(caps.controls i).trans (le_max_right _ _))
      _=_ := by simp only [Finset.prod_const,Finset.card_univ]
  have hmass : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  have hveq : Real.logb Z (geometryExceptionalVolume s)=Real.logb Z (volume s) := rfl
  dsimp only at hraw
  refine hraw.trans ((affine_exceptional_parent_fold _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Z^(-(1/100:ℝ)+(1-Mrow))) _ hsheq hprod (affine_conductor_power_le Z _ _ _ hZ hNpos ?_)
    hCd.le (by positivity) hshell hfixed.le (by positivity) hcoef hlower (by positivity)
    (by positivity) hmass (by positivity) (by positivity) (Nat.cast_nonneg _)).trans_eq ?_)
  · linarith [hsave]
  · rfl

/-- One constant and one height degree, chosen before the scale, pay the extracted
exceptional error mass of every parent input with source gates of profile cap `Cs`, on
every slot subset of the ambient slot type. -/
theorem actual_affine_error_exceptional_parent_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad) (W : ℝ→ℂ)
    (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Cs : ℝ) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀T : Finset α,GeometryAffineExceptionalErrorParentSpec (α:=T)
        rayM H hH Sbad W εaffine mesh Qfix m Cs C Sp degree Z := by
  classical
  have data (T : Finset α):=affine_error_exceptional_parent_bound (α:=T) rayM H hH Sbad hbad W
    εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  choose Ct hCt St dt hspec using data
  obtain ⟨C,hC,S,jdeg,kdeg,ldeg,huniform⟩:=geometry_uniform_profile_controls
    Ct St (fun _=>0) dt (fun _=>0) hCt
  refine ⟨C,hC,S,kdeg,?_⟩
  filter_upwards [Filter.eventually_all.mpr hspec] with Z hz
  refine ⟨(hz ∅).1,?_⟩
  intro T hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta amp P μ Ψ reflected key firstHeight secondHeight hK firsts υ hυ
  have hbound:=(hz T).2 hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1
    hfit hwm hzslot haff beta hbeta Ψ reflected key firstHeight secondHeight υ hυ
  have hcontrol:=huniform T p 1 (1+‖secondHeight‖) 1 le_rfl (by linarith [norm_nonneg secondHeight])
    le_rfl
  simp only [one_pow,mul_one] at hcontrol
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell]; split_ifs <;> positivity
  have hpower : 0≤Z^(-(1/100:ℝ)+(1-Mrow)) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  refine hbound.trans ?_
  calc Ct T*geometryAffineExceptionalShell reflected Z key*(p.control (St T))^2*
        (1+‖secondHeight‖)^(dt T)*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)
      =(Ct T*(p.control (St T))^2*(1+‖secondHeight‖)^(dt T))*
        (geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)+(1-Mrow)))/(seed.absNorm:ℝ) := by
        ring
    _≤(C*(p.control S)^2*(1+‖secondHeight‖)^kdeg)*
        (geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)+(1-Mrow)))/(seed.absNorm:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcontrol (mul_nonneg hshell hpower))
        (Nat.cast_nonneg _)
    _=_ := by ring

/-- The filtered main exceptional remainder of a parent input `s` with its source gates,
first-stage puncture `R`, seed `seed` and radial scale `Z^Mrow`, after its one
prime-average cancellation. The constant does not depend on the character of the parent:
its conductor enters only through `hfit`, and the bound carries the radial deficit
`Z^(1-Mrow)`. -/
def GeometryAffineExceptionalMainParentSpec
    (Sbad : Finset (Ideal O)) (W : ℝ→ℂ) (εaffine mesh : ℝ) (Qfix : Ideal O) (m : O)
    (Cs C : ℝ) (Sp : Finset (ℕ×ℕ)) (degree : ℕ) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (η₀ : Character)(θ : α→RayQuotient.Characters rayM H)(w σ freq : α→ℝ)
    (hm : Matches rayM H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRcap : (R.absNorm:ℝ)≤Z^(20:ℝ))(hMrow : 0≤ Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16)
    (hwm : ∀j,w j≤ mesh)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (beta : ℝ)(hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))),
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
    ∀χ : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) firstHeight
      (Fintype.card α) hZ key caps.zero₁ caps.zero₂→RayCharacter,
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      geometryAffineMainExceptionalNorm s R seed Ψ Z Mrow amp (μ/64) (μ/8) firstHeight hZ reflected
        key caps.zero₁ caps.zero₂ Qfix m χ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖firstHeight‖)^degree*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)

set_option maxHeartbeats 600000 in
private theorem affine_main_exceptional_parent_bound
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad) (W : ℝ→ℂ)
    (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Cs : ℝ) :
    ∃C : ℝ,0≤C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalMainParentSpec (α:=α)
        rayM H hH Sbad W εaffine mesh Qfix m Cs C Sp degree Z := by
  classical
  have hfixed:=fixedPresentationCost_pos
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 :=
    (min_le_right (εaffine/128) _).trans
      ((min_le_right ((Cycle63.AffineLedger.lowReserve)*1/128) _).trans (min_le_right (1/128) (1/128)))
  have hμdef : geometryLossUnit 1 εaffine=μ := rfl
  have hξ₁ : μ/64≤1 := by linarith
  obtain ⟨J,Sp,Ck,Kfix,Cd,Da,hCd,hDa,hkernel⟩:=affine_main_exceptional_kernel (ι:=α) μ hμ hξ₁
    Qfix hQ hQt hQ72
  let coef:=max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
    (Fintype.card α) (9/4) J Qfix Kfix)
  have hcoef : 0≤ coef := le_trans (by norm_num) (le_max_left _ _)
  have hlower : 0≤geometryExceptionalLowerConstant (Fintype.card α) 1 (1/4) := by
    unfold geometryExceptionalLowerConstant; positivity
  let fee:=(Fintype.card RayCharacter:ℝ)*Cycle63.AffineLedger.primePaymentConstant*(amplifierCap 2 0 1+1)
  have hfee : 0≤fee := by
    have hfloor:=Cycle63.AffineLedger.amplifierFloor_pos
    dsimp only [fee,amplifierCap,Cycle63.AffineLedger.primePaymentConstant]; positivity
  let C:=Cd*fee*fixedPresentationCost*(max 1 (9/4:ℝ))^(Fintype.card α)*coef*
    geometryExceptionalLowerConstant (Fintype.card α) 1 (1/4)*((max 1 Cs)^(Fintype.card α))^6*
    ((9/4:ℝ)^(Fintype.card α))^(1/3:ℝ)*Da^2
  have hC : 0≤C := by
    have hCd0 : 0≤Cd := hCd.le
    dsimp only [C]; positivity
  refine ⟨C,hC,Sp,2*J,?_⟩
  filter_upwards [hkernel,
    eventual_affine_cell_prime_pools rayM H hH Sbad hbad (μ/128) (by positivity),
    eventual_geometry_small_frequency μ hμ] with Z hk hpool hfreq
  refine ⟨hk.1,?_⟩
  intro hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta
  subst hbeta
  intro amp P μ' Ψ reflected key firstHeight χ
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb:=Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hampeq : amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))) := rfl
  have hamp : 0≤amp := (Cycle63.AffineLedger.amp_pos hb).le
  have hN1 : (1:ℝ)≤(s.η.modulus.absNorm:ℝ) := by
    exact_mod_cast norm_at_least_one s.η.modulus s.η.modulus_ne_bot
  have hNpos : (0:ℝ)<(s.η.modulus.absNorm:ℝ) := zero_lt_one.trans_le hN1
  have hell : 0≤Real.logb Z (s.η.modulus.absNorm:ℝ) := Real.logb_nonneg hZ hN1
  have hMrow2 : Mrow≤2 := by linarith
  have hηZ : (s.η.modulus.absNorm:ℝ)≤Z^(2:ℝ) := by
    rw [←Real.rpow_logb hZ0 hZ.ne' hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hKM : Z^Mrow≤Z^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hMrow2
  have hplain (X : ℝ) (hX : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-
      (Real.logb Z (s.η.modulus.absNorm:ℝ)/4+Cycle63.AffineLedger.plainLossCap))≤X) :
      Z^((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/4+
        Cycle63.AffineLedger.plainLossCap))≤X := by
    convert hX using 2; ring
  have hprime:=(hpool.2 _ hcell.1 hcell.2.1).2
  have hpost:=hk.2 hZ s caps.lo caps.hi hηZ caps.endpoints (by rw [caps.lower]) caps.scales p
    caps.profile₁ caps.profile₂ R seed hR hseed caps.zero₁ caps.zero₂ caps.volume
    caps.sourcePositive caps.sourceCap caps.poolCap hRcap Mrow amp (μ/8) firstHeight
    ((Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/4+Cycle63.AffineLedger.plainLossCap)
    hMrow hKM hamp (by positivity) (hplain _ caps.plain₁) (hplain _ caps.plain₂)
    (hplain _ caps.plain₃) (hplain _ caps.plain₄) caps.support₁ caps.support₂ reflected Ψ key
    m hm hml hm2 χ P _ (amplifierCap 2 0 1) hb (by norm_num [amplifierCap]) rfl hprime
  have hlog:=input_log_volume_cell_bound s Z hZ hzslot haff
  have hsave:=(affine_exceptional_exponent_saving _ (Real.logb Z (volume s)) 0
    (2*(μ/128)+2*(μ/128)+232*(μ/2048)+5*(frequencyLoss Z 32 (μ/64)+μ/8)/6+
      3*(μ/128)+3*(μ/128)+μ/128+(Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)-1)/6)
    hb hlog le_rfl (by linarith [hfreq.2.2])).1
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell]; split_ifs <;> positivity
  have hprod : (∏i,s.M i)≤(max 1 Cs)^(Fintype.card α) := by
    calc
      _≤∏_i : α,max 1 Cs := Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.M_ge_one i))
        (fun i _=>(caps.controls i).trans (le_max_right _ _))
      _=_ := by simp only [Finset.prod_const,Finset.card_univ]
  have hmass : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  dsimp only at hpost
  refine hpost.trans ((affine_exceptional_parent_fold _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Z^(-(1/100:ℝ)+(1-Mrow))) _ rfl hprod (affine_conductor_power_le Z _ _ _ hZ hNpos ?_)
    hCd.le hfee hshell hfixed.le (by positivity) hcoef hlower (by positivity)
    (by positivity) hmass (by positivity) (by positivity) (Nat.cast_nonneg _)).trans_eq ?_)
  · linarith [hsave]
  · rfl

/-- One constant and one height degree, chosen before the scale, pay the filtered main
exceptional remainder of every parent input with source gates of profile cap `Cs`, on every
slot subset of the ambient slot type. -/
theorem actual_affine_main_exceptional_parent_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad) (W : ℝ→ℂ)
    (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) (Cs : ℝ) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀T : Finset α,GeometryAffineExceptionalMainParentSpec (α:=T)
        rayM H hH Sbad W εaffine mesh Qfix m Cs C Sp degree Z := by
  classical
  have data (T : Finset α):=affine_main_exceptional_parent_bound (α:=T) rayM H hH Sbad hbad W
    εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  choose Ct hCt St dt hspec using data
  obtain ⟨C,hC,S,jdeg,kdeg,ldeg,huniform⟩:=geometry_uniform_profile_controls
    Ct St (fun _=>0) dt (fun _=>0) hCt
  refine ⟨C,hC,S,kdeg,?_⟩
  filter_upwards [Filter.eventually_all.mpr hspec] with Z hz
  refine ⟨(hz ∅).1,?_⟩
  intro T hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta amp P μ Ψ reflected key firstHeight χ
  have hbound:=(hz T).2 hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1
    hfit hwm hzslot haff beta hbeta Ψ reflected key firstHeight χ
  have hcontrol:=huniform T p 1 (1+‖firstHeight‖) 1 le_rfl (by linarith [norm_nonneg firstHeight])
    le_rfl
  simp only [one_pow,mul_one] at hcontrol
  have hshell : 0≤geometryAffineExceptionalShell reflected Z key := by
    dsimp only [geometryAffineExceptionalShell]; split_ifs <;> positivity
  have hpower : 0≤Z^(-(1/100:ℝ)+(1-Mrow)) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  refine hbound.trans ?_
  calc Ct T*geometryAffineExceptionalShell reflected Z key*(p.control (St T))^2*
        (1+‖firstHeight‖)^(dt T)*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)
      =(Ct T*(p.control (St T))^2*(1+‖firstHeight‖)^(dt T))*
        (geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)+(1-Mrow)))/(seed.absNorm:ℝ) := by
        ring
    _≤(C*(p.control S)^2*(1+‖firstHeight‖)^kdeg)*
        (geometryAffineExceptionalShell reflected Z key*Z^(-(1/100:ℝ)+(1-Mrow)))/(seed.absNorm:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcontrol (mul_nonneg hshell hpower))
        (Nat.cast_nonneg _)
    _=_ := by ring

end Parent

/-- The literal affine input of a fixed parent with character `η` at a scale where the
conductor of `η` is at most `μ/16`: its dictionary match, the conductor fit at radial scale
one, the slot window and the plane in its own slot logarithms, and its original cell. -/
theorem affine_exceptional_first_level_data {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η₀ η : Character) (θ : κ→RayQuotient.Characters rayM H) (w σ freq : κ→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50)) {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ)
    (hη : state.character=η) (p : Profiles (1/4) (9/4)) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hZ : 1<Z) (μ : ℝ)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i))
    (hanchor : Real.logb Z (η.modulus.absNorm:ℝ)≤μ/16*1) :
    let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    Matches rayM H hH s η₀ θ w σ freq W 2 Z ∧
      1+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16 ∧
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) ∧
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B ∧
      Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))=
        Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) := by
  intro s
  have hmatch : Matches rayM H hH s η₀ θ w σ freq W 2 Z := by constructor <;> intros <;> rfl
  have hsum : (∑j,Real.logb Z (s.P j))=∑i,w i := by
    refine Finset.sum_congr rfl (fun j _=>?_)
    rw [hmatch.scale j,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hηs : s.η=η := hη
  refine ⟨hmatch,?_,?_,?_,by rw [hsum]⟩
  · rw [hηs]; linarith
  · rw [hsum]; exact ⟨hwin.slots_ge,hwin.slots_le⟩
  · rw [hsum]; exact hwin.plane

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
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    let beta:=Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight secondHeight : ℝ),
    let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
    let firsts:=GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key
    ∀(υ : firsts→elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64) hK key q.1.val) ψ)
          fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      geometryAffineErrorExceptionalMass s 1 1 Ψ Z 1 amp (μ/64) (μ/8) firstHeight secondHeight
        hZ reflected key P Qfix m υ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖secondHeight‖)^degree*Z^(-(1/100:ℝ))

set_option maxHeartbeats 600000 in
/-- Actual affine error exceptional payment with one profile union and one
height degree for every finite original slot subset: the parent payment at the
unit puncture and seed and the radial scale one. -/
theorem actual_affine_error_exceptional_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalErrorSpec (α:=α)
        rayM H hH Sbad W hW hWs η εaffine mesh Qfix m C Sp degree Z := by
  obtain ⟨Cs,_,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  obtain ⟨C,hC,Sp,degree,hgeneral⟩:=actual_affine_error_exceptional_parent_payment (α:=α)
    rayM H hH Sbad hbad W εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  refine ⟨C,hC,Sp,degree,?_⟩
  filter_upwards [hgeneral,hsources,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>η) 1 (geometryLossUnit 1 εaffine/16)
      one_pos (by positivity)] with Z hg hs hanchor
  refine ⟨hg.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hwin s beta amp P μ
    Ψ reflected key firstHeight secondHeight hK firsts υ hυ
  obtain ⟨hmatch,hfit,hzslot,haff,hbeta⟩:=affine_exceptional_first_level_data rayM H hH
    W hW hWs η₀ η θ w σ freq hσ state hη p t X₁ X₂ hX₁ hX₂ hZ (geometryLossUnit 1 εaffine) hwin
    (hanchor.2 () 1 le_rfl)
  have caps:=hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have h:=(hg.2 T) hZ s p {caps with card:=le_rfl} η₀ θ w σ freq hmatch 1 1 1 one_ne_zero
    squarefree_one (by simpa using Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤20)) zero_le_one
    le_rfl hfit hwm hzslot haff beta hbeta Ψ reflected key firstHeight secondHeight υ hυ
  refine h.trans_eq ?_
  rw [sub_self,add_zero,show ((1:Ideal O).absNorm:ℝ)=1 by simp,div_one]

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
    Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    let beta:=Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
    let μ:=geometryLossUnit 1 εaffine
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ),
    ∀χ : geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) firstHeight
      (Fintype.card T) hZ key (affine_profile_zero p 0) (affine_profile_zero p 1)→RayCharacter,
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      geometryAffineMainExceptionalNorm s 1 1 Ψ Z 1 amp (μ/64) (μ/8) firstHeight hZ reflected key
        (affine_profile_zero p 0) (affine_profile_zero p 1) Qfix m χ≤
      C*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖firstHeight‖)^degree*Z^(-(1/100:ℝ))

set_option maxHeartbeats 600000 in
/-- One actual filtered main exceptional bound covers all finite slot subsets,
all original detectors and all inducing rays, preserving the physical H or 1/H:
the parent payment at the unit puncture and seed and the radial scale one. -/
theorem actual_affine_main_exceptional_payment
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η : Character) (εaffine mesh : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O) (hQ : Qfix≠0) (hQt : Qfix≠⊤) (hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃C : ℝ,0<C ∧ ∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineExceptionalMainSpec (α:=α)
        rayM H hH Sbad W hW hWs η εaffine mesh Qfix m C Sp degree Z := by
  obtain ⟨Cs,_,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α)
    rayM H hH W hW hWs
  obtain ⟨C,hC,Sp,degree,hgeneral⟩:=actual_affine_main_exceptional_parent_payment (α:=α)
    rayM H hH Sbad hbad W εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  refine ⟨C,hC,Sp,degree,?_⟩
  filter_upwards [hgeneral,hsources,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>η) 1 (geometryLossUnit 1 εaffine/16)
      one_pos (by positivity)] with Z hg hs hanchor
  refine ⟨hg.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hwin s beta amp P μ
    Ψ reflected key firstHeight χ
  obtain ⟨hmatch,hfit,hzslot,haff,hbeta⟩:=affine_exceptional_first_level_data rayM H hH
    W hW hWs η₀ η θ w σ freq hσ state hη p t X₁ X₂ hX₁ hX₂ hZ (geometryLossUnit 1 εaffine) hwin
    (hanchor.2 () 1 le_rfl)
  have caps:=hs.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have h:=(hg.2 T) hZ s p {caps with card:=le_rfl} η₀ θ w σ freq hmatch 1 1 1 one_ne_zero
    squarefree_one (by simpa using Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤20)) zero_le_one
    le_rfl hfit hwm hzslot haff beta hbeta Ψ reflected key firstHeight χ
  refine h.trans_eq ?_
  rw [sub_self,add_zero,show ((1:Ideal O).absNorm:ℝ)=1 by simp,div_one]

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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
