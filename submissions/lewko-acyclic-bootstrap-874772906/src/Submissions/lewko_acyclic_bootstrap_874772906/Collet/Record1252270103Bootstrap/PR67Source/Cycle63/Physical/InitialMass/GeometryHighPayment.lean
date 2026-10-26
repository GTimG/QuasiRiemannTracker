import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighBins
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ValuationCone
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryCompensatedHigh
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryUniformScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical

def geometryHighSide (reflected : Bool)(A : ℝ)(x : Fin 5→ℝ) : ℝ :=
  if reflected then rightExponent A x else leftExponent A x

def geometryHighFactor (reflected : Bool)(C₀ : ℝ)(bin : ℤ×(Fin 5→ℤ)) : ℝ :=
  if reflected then (geometryDCompensator bin)⁻¹ else 2*C₀^2*geometryDCompensator bin

lemma geometry_high_factor_pos (reflected : Bool)(C₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (hC : 0<C₀) : 0<geometryHighFactor reflected C₀ bin := by
  cases reflected <;> simp only [geometryHighFactor,Bool.false_eq_true,ite_false,ite_true]
  · exact mul_pos (by positivity) (geometryDCompensator_pos bin)
  · exact inv_pos.mpr (geometryDCompensator_pos bin)

lemma geometry_high_side_box (reflected : Bool)(A B : ℝ)(x : Fin 5→ℝ)
    (hB : 0≤B)(hA : |A|≤B)(hx : ∀j,0≤x j ∧ x j≤B) :
    |geometryHighSide reflected A x|≤5*B := by
  have ha:=abs_le.mp hA
  have hm (i j : Fin 5) : 0≤ max (3*x i-5*x j-x 3) 0 ∧
      max (3*x i-5*x j-x 3) 0≤3*B := by
    refine ⟨le_max_right _ _,max_le ?_ (by linarith)⟩
    linarith [(hx i).2,(hx j).1,(hx 3).1]
  apply abs_le.mpr
  cases reflected <;> simp only [geometryHighSide,Bool.false_eq_true,ite_false,ite_true]
  · dsimp only [leftExponent,geometrySurplus]
    constructor <;> linarith [(hx 0).1,(hx 0).2,(hx 1).1,(hx 1).2,(hx 2).1,(hx 2).2,
      (hx 3).1,(hx 3).2,(hx 4).1,(hx 4).2,(hm 0 1).1,(hm 0 1).2,(hm 1 0).1,(hm 1 0).2]
  · dsimp only [rightExponent,geometrySurplus]
    constructor <;> linarith [(hx 0).1,(hx 0).2,(hx 1).1,(hx 1).2,(hx 2).1,(hx 2).2,
      (hx 3).1,(hx 3).2,(hx 4).1,(hx 4).2,(hm 0 1).1,(hm 0 1).2,(hm 1 0).1,(hm 1 0).2]

variable {α : Type} [Fintype α] [DecidableEq α]

def geometryFirstHighMass (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin)) : ℝ :=
  ‖geometryColumnScalar reflected s R seed (Z^D) Z ξ D (Real.logb Z (volume s.toData))
    hK bin (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z ξ q)) j‖^2*
    ((geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin j).absNorm:ℝ)^(ε-1)

omit [DecidableEq α] in
lemma geometry_first_high_mass_nonneg (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin)) :
    0≤geometryFirstHighMass reflected s R seed W D Z ξ ε hK bin j := by
  unfold geometryFirstHighMass
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The support constant is fixed before the source and first label move. -/
theorem actual_geometry_uniform_high_mass (reflected : Bool)(N : ℕ)(lo ap : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ B ε : ℝ)(hZ : 1<Z)(hK : 0<Z^D)
    (hε : 0≤ε)(hcard : Fintype.card α≤N)(hlower : lo≤ s.lower)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ap≤x)(hs₂ : ∀x,s.W₂ x≠0→ap≤x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin)) :
    geometryFirstHighMass reflected s R seed W D Z ξ ε hK bin j≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*ε)/
        Z^(geometryHighSide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^D) Z ξ j.1.val)) := by
  have hC:=actual_geometry_support_constant s N lo ap ap hcard hlo hlower hap hap
  cases reflected
  · have hh:=actual_geometry_left_mass_compensation s R seed W D Z ξ B ε hZ hε hs hz₁ hz₂
      hsource ap ap hap hap hs₁ hs₂ bin j
    apply hh.trans
    have hsq : (4/((∏i,s.lo i)*ap*ap))^2≤(geometrySupportConstant N lo ap ap)^2 := by
      nlinarith [hC.1,hC.2]
    change (2*(4/((∏i,s.lo i)*ap*ap))^2*geometryDCompensator bin)*Z^(B*ε)/_≤
      (2*(geometrySupportConstant N lo ap ap)^2*geometryDCompensator bin)*Z^(B*ε)/_
    apply div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
      (geometryDCompensator_pos bin).le
  · have hh:=actual_geometry_right_mass_compensation s R seed (Z^D) Z ξ D
      (Real.logb Z (volume s.toData)) B ε hK hZ hε hs hz₁ hz₂ hsource bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z ξ q)) j
    simpa only [geometryFirstHighMass,geometryHighSide,geometryHighFactor,ite_true,div_eq_mul_inv,
      mul_assoc,mul_left_comm,mul_comm] using hh

omit [DecidableEq α] in
lemma actual_geometry_high_side_identity (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)
    (hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (reflected : Bool)(A : ℝ) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d:=Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let r:=Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let e:=Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)=
      p+A-c+r+e+max (3*c-5*d-r) 0/6+geometrySurplus (geometryExponents s R seed K Z ξ j.1.val) := by
  intro l c d r e p
  have he : Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}=firstProjectorRadical l.1.1 l.1.2 l.2.val := by
    rw [primeSubsetGenerator,span_idealGenerator]
    rfl
  change Ideal.span {primeSubsetGenerator
    (fun P : CommonIndex j.1.val.1.val.1 j.1.val.1.val.2=>P.val) j.1.val.2.1.val}=_ at he
  cases reflected <;>
    dsimp [geometryHighSide,leftExponent,rightExponent,geometryExponents,geometryNorms,
      geometryIdeals,c,d,r,e,p,l,geometryFirstLabel] <;> rw [he] <;> rfl

omit [DecidableEq α] in
/-- The surplus of the geometry coordinates is the surplus of the label in either orientation. -/
lemma actual_geometry_surplus_eq (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)
    (hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) (reflected : Bool) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d:=Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let r:=Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    geometrySurplus (geometryExponents s R seed K Z ξ j.1.val)=ValuationCone.surplus c d p r := by
  intro l c d r p
  cases reflected <;>
    dsimp [geometrySurplus,ValuationCone.surplus,geometryExponents,geometryNorms,
      geometryIdeals,c,d,r,p,l,geometryFirstLabel]
  ring

/-- The missing-radical coordinate of the compensated HIGH coordinates is exact. -/
theorem actual_geometry_compensated_high_missing
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv : ℝ)(hZ : 1<Z) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    ((firstSourceMissing left l).absNorm:ℝ)=Z^(x 1) := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z ξ hK bin j.1).hD
  simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
    ite_false,add_zero] using actual_child_high_missing reflected left second l hC hD d₂.C d₂.D U
      Z D A a ξ reserve ε εv hZ

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The literal first scalar in the finite-bin transport: the energy weighted by the first mass is at most the support
factor times the binned count form of the compensated coordinates. The rows of a bin are counted by the caller. -/
theorem actual_geometry_paid_binned_high_transport {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,coeff l≤Z^(x l 0)) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤ s.lower →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l)),
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R₂ : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R₂ l*E l)) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*x l 3+rawError) →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
        binnedCount labels (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected
          (Real.logb Z (volume s.toData)) (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
          (fun key=>C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
            Z^(exponentBinUpper width key 0+(2*a-1)*exponentBinUpper width key 3+rawError+allowance))  := by
  obtain ⟨bound,hbound,hbinned⟩ := actual_geometry_binned_high_transport
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ ε hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hbinned P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed W D ξ hK bin column datum first row hfirst
    left unit hf rawKey key a rawError allowance Kcontrol T width i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hcoeff hseed hz₁ hz₂ hsource hlower
    st hQM hQη z hz hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hZ : 1<Z := by linarith [he.1]
  have hzpos : 0<Z := zero_lt_one.trans hZ
  let side := fun l=>geometryHighSide reflected (Real.logb Z (volume s.toData))
    (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let scale := factor*Z^(B*εmass)
  let mass := fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)
  let xc := fun l=>compensatedHighCoordinates (x l) (side l)
  let cc := fun l=>mass l*coeff l/scale
  have hfactor : 0<factor := geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have hscale : 0<scale := mul_pos hfactor (Real.rpow_pos_of_pos hzpos _)
  have hcc (l : κ)(hl : l∈labels) : cc l≤Z^(xc l 0) := by
    apply (div_le_iff₀ hscale).mpr
    have hs₁ (u : ℝ)(hu : s.W₁ u≠0) : ap≤u := by
      have hw : ((p l).profile 0) u≠0 := by
        simpa only [←(hW l hl).1] using hu
      exact ((p l).support 0 hw).1
    have hs₂ (u : ℝ)(hu : s.W₂ u≠0) : ap≤u := by
      have hw : ((p l).profile 1) u≠0 := by
        simpa only [←(hW l hl).2.1] using hu
      exact ((p l).support 1 hw).1
    have hm:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z ξ B εmass
      hZ hK hεmass hcard hlower hseed hz₁ hz₂ hsource hs₁ hs₂ bin (column l)
    have hh:=compensated_high_coefficient Z (mass l) (coeff l) factor (B*εmass) (side l) (x l)
      hzpos (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l)) hm
      (hcoeff l hl)
    simpa only [scale,xc,mul_comm] using hh
  have hj:=he.2 reflected second s R seed (Z^D) ξ hK bin column datum first row hfirst
    a rawError allowance Kcontrol T width i ha ha' hKcontrol hT hwidthbin hinj
    labels xc cc hcc st hQM hQη z hz
    hi hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (3:Fin 4)≠0 by decide,ite_false,add_zero] using hledger)
  have hh:=mul_le_mul_of_nonneg_left hj hscale.le
  calc
    _=scale*(∑l∈labels,cc l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
      retainedAllocationCost (src l) L alloc (z l))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp only [cc,mass]
      field_simp [ne_of_gt hscale]
    _≤_ := hh

/-- The level-1 payment of the binned count form. With the level-1 count of each bin of the compensated
coordinates, the binned count is at most the number of bins times one paid exponential. The constants of the count
are fixed before `Z`. -/
theorem actual_geometry_high_transport_payment {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hloss : 0<loss) :
    ∃J : ℕ,∃Ccount : ℝ,0<Ccount ∧ ∀Z : ℝ,2≤Z → ∀Bmask bΦ : ℝ,
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀(a C₀ rawError allowance width Bbox target reserve T' : ℝ),
      ((1+Cycle63.Arithmetic.q0)/2) ≤ a → a ≤ 7/8 → 0 ≤ C₀ → 0<width → 0 ≤ T' →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→Fin 4→ℝ),
      (∀l∈labels,∀j,-Bbox≤x l j ∧ x l j≤Bbox) →
      (∀l∈labels,x l 2+width≤Q) →
      (∀l∈labels,highExponentValue (2*a-1) (x l)≤
        geometryHighSide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s R seed K Z ξ (column l).1.val)+target-reserve) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      |Real.logb Z (volume s.toData)|≤B →
      ∀ st : κ → NaturalState Z Bmask bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^(x l 2) ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          T') →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^(x l 1)) →
      binnedCount labels (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected
          (Real.logb Z (volume s.toData)) (geometryExponents s R seed K Z ξ (column l).1.val))) width
          (fun key=>C₀*Z^(exponentBinUpper width key 0+(2*a-1)*exponentBinUpper width key 3+rawError+allowance))≤
        ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
          (C₀*(Ccount*(1+T')^J)*Z^(target-reserve+4*width+loss+(rawError+allowance))) := by
  obtain ⟨J,Ccount,hCcount,hlabels⟩ := actual_geometry_high_label_count
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss hB hQ hQB hloss
  refine ⟨J,Ccount,hCcount,?_⟩
  intro Z hZ2 Bmask bΦ κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent
    hfirst hR ψ left unit hf rawKey key a C₀ rawError allowance width Bbox target reserve T' ha ha' hC₀ hwidthbin hT'
    hinj labels x hx hq hpoint hseed hz₁ hz₂ hsource hAbox st hQM hQη z hz hchar hpuncture hrow
    hzero hsupport hnorm hmissing
  have hZ : 1<Z := by linarith
  have hδ : Cycle63.Arithmetic.q0≤2*a-1 ∧ 2*a-1≤3/4 := by
    constructor <;> linarith [Cycle63.Arithmetic.q0_bounds.1, Cycle63.Arithmetic.q0_bounds.2]
  have ha4 : 4/5≤a := by linarith [Cycle63.Arithmetic.q0_bounds.1]
  let side := fun l=>geometryHighSide reflected (Real.logb Z (volume s.toData))
    (geometryExponents s R seed K Z ξ (column l).1.val)
  let xc := fun l=>compensatedHighCoordinates (x l) (side l)
  have hsbox (l : κ) : |side l|≤5*B := by
    apply geometry_high_side_box reflected _ B _ hB hAbox
    intro j
    have hn:=actual_geometry_norm_caps s R seed K Z ξ B hseed hz₁ hz₂ hsource (column l).1.val j
    exact ⟨Real.logb_nonneg hZ hn.1,(Real.logb_le_iff_le_rpow hZ
      (zero_lt_one.trans_le hn.1)).mpr hn.2⟩
  have hxc (l : κ)(hl : l∈labels) : ∀j,-(Bbox+5*B)≤xc l j ∧ xc l j≤Bbox+5*B :=
    compensated_high_coordinate_box (x l) (side l) Bbox (5*B) (hx l hl) (hsbox l)
  have hp (l : κ)(hl : l∈labels) : highExponentValue (2*a-1) (xc l)≤target-reserve := by
    rw [compensated_high_exponent]
    have hh:=hpoint l hl
    change highExponentValue (2*a-1) (x l)≤ side l+target-reserve at hh
    linarith
  have hxc1 (l : κ) : xc l 1=x l 1 := by
    simp only [xc,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,ite_false,add_zero]
  have hxc2 (l : κ) : xc l 2=x l 2 := by
    simp only [xc,compensatedHighCoordinates,childHighCoordinates,show (2:Fin 4)≠0 by decide,ite_false,add_zero]
  have hcount : ∀key∈labels.image (fun l=>exponentBin width (xc l)),
      ((labels.filter (fun l=>exponentBin width (xc l)=key)).card:ℝ)≤
        (Ccount*(1+T')^J)*
          Z^(exponentBinUpper width key 1+exponentBinUpper width key 2*unmarkedDensity (2*a-1)+loss) := by
    intro key hkey
    let rows := labels.filter (fun l=>exponentBin width (xc l)=key)
    have hrow' (l : κ)(hl : l∈rows) : l∈labels := (Finset.mem_filter.mp hl).1
    have hround (l : κ)(hl : l∈rows)(j : Fin 4) :
        xc l j≤exponentBinUpper width key j ∧ exponentBinUpper width key j≤xc l j+width := by
      have hh:=exponent_bin_enclosure width hwidthbin (xc l) j
      rw [(Finset.mem_filter.mp hl).2] at hh
      exact hh
    obtain ⟨l₀,hl₀,hk₀⟩ := Finset.mem_image.mp hkey
    have hl₀' : l₀∈rows := Finset.mem_filter.mpr ⟨hl₀,hk₀⟩
    have hq' : exponentBinUpper width key 2≤Q := by
      have h1 := (hround l₀ hl₀' 2).2
      have h2 := hq l₀ hl₀
      rw [hxc2] at h1
      linarith
    exact hlabels Z hZ2 Bmask bΦ reflected second s hη R seed K ξ hK bin column datum first row
      hparent hfirst hR ψ (exponentBinUpper width key 2) (exponentBinUpper width key 1) a T'
      hq' ha4 ha' hT' hinj rows st hQM hQη z hz hchar hpuncture hrow
      (fun l hl=>⟨(hzero l (hrow' l hl)).1.trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by rw [← hxc2 l]; exact (hround l hl 2).1)),
        (hzero l (hrow' l hl)).2⟩)
      (fun l hl=>hsupport l (hrow' l hl)) (fun l hl=>hnorm l (hrow' l hl))
      (fun l hl=>(hmissing l (hrow' l hl)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (by rw [← hxc1 l]; exact (hround l hl 1).1)))
  exact binned_count_payment labels xc width
    (fun key=>C₀*Z^(exponentBinUpper width key 0+(2*a-1)*exponentBinUpper width key 3+rawError+allowance))
    (Bbox+5*B) (2*a-1) Z C₀ (Ccount*(1+T')^J)
    target reserve loss (rawError+allowance) hwidthbin hZ.le hC₀ (by positivity) hδ hxc hp
    (fun key=>le_of_eq (by ring_nf)) hcount

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
