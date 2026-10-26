/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B084
import Candidate.Bundles.B104
import Candidate.Bundles.B110
import Candidate.Bundles.B116
import Candidate.Bundles.B134
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinLabels

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighPayment; sha256 644a0ec57d74132c4e91c6bce9c15119037df445f53697780b944714faedc0a8 -/
section
                                                    
                                                           
                                                         

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

def geometryHighSide (reflected : Bool)(A : ℝ)(x : Fin 5→ℝ) : ℝ :=
  if reflected then rightExponent A x else leftExponent A x

def geometryHighFactor (reflected : Bool)(C₀ : ℝ)(bin : ℤ×(Fin 5→ℤ)) : ℝ :=
  if reflected then (geometryDCompensator bin)⁻¹ else 2*C₀^2*geometryDCompensator bin

lemma geometry_high_factor_pos (reflected : Bool)(C₀ : ℝ)(bin : ℤ×(Fin 5→ℤ))
    (hC : 0< C₀) : 0< geometryHighFactor reflected C₀ bin := by
  cases reflected <;> simp only [geometryHighFactor,Bool.false_eq_true,ite_false,ite_true]
  · exact mul_pos (by positivity) (geometryDCompensator_pos bin)
  · exact inv_pos.mpr (geometryDCompensator_pos bin)

lemma geometry_high_side_box (reflected : Bool)(A B : ℝ)(x : Fin 5→ℝ)
    (hB : 0≤ B)(hA : |A|≤ B)(hx : ∀j,0≤ x j ∧ x j≤ B) :
    |geometryHighSide reflected A x|≤5*B := by
  have ha:=abs_le.mp hA
  have hm (i j : Fin 5) : 0≤ max (3*x i-5*x j-x 3) 0 ∧
      max (3*x i-5*x j-x 3) 0≤3*B := by
    refine ⟨le_max_right _ _,max_le ?_ (by linarith)⟩
    linarith [(hx i).2,(hx j).1,(hx 3).1]
  apply abs_le.mpr
  cases reflected <;> simp only [geometryHighSide,Bool.false_eq_true,ite_false,ite_true]
  · dsimp only [leftExponent]
    constructor <;> linarith [(hx 0).1,(hx 0).2,(hx 2).1,(hx 2).2,
      (hx 3).1,(hx 3).2,(hx 4).1,(hx 4).2,(hm 0 1).1,(hm 0 1).2]
  · dsimp only [rightExponent]
    constructor <;> linarith [(hx 1).1,(hx 1).2,(hx 2).1,(hx 2).2,
      (hx 3).1,(hx 3).2,(hx 4).1,(hx 4).2,(hm 1 0).1,(hm 1 0).2]

variable {α : Type} [Fintype α] [DecidableEq α]

def geometryFirstHighMass (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin)) : ℝ :=
  ‖geometryColumnScalar reflected s R seed (Z^D) Z ξ D (Real.logb Z (volume s.toData))
    hK bin (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z ξ q)) j‖^2*
    ((geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin j).absNorm:ℝ)^(ε-1)

omit [DecidableEq α] in
lemma geometry_first_high_mass_nonneg (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin)) :
    0≤ geometryFirstHighMass reflected s R seed W D Z ξ ε hK bin j := by
  unfold geometryFirstHighMass
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The support constant is fixed before the source and first label move. -/
theorem actual_geometry_uniform_high_mass (reflected : Bool)(N : ℕ)(lo ap : ℝ)
    (hlo : 0< lo)(hap : 0< ap)(s : Input α)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ B ε : ℝ)(hZ : 1< Z)(hK : 0< Z^D)
    (hε : 0≤ε)(hcard : Fintype.card α≤ N)(hlower : lo≤ s.lower)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
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
    (hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (reflected : Bool)(A : ℝ) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d:=Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let r:=Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let e:=Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)=
      p+A-c+r+e+max (3*c-5*d-r) 0/6 := by
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

/-- Actual geometry supplies the side cancellation and a uniform box after
normalization. The target contains no first-label norm exponent. -/
theorem actual_geometry_compensated_high_gates
    (s : Input α)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (D A a reserve ε εv B b δ : ℝ)(hZ : 1< Z)(hB : 0≤ B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)
    (hsecond : (d₂.C.absNorm:ℝ)≤ Z^B ∧ (d₂.D.absNorm:ℝ)≤ Z^B)
    (hDbox : |D|≤ B)(hAbox : |A|≤ B)(habox : |a|≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤ B)(hε : |ε|≤ B)
    (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4)(hD : 0≤ D)
    (hA : A≤ D*Cycle61.Arithmetic.totalA b)(ha : a≤ D*Cycle61.Arithmetic.amp b) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    let side:=geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected left second l d₂.C d₂.D U Z D A a ξ reserve ε) εv) side
    ((firstSourceMissing left l).absNorm:ℝ)=Z^(x 1) ∧
      (∀k,-(37*B+|εv|)≤ x k ∧ x k≤37*B+|εv|) ∧
      highExponentValue δ x≤
        (1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+unmarkedDensity δ*ε+εv-
          D*(720486667/30493190000000) := by
  intro l side x
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val
  have hf : (l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B := ⟨(hn 0).2,(hn 1).2⟩
  have hg:=actual_geometry_high_coordinate_gates s R seed K Z ξ hK bin j d₂ reflected left second U
    D A a reserve ε εv B b δ hZ hB hf hsecond hDbox hAbox habox hω hε hb hδ hD hA ha
  have hside : |side|≤5*B := by
    apply geometry_high_side_box reflected A B _ hB hAbox
    intro k
    exact ⟨Real.logb_nonneg hZ (hn k).1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (hn k).1)).mpr (hn k).2⟩
  refine ⟨?_,?_,?_⟩
  · simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
      ite_false,add_zero] using hg.1
  · have hh:=compensated_high_coordinate_box _ side (32*B+|εv|) (5*B) hg.2.1 hside
    intro k
    simpa only [show 32*B+|εv|+5*B=37*B+|εv| by ring] using hh k
  · rw [compensated_high_exponent]
    have he:=actual_geometry_high_side_identity s R seed K Z ξ hK bin j reflected A
    change side=_ at he
    dsimp only at hg
    rw [←he] at hg
    linarith [hg.2.2]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The literal first scalar is paid inside the joint finite-bin density.
Only fixed support, physical-D and bin-count factors occur outside the sum. -/
theorem actual_geometry_paid_binned_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width Bbox target reserve : ℝ) (i : ℕ),
      21/25 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→ Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,∀j,-Bbox≤ x l j ∧ x l j≤ Bbox) →
      (∀l∈labels,x l 2+width≤ Q) →
      (∀l∈labels,coeff l≤ Z^(x l 0)) →
      (∀l∈labels,highExponentValue (2*a-1) (x l)≤
        geometryHighSide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)+target-reserve) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s.toData)|≤ B → lo≤ s.lower →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
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
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^(x l 1)) →
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R₂ : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap Araw : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      Real.logb Z (preVolume s.toData)≤ Araw → pad≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R₂ l*E l)) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*x l 3+rawError) →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(Bbox+5*B)/width⌋:ℤ) ⌊(Bbox+5*B)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-reserve+4*width+loss+rawError+allowance+B*εmass)) := by
  obtain ⟨bound,hbound,J,hbinned⟩ := actual_geometry_binned_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hbinned P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key a rawError allowance Kcontrol T width Bbox target reserve i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hx hq hcoeff hpoint hseed hz₁ hz₂ hsource hAbox hlower
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hZ : 1< Z := by linarith [he.1]
  have hzpos : 0< Z := zero_lt_one.trans hZ
  let side := fun l=>geometryHighSide reflected (Real.logb Z (volume s.toData))
    (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let scale := factor*Z^(B*εmass)
  let mass := fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)
  let xc := fun l=>compensatedHighCoordinates (x l) (side l)
  let cc := fun l=>mass l*coeff l/scale
  have hfactor : 0< factor := geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have hscale : 0< scale := mul_pos hfactor (Real.rpow_pos_of_pos hzpos _)
  have hsbox (l : κ) : |side l|≤5*B := by
    apply geometry_high_side_box reflected _ B _ hB hAbox
    intro j
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val j
    exact ⟨Real.logb_nonneg hZ hn.1,(Real.logb_le_iff_le_rpow hZ
      (zero_lt_one.trans_le hn.1)).mpr hn.2⟩
  have hcc (l : κ)(hl : l∈labels) : cc l≤ Z^(xc l 0) := by
    apply (div_le_iff₀ hscale).mpr
    have hs₁ (u : ℝ)(hu : s.W₁ u≠0) : ap≤ u := by
      have hw : ((p l).profile 0) u≠0 := by
        simpa only [←(hW l hl).1] using hu
      exact ((p l).support 0 hw).1
    have hs₂ (u : ℝ)(hu : s.W₂ u≠0) : ap≤ u := by
      have hw : ((p l).profile 1) u≠0 := by
        simpa only [←(hW l hl).2.1] using hu
      exact ((p l).support 1 hw).1
    have hm:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z ξ B εmass
      hZ hK hεmass hcard hlower hseed hz₁ hz₂ hsource hs₁ hs₂ bin (column l)
    have hh:=compensated_high_coefficient Z (mass l) (coeff l) factor (B*εmass) (side l) (x l)
      hzpos (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l)) hm
      (hcoeff l hl)
    simpa only [scale,xc,mul_comm] using hh
  have hxc (l : κ)(hl : l∈labels) : ∀j,-(Bbox+5*B)≤ xc l j ∧ xc l j≤ Bbox+5*B :=
    compensated_high_coordinate_box (x l) (side l) Bbox (5*B) (hx l hl) (hsbox l)
  have hp (l : κ)(hl : l∈labels) : highExponentValue (2*a-1) (xc l)≤ target-reserve := by
    rw [compensated_high_exponent]
    have hh:=hpoint l hl
    change highExponentValue (2*a-1) (x l)≤ side l+target-reserve at hh
    linarith
  have hj:=he.2 reflected second s hη R seed (Z^D) ξ hK bin column datum first row hparent hfirst hR ψ
    a rawError allowance Kcontrol T width (Bbox+5*B) target reserve i ha ha' hKcontrol hT hwidthbin hinj
    labels xc cc hxc (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (2:Fin 4)≠0 by decide,ite_false,add_zero] using hq) hcc hp
    st hQM hQη z hz hchar hpuncture hrow
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (2:Fin 4)≠0 by decide,ite_false,add_zero] using hzero)
    hsupport hnorm
    (by simpa only [xc,compensatedHighCoordinates,childHighCoordinates,
      show (1:Fin 4)≠0 by decide,ite_false,add_zero] using hmissing)
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
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [cc,mass]
      field_simp [ne_of_gt hscale]
    _≤ _ := hh
    _=_ := by
      dsimp only [scale,factor]
      conv_rhs => rw [Real.rpow_add hzpos]
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_uniform_high_mass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_side_identity
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_compensated_high_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_paid_binned_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.FirstLowLabelCount; sha256 7ebc2a95d372e8993ffdb3c86a83c6ff5f9e4654266b71bf7c8776c7fb542621 -/
section
                                         
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentRankinLabels
open Cycle61Moment
local notation "O" => HeckeFamily.O

def firstPartitionCode (l : FirstSourceLabel) : (Ideal O×Ideal O)×Finset (Ideal O) :=
  (l.1,l.2.val.image Subtype.val)

theorem first_partition_code_injective : Function.Injective firstPartitionCode := by
  rintro ⟨CD,E⟩ ⟨CD',F⟩ h
  have hCD : CD=CD' := congrArg Prod.fst h
  cases hCD
  have hEF : E.val=F.val := Finset.image_injective Subtype.val_injective (congrArg Prod.snd h)
  have he : E=F := Subtype.ext hEF
  cases he
  rfl

/-- The low branch may count first labels explicitly. The inactive subset
is included, arbitrary valuations are allowed, and the old seed is saved. -/
theorem actual_first_low_label_count (B ε : ℝ)(hB : 0≤ B)(hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀p : ℝ,p≤ B →
      ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (labels.card:ℝ)≤ K*Z^(p+ε)/(seed.absNorm:ℝ) := by
  let e := ε/(3*B+1)
  have he : 0< e := div_pos hε (by positivity)
  obtain ⟨K,hK,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨K,hK,?_⟩
  intro Z hZ p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hz := zero_lt_one.trans_le hZ
  have hpart (l : FirstSourceLabel) :
      (firstPartitionCode l).2⊆IdealMobiusDivisorSum.primeSupport (commonRadical l.1.1 l.1.2) := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [commonRadical_support]
    exact Q.property
  have hh := hcount seed hs hs0 (labels.image firstPartitionCode)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact ⟨(hsup l hl).1.1,(hsup l hl).2.1⟩)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact heq l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hseed l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hpart l)
    (Z^B) (Z^B) (Z^p) (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _)
    (Real.rpow_pos_of_pos hz _)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hnorm l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hrad l hl)
  rw [Finset.card_image_of_injective _ first_partition_code_injective] at hh
  have hexp : B*e+B*e+p*(1+e)≤ p+ε := by
    have hid : e*(3*B+1)=ε := by dsimp only [e];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hp he.le]
  calc
    _≤ K*(Z^B)^e*(Z^B)^e*(Z^p)^(1+e)/(seed.absNorm:ℝ) := hh
    _=K*Z^(B*e+B*e+p*(1+e))/(seed.absNorm:ℝ) := by
      simp only [←Real.rpow_mul hz.le,Real.rpow_add hz]
      ring
    _≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) hK.le)
      (Nat.cast_nonneg _)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_partition_code_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_low_label_count

end
/- END ORIGINAL Cycle61.Physical.InitialMass.FirstLowLabelCount -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryColumnFibres; sha256 b2a48e433a85a18431c254338544ae18abaed6dd62b6ecd97d114f62235c1287 -/
section
                                                      
                                           

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O

/-- The first dyads and ray choices may be selected at each arithmetic
label/projector pair for a uniform small-power cost. The projector remains
in the selected family for its later joint-frequency divisor bound. -/
theorem actual_first_selected_column_budget_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D B ξ ε : ℝ) (hA : 0≤ A) (hD : 0≤ D) (hB : 0≤ B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ)),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^A → K⁻¹≤ Z^D →
      ∀{κ : Type*}(column : κ→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)),
      Function.Injective column → ∀(rows : Finset κ)
        (cost : rows→ℝ)(E : ℝ),(∀r,0≤ cost r) →
      let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key (column r.val),(column r.val).2.1.val)
      (∀pick : (j : Finset.univ.image code)→ ↥rows,
        (∀j,code (pick j)=j.val) → (∑j : Finset.univ.image code,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(C*Z^ε)*E := by
  have hL : 0≤3*max A D+ξ/2 := by positivity
  obtain ⟨C,hC,hdyad⟩ := source_dyadic_envelope_subpower B (3*max A D+ξ/2) ε hB hL hε
  have hray : (0:ℝ)< Fintype.card RayCharacter := by exact_mod_cast Fintype.card_pos
  refine ⟨C*(Fintype.card RayCharacter:ℝ)^2,by positivity,?_⟩
  filter_upwards [hdyad,eventually_ge_atTop (1:ℝ)] with Z hdyad hZ
  refine ⟨hZ,?_⟩
  intro s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi κ column hinj rows cost E hc
  dsimp only
  intro hjoint
  let N : Finset (Fin 4→ℤ) := Fintype.piFinset (fun i=>
    indices (![K/Z^(2*B),1,1,1] i) (![K,Z^(3*max A D+ξ/2),Z^B,Z^B] i))
  have hN : (N.card:ℝ)≤ C*Z^ε := by
    have hh := hdyad K hK
    simpa only [N,SourceDyadicEnvelope,Fintype.card_piFinset,Fintype.card_pi,Fintype.card_coe] using hh
  let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key (column r.val),(column r.val).2.1.val)
  apply joint_fiber_selection code cost ((C*(Fintype.card RayCharacter:ℝ)^2)*Z^ε) E
    (by positivity) hc _ hjoint
  intro j hj
  let fiber := Finset.univ.filter (fun r : rows=>code r=j)
  let target := N ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ (Finset.univ : Finset RayCharacter))
  have hcard : fiber.card≤ target.card := Finset.card_le_card_of_injOn
    (fun r : rows=>((fun i=>((column r.val).1.val.2.2 i:ℤ)),(column r.val).2.2.1,(column r.val).2.2.2))
    (by
      intro r hr
      refine Finset.mem_product.mpr ⟨?_,by simp⟩
      exact Fintype.mem_piFinset.mpr (actual_dyads_in_envelope s R seed K Z ξ A D B
        hK hZ hB hA hD hξ hseed hz₁ hz₂ hsource hsourcecap hV hKi (column r.val).1.val))
    (by
      intro r hr t ht he
      apply Subtype.ext
      apply hinj
      apply geometry_first_column_code_injective s R seed K Z ξ hK key
      have hcode : code r=code t := (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm
      exact congrArg₂ (fun (x : FirstSourceLabel×Ideal O) (y : (Fin 4→ℤ)×RayCharacter×RayCharacter)=>
        (x.1,x.2,y)) hcode he)
  have hcard' : (fiber.card:ℝ)≤ N.card*(Fintype.card RayCharacter:ℝ)^2 := by
    have hh : target.card=N.card*(Fintype.card RayCharacter)^2 := by
      simp only [target,Finset.card_product,Finset.card_univ,pow_two]
    rw [hh] at hcard
    exact_mod_cast hcard
  exact hcard'.trans ((mul_le_mul_of_nonneg_right hN (sq_nonneg _)).trans_eq (by ring))


/-- Specialization to the original column type. -/
theorem actual_first_selected_column_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D B ξ ε : ℝ) (hA : 0≤ A) (hD : 0≤ D) (hB : 0≤ B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ)(hK : 0< K)(key : ℤ×(Fin 5→ℤ)),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^A → K⁻¹≤ Z^D →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (cost : rows→ℝ)(E : ℝ),(∀r,0≤ cost r) →
      let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key r.val,r.val.2.1.val)
      (∀pick : (j : Finset.univ.image code)→ ↥rows,
        (∀j,code (pick j)=j.val) → (∑j : Finset.univ.image code,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(C*Z^ε)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    A D B ξ ε hA hD hB hξ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi rows cost E hc code hjoint
  exact hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
    id Function.injective_id rows cost E hc hjoint

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_selected_column_budget

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_selected_column_budget_indexed

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryColumnFibres -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAmplification; sha256 a78a12ef82a0727a9af90229ca391e740e17f0a57425c51023b077514dce2863 -/
section
                                                     

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryAmplificationDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def geometryAllocationWeight (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) : ℝ :=
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key j
  if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
    ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
      ((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(frozenControl B.val s.M)^2
  else 0

omit [DecidableEq ι] in
lemma geometryAllocationWeight_nonneg (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    0≤ geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  unfold geometryAllocationWeight
  dsimp only
  split_ifs <;> positivity

omit [DecidableEq ι] in
/-- Exact allocation sum underlying the first-source budget. Zero frozen
coefficients remain zero weights, before applying amplification. -/
theorem geometryLiveBudget_eq_allocations (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b t : ℝ) :
    geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t=
    ∑j : firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
        geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
          childNormalizedGaussSource s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val)
            R j.val.2.1.val B (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val)
              t CenteredMomentFirstAnnularMajorant.profile
              (geometryFirstSource s R seed K Z ξ hK key j.val.1).H0 := by
  rw [Finset.sum_coe_sort _ (fun j=>
    ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j),
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*
        childNormalizedGaussSource s (geometryColumnIdeal reflected s R seed K Z ξ hK key j)
          R j.2.1.val B (geometryColumnCharacter reflected s R seed K Z ξ hK key j)
            t CenteredMomentFirstAnnularMajorant.profile
            (geometryFirstSource s R seed K Z ξ hK key j.1).H0)]
  dsimp only [geometryLiveBudget]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  unfold geometryAllocationWeight
  dsimp only
  split_ifs <;> ring


omit [DecidableEq ι] in
/-- Amplification of the literal, unreflected or reflected first-source
budget. All first columns and common allocations stay in the same sum. -/
theorem actual_geometry_budget_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Amax D ξcap Bcap b eta ξ reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hcap : 0≤ amplifierCap Amax D ξcap)
    (hb : 0≤ b) (hgap : eta< sigma/6) (hξ : 0≤ξ) (hξcap : ξ≤ξcap)
    (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀(reflected : Bool) (s : Input ι) (R seed : Ideal O) (K M A : ℝ) (hK : 0< K)
      (key : ℤ×(Fin 5→ℤ))
      (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (t : ℝ),
      CenteredMomentExceptionalAmplitudePair.volume s.toData≤ Z^Amax → K⁻¹≤ Z^D →
      R≠0 → (R.absNorm:ℝ)≤ Z^BR → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      sourceRadius s≤ Z^Bcap →
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤ Z^Bs) →
      (∀i,Function.support (s.W i)⊆Set.Iic b) →
    ∀z : ι→ℝ, (∀i,z i≤ eta) → (∀i,s.P i=Z^(z i)) →
    let Label := ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus));
    let C (j : Label) := geometryColumnIdeal reflected s R seed K Z ξ hK key j.val;
    let χ (j : Label) := geometryColumnCharacter reflected s R seed K Z ξ hK key j.val;
    let g (j : Label) := geometryBranch reflected s R seed K Z ξ hK key j.val;
    let w (j : Label) := geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val;
    ∃τ : (j : Label)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
      (∀j B p i ψ,(τ j B p i ψ).modulus.absNorm≤
        radicalBound (childCharacter (χ j) ψ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t ≤
      (56/(P.card:ℝ))*
        (((amplifierCap Amax D ξcap+2*sigma)/(sigma/6))*
          (∑j,∑B,w j B*actualMainSource (child s (C j) R B (χ j) t)
            (g j) Z sigma 1 ξ reserve)+
          ∑j,∑B,w j B*actualErrorSources (child s (C j) R B (χ j) t)
            (g j) Z sigma 1 ξ reserve P (τ j B)) := by
  filter_upwards [eventually_ge_atTop (32:ℝ),
    actual_common_children_amplification (ι:=ι) rayM H hH Sbad hbad
      sigma loss (BR+Bcap) Bs (amplifierCap Amax D ξcap) b eta 1 ξ reserve
      hsigma hloss hcap hb hgap le_rfl hξ hreserve] with Z hZ hz
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_⟩
  intro reflected s R seed K M A hK key weight N t hV hKi hR hRn hs hz₁ hz₂
    hsource hpool hsupp z hzslot hlen Label C χ g w
  obtain ⟨τ,hτ,he⟩ := hz.2.2.2 s R C g χ (fun _=>t) w
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    (fun _=>rfl)
    (fun j=>actual_geometry_admission reflected s R seed K Z ξ Amax D ξcap Bcap BR Bs hK hZ
      hξcap hV hKi hR hRn hs hz₁ hz₂ hsource hpool key j.val)
    hsupp z hzslot hlen
  refine ⟨τ,hτ,?_⟩
  rw [geometryLiveBudget_eq_allocations]
  exact he

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryLiveBudget_eq_allocations

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_budget_amplification

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAmplification -/
