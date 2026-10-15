/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B133

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryScalarCompensation; sha256 6bc35b2b1509bd5b919be80711f6f79965c944a93ec3a925e2cb3ef5bf638d7a -/
section
                                                 

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSourceReduction CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- Physical D, including on the reflected side. This is fixed by the
original geometry bin before any Mellin height or allocation is selected. -/
def geometryDCompensator (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  (2:ℝ)^((key.2 1):ℝ)

lemma geometryDCompensator_pos (key : ℤ×(Fin 5→ℤ)) :
    0< geometryDCompensator key := Real.rpow_pos_of_pos (by norm_num) _

variable {ι : Type*} [Fintype ι]

/-- Literal physical D lies in the frozen dyadic interval. -/
theorem actual_geometry_D_compensation (s : Input ι)(R seed : Ideal O)(K Z ξ B : ℝ)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    geometryDCompensator key≤(q.val.1.val.2.absNorm:ℝ) ∧
      (q.val.1.val.2.absNorm:ℝ)<2*geometryDCompensator key := by
  have hn := (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val 1).1
  have hn' : 0< geometryNorms s R seed K Z ξ q.val 1 := zero_lt_one.trans_le hn
  have hi := congrFun (congrArg Prod.snd q.property) (1 : Fin 5)
  change ⌊Real.logb 2 (geometryNorms s R seed K Z ξ q.val 1)⌋=key.2 1 at hi
  have hlo := Int.floor_le (Real.logb 2 (geometryNorms s R seed K Z ξ q.val 1))
  have hhi := Int.lt_floor_add_one (Real.logb 2 (geometryNorms s R seed K Z ξ q.val 1))
  rw [hi] at hlo hhi
  have hpow := Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1) hn'
  have hl := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hlo
  have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hhi
  rw [hpow] at hl hh
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one] at hh
  constructor
  · exact hl
  · simpa [geometryDCompensator,geometryNorms,geometryIdeals,mul_comm] using hh

lemma scalar_left_compensation (Z S n d H C ε B : ℝ)
    (hZ : 1≤ Z)(hn : 0< n)(hd : 0≤ d)(hH : d≤2*H)
    (hε : 0≤ε)(hcap : n≤ Z^B) :
    (C^2*n*d/Z^S)*n^(ε-1)≤(2*C^2*H)*Z^(B*ε)/Z^S := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hnε : n*n^(ε-1)=n^ε := by
    calc
      _=n^(1:ℝ)*n^(ε-1) := by rw [Real.rpow_one]
      _=n^ε := by rw [←Real.rpow_add hn]; congr 1; ring
  have hp : n^ε≤ Z^(B*ε) := by
    rw [Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow hn.le hcap hε
  have hc : 0≤ C^2*d := mul_nonneg (sq_nonneg _) hd
  calc
    _=(C^2*d)*n^ε/Z^S := by rw [←hnε]; ring
    _≤(C^2*d)*Z^(B*ε)/Z^S := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hc) (Real.rpow_nonneg hz.le _)
    _≤ _ := by
      have hcD : C^2*d≤2*C^2*H := by nlinarith [mul_le_mul_of_nonneg_left hH (sq_nonneg C)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcD (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)

lemma scalar_right_compensation (Z S d H ε B : ℝ)
    (hZ : 1≤ Z)(hH : 0< H)(hd : H≤ d)
    (hε : 0≤ε)(hcap : d≤ Z^B) :
    (1/Z^S)*d^(ε-1)≤(Z^(B*ε)/Z^S)/H := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hdpos : 0< d := hH.trans_le hd
  have hp : d^ε≤ Z^(B*ε) := by
    rw [Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow hdpos.le hcap hε
  rw [Real.rpow_sub hdpos,Real.rpow_one]
  calc
    _=(d^ε/Z^S)/d := by ring
    _≤(Z^(B*ε)/Z^S)/d := by gcongr
    _≤ _ := div_le_div_of_nonneg_left (by positivity) hH hd


/-- The actual left allocation mass retains only the frozen physical-D
factor and a small power; its entire side exponent remains in the denominator. -/
theorem actual_geometry_left_mass_compensation [DecidableEq ι]
    (s : Input ι)(R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(M Z ξ B ε : ℝ)(hZ : 1< Z)
    (hε : 0≤ε)(hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)
    (a₁ a₂ : ℝ)(ha₁ : 0< a₁)(ha₂ : 0< a₂)
    (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x)(hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)) :
    let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
    ‖geometryColumnScalar false s R seed (Z^M) Z ξ M (Real.logb Z (volume s.toData))
      hK key (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) j‖^2*
      ((geometryColumnIdeal false s R seed (Z^M) Z ξ hK key j).absNorm:ℝ)^(ε-1)≤
      (2*(4/((∏i,s.lo i)*a₁*a₂))^2*geometryDCompensator key)*Z^(B*ε)/
        Z^(leftExponent (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^M) Z ξ j.1.val)) := by
  intro hK
  have hc := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val 0
  have hd := actual_geometry_D_compensation s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource key j.1
  have hcp : 0<(j.1.val.1.val.1.absNorm:ℝ) := zero_lt_one.trans_le hc.1
  have hscalar := actual_geometry_left_scalar_sq s R seed W M Z ξ hZ a₁ a₂ ha₁ ha₂ hs₁ hs₂ key j
  have hh := mul_le_mul_of_nonneg_right hscalar
    (Real.rpow_nonneg hcp.le (ε-1))
  apply hh.trans
  exact scalar_left_compensation Z _ _ _ _ _ ε B hZ.le hcp (Nat.cast_nonneg _)
    hd.2.le hε hc.2

/-- Reflection changes the selected ideal but not the physical-D
compensator, so the right allocation mass supplies its reciprocal. -/
theorem actual_geometry_right_mass_compensation (s : Input ι)(R seed : Ideal O)
    (K Z ξ M A B ε : ℝ)(hK : 0< K)(hZ : 1< Z)(hε : 0≤ε)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    ‖geometryColumnScalar true s R seed K Z ξ M A hK key weight j‖^2*
      ((geometryColumnIdeal true s R seed K Z ξ hK key j).absNorm:ℝ)^(ε-1)≤
      (Z^(B*ε)/Z^(rightExponent A (geometryExponents s R seed K Z ξ j.1.val)))/
        geometryDCompensator key := by
  have hd := actual_geometry_D_compensation s R seed K Z ξ B hs hz₁ hz₂ hsource key j.1
  have hc := (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 1).2
  have he : ‖geometryColumnScalar true s R seed K Z ξ M A hK key weight j‖^2=
      1/Z^(rightExponent A (geometryExponents s R seed K Z ξ j.1.val)) := by
    simp only [geometryColumnScalar,ite_true,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,
      Real.sq_sqrt (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),one_div]
  rw [he]
  exact scalar_right_compensation Z _ _ _ ε B hZ.le (geometryDCompensator_pos key) hd.1 hε hc

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryDCompensator_pos

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_D_compensation

#print axioms OAI.SevenEighths.Cycle61InitialMass.scalar_left_compensation

#print axioms OAI.SevenEighths.Cycle61InitialMass.scalar_right_compensation

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_left_mass_compensation

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_right_mass_compensation

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryScalarCompensation -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryCompensatedHigh; sha256 b33f76dcf8db53d77d2c81c8d3e3718d843731e8fcba456dda6515fdb7fc57db -/
section
                                                              
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily Cycle61Moment

/-- Shift the actual side normalization inside the coefficient coordinate.
The varying side exponent then cancels before joint density is applied. -/
def compensatedHighCoordinates (x : Fin 4→ℝ)(side : ℝ) : Fin 4→ℝ :=
  childHighCoordinates x (-side)

lemma compensated_high_exponent (δ side : ℝ)(x : Fin 4→ℝ) :
    highExponentValue δ (compensatedHighCoordinates x side)=
      highExponentValue δ x-side := by
  simp only [compensatedHighCoordinates,child_high_exponent_value,sub_eq_add_neg]

lemma compensated_high_reserve (δ side reserve error : ℝ)(x : Fin 4→ℝ)
    (h : highExponentValue δ x≤ side-reserve+error) :
    highExponentValue δ (compensatedHighCoordinates x side)≤ error-reserve := by
  rw [compensated_high_exponent]
  linarith

lemma compensated_high_coordinate_box (x : Fin 4→ℝ)(side B S : ℝ)
    (hx : ∀j,-B≤ x j ∧ x j≤ B)(hs : |side|≤ S) :
    ∀j,-(B+S)≤ compensatedHighCoordinates x side j ∧
      compensatedHighCoordinates x side j≤ B+S := by
  intro j
  have hh := child_high_coordinate_box x B (-side) hx j
  simp only [abs_neg] at hh
  dsimp only [compensatedHighCoordinates]
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

/-- Multiply by the literal first allocation mass without pulling out a
maximum over labels. Only the fixed compensated factor is external. -/
lemma compensated_high_coefficient (Z mass coeff factor loss side : ℝ)
    (x : Fin 4→ℝ)(hZ : 0< Z)(hm : 0≤ mass)
    (hmass : mass≤ factor*Z^loss/Z^side)(hcoeff : coeff≤ Z^(x 0)) :
    mass*coeff≤(factor*Z^loss)*Z^((compensatedHighCoordinates x side) 0) := by
  have hh := mul_le_mul_of_nonneg_left hcoeff hm
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hZ.le _)).trans_eq
  simp only [compensatedHighCoordinates,childHighCoordinates,ite_true]
  rw [show x 0+-side=x 0-side by ring,Real.rpow_sub hZ]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.compensated_high_exponent
#print axioms OAI.SevenEighths.Cycle61InitialMass.compensated_high_reserve
#print axioms OAI.SevenEighths.Cycle61InitialMass.compensated_high_coordinate_box
#print axioms OAI.SevenEighths.Cycle61InitialMass.compensated_high_coefficient

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryCompensatedHigh -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighBins; sha256 8c080b1cdde598e7ec91645c5957695b8d5035cbb3fd764817e03f38ceba69a8 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
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
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint finite-bin high density for the physical geometric rows. The outside
weight stays inside each selected shell; only the fixed bin count is charged. -/
theorem actual_geometry_binned_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a rawError allowance Kcontrol T width Bbox target reserve : ℝ) (i : ℕ),
      167/200 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      Function.Injective key →
      ∀(labels : Finset κ)(x : κ→ Fin 4→ℝ)(coeff : κ→ℝ),
      (∀l∈labels,∀j,-Bbox≤ x l j ∧ x l j≤ Bbox) →
      (∀l∈labels,x l 2+width≤ Q) →
      (∀l∈labels,coeff l≤ Z^(x l 0)) →
      (∀l∈labels,highExponentValue (2*a-1) (x l)≤ target-reserve) →
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
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap Araw : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      Real.logb Z (preVolume s.toData)≤ Araw → pad≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
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
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*a-1)*x l 3+rawError) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      ((Finset.Icc (⌊-Bbox/width⌋:ℤ) ⌊Bbox/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-reserve+4*width+loss+rawError+allowance)) := by
  obtain ⟨bound,hbound,J,hselected⟩ := actual_geometry_selected_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hselected P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key a rawError allowance Kcontrol T width Bbox target reserve i ha ha' hKcontrol hT hwidthbin
    hinj labels x coeff hx hq hcoeff hpoint st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  have hZ : 1< Z := by linarith [he.1]
  have hzpos : 0< Z := by linarith
  have hδ : Cycle61.Arithmetic.q0≤2*a-1 ∧ 2*a-1≤3/4 := by
    norm_num [Cycle61.Arithmetic.q0]; constructor <;> linarith
  have hd0 : 0≤2*a-1 := by linarith
  let shell := fun l=>∑L∈Ds l,∑alloc∈(src l).toSource.active L,
    retainedAllocationCost (src l) L alloc (z l)
  have hshell0 (l : κ) : 0≤ shell l := Finset.sum_nonneg (fun L _=>
    Finset.sum_nonneg (fun alloc _=>retained_allocation_cost_nonneg _ _ _ _))
  let Cbase := C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)
  have hbase : 0≤ Cbase := by dsimp [Cbase]; positivity
  have hbin (bin₂ : Fin 4→ℤ)(hbin : bin₂∈labels.image (fun l=>exponentBin width (x l))) :
      (∑l∈labels.filter (fun l=>exponentBin width (x l)=bin₂),coeff l*shell l)≤
        (Cbase*Z^(loss+rawError+allowance))*Z^(highExponentValue (2*a-1) (exponentBinUpper width bin₂)) := by
    let rows := labels.filter (fun l=>exponentBin width (x l)=bin₂)
    let u := exponentBinUpper width bin₂
    have hrow' (l : κ)(hl : l∈rows) : l∈labels := (Finset.mem_filter.mp hl).1
    have hround (l : κ)(hl : l∈rows)(j : Fin 4) : x l j≤ u j ∧ u j≤ x l j+width := by
      have hh:=exponent_bin_enclosure width hwidthbin (x l) j
      rw [(Finset.mem_filter.mp hl).2] at hh
      exact hh
    obtain ⟨l₀,hl₀,hkey₀⟩ := Finset.mem_image.mp hbin
    have hl₀' : l₀∈rows := Finset.mem_filter.mpr ⟨hl₀,hkey₀⟩
    have hq' : u 2≤ Q := (hround l₀ hl₀' 2).2.trans (hq l₀ hl₀)
    have hs := he.2 reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
      (u 2) (u 1) a ((2*a-1)*u 3+rawError) allowance Kcontrol T i
      hq' (by linarith) ha' hKcontrol hT hinj rows st hQM hQη z hz hchar hpuncture hrow
      (fun l hl=>⟨(hzero l (hrow' l hl)).1.trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 2).1),(hzero l (hrow' l hl)).2⟩)
      (fun l hl=>hsupport l (hrow' l hl)) (fun l hl=>hnorm l (hrow' l hl))
      (fun l hl=>(hmissing l (hrow' l hl)).trans
        (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 1).1))
      hi hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁
      (fun l hl=>hf₁ l (hrow' l hl)) E R₂ pick t w σ v θ p Ds cap Araw
      hcap hmatches hscales hAraw hpadallow (fun l hl=>hf₂ l (hrow' l hl))
      (fun l hl=>hstateMask l (hrow' l hl)) (fun l hl=>hwidth l (hrow' l hl))
      (fun l hl=>hradial l (hrow' l hl)) (fun l hl=>hupper l (hrow' l hl))
      hw hwr hσlo hσhi
      (fun l hl=>hfreq l (hrow' l hl)) (fun l hl=>hplainfreq l (hrow' l hl))
      (fun l hl=>hW l (hrow' l hl)) (fun l hl=>hDs l (hrow' l hl))
      (fun l hl=>hdyad l (hrow' l hl)) (fun l hl=>hcontrol l (hrow' l hl)) (by
        intro l hl
        have hh:=hledger l (hrow' l hl)
        have hr:=mul_le_mul_of_nonneg_left (hround l hl 3).1 hd0
        linarith)
    calc
      _≤∑l∈rows,Z^(u 0)*shell l := Finset.sum_le_sum (fun l hl=>
        mul_le_mul_of_nonneg_right ((hcoeff l (hrow' l hl)).trans
          (Real.rpow_le_rpow_of_exponent_le hZ.le (hround l hl 0).1)) (hshell0 l))
      _=Z^(u 0)*(∑l∈rows,shell l) := (Finset.mul_sum _ _ _).symm
      _≤ Z^(u 0)*(Cbase*Z^(u 1+u 2*unmarkedDensity (2*a-1)+loss+
          ((2*a-1)*u 3+rawError)+allowance)) := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hzpos.le _)
      _=_ := by
        dsimp only [highExponentValue,u]
        rw [mul_left_comm,←Real.rpow_add hzpos]
        rw [mul_assoc Cbase,←Real.rpow_add hzpos]
        congr 1
        congr 1
        ring
  have hh:=high_binned_sum labels x (fun l=>coeff l*shell l) width Bbox (2*a-1) Z
    (Cbase*Z^(loss+rawError+allowance)) target reserve hwidthbin hZ.le (by positivity) hδ hx hpoint hbin
  apply hh.trans_eq
  congr 1
  rw [mul_assoc,←Real.rpow_add hzpos]
  congr 1
  congr 1
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_binned_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighBins -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryUniformScalar; sha256 b5546a6e9316f5c100995659ea8bfd40a7f1a97c3dc9f056a367aac661deeb1b -/
section
                                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- Uniform before the moving source and both first-label orientations. -/
def geometrySupportConstant (N : ℕ)(lo a₁ a₂ : ℝ) : ℝ :=
  4/((min 1 lo)^N*a₁*a₂)

lemma geometrySupportConstant_pos (N : ℕ)(lo a₁ a₂ : ℝ)
    (hlo : 0< lo)(ha₁ : 0< a₁)(ha₂ : 0< a₂) :
    0< geometrySupportConstant N lo a₁ a₂ := by
  unfold geometrySupportConstant
  positivity

lemma actual_geometry_support_constant {ι : Type*}[Fintype ι]
    (s : Input ι)(N : ℕ)(lo a₁ a₂ : ℝ)(hn : Fintype.card ι≤ N)
    (hlo : 0< lo)(hl : lo≤ s.lower)(ha₁ : 0< a₁)(ha₂ : 0< a₂) :
    0≤4/((∏i,s.lo i)*a₁*a₂) ∧
      4/((∏i,s.lo i)*a₁*a₂)≤ geometrySupportConstant N lo a₁ a₂ := by
  have hp : (min 1 lo)^N≤∏i,s.lo i := by
    apply (pow_le_pow_of_le_one (lt_min zero_lt_one hlo).le (min_le_left _ _) hn).trans
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _ : ι=>min 1 lo)
        (g:=fun i=>s.lo i) (fun _ _=>(lt_min zero_lt_one hlo).le)
        (fun i _=>(min_le_right _ _).trans (hl.trans (s.lower_le i)))
  have hpp : 0<∏i,s.lo i := Finset.prod_pos (fun i _=>s.lo_pos i)
  refine ⟨by positivity,?_⟩
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp ha₁.le) ha₂.le

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometrySupportConstant_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_support_constant

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryUniformScalar -/
