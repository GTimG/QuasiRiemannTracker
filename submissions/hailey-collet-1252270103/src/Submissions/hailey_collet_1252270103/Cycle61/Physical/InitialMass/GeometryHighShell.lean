import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondChildHighShell
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryNaturalState
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondSourceControls

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

/-- High shell energy for actual geometric second rows in the fixed two-ray
dictionary. Canonical masks, nonzero holes and both stages of ideal support
are derived from the source, for either first orientation and second sign. -/
theorem actual_geometry_selected_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      Function.Injective key →
      ∀ labels : Finset κ,
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q ∧
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
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^m) →
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
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
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤e) →
      (∑l∈labels,∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨bound,hbound,J,hboundJoint⟩ := actual_child_selected_high_shell
    (α:=α) (bp:=bp) M H hH (secondFixedDictionary η₀) η₀ B Q loss ε hB hQ hQB hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key q m a e allowance Kcontrol T i hq ha ha' hKcontrol hT
    hinj labels st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  let index := fun l=>(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)
  let holes := fun l=>(datum (row l).val.1).input.η.modulus*
    ((datum (row l).val.1).R*(if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
  have hd l := actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin (column l) datum first (row l) (hparent l) (hfirst l) (hR l) (ψ l)
  have hmask l (I : Ideal O) :
      idealCoeff (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ (index l)) (nonzeroJointSourceRow (key l)).val
        (nonzeroJointSourceRow (key l)).property).character (holes l)) I := by
    have transfer (χ χ' : Character) (u v : O) (hu : u≠0) (hv : v≠0)
        (hc : χ=χ') (hr : u=v) :
        (naturalRow χ u hu).character=(naturalRow χ' v hv).character := by
      subst χ'; subst v; rfl
    have hv : (if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val)≠0 :=
      (hrow l) ▸ (st l).row_ne_zero (z l) (hz l)
    rw [transfer _ _ _ _ _ hv (hchar l) (hrow l),hpuncture l]
    exact (hd l).2 I
  have hfirstSupport l : Supported (key l).val.1.1.1 ∧ Supported (key l).val.1.1.2 ∧
      primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 := by
    have heq : (key l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l) := by
      cases second <;> exact hfirst l
    rw [heq]
    exact ⟨(geometryFirstSource s R seed K Z ξ hK bin (column l).1).hC,
      (geometryFirstSource s R seed K Z ξ hK bin (column l).1).hD,
      (geometryFirstSource s R seed K Z ξ hK bin (column l).1).sameSupport⟩
  have hsupported l : Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2≠0 ∧
      Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2≠0 := by
    refine ⟨(hfirstSupport l).1,(hfirstSupport l).2.1.1,?_⟩
    cases second <;> exact ⟨(datum (row l).val.1).hC,(datum (row l).val.1).hD.1⟩
  have heq l : primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 ∧
      primeSupport (key l).val.2.1.1=primeSupport (key l).val.2.1.2 := by
    refine ⟨(hfirstSupport l).2.2,?_⟩
    cases second <;> exact (datum (row l).val.1).sameSupport
  exact he.2 left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hKcontrol hT
    key hinj labels st hQM hQη z hz index holes (fun l _=>(hd l).1) (fun l _=>hmask l)
    hzero (fun l _=>hsupported l) (fun l _=>heq l) hsupport hnorm hmissing hi
    s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hledger

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_high_shell
