import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondChildHighShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
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
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The level-one count of the rows of a bin of actual geometric second rows, in either first orientation and second
sign. Their natural states have the masked rows of the fixed two-ray dictionary at the rows' labels (derived from the
source), rows of norm at most `Z^q`, missing radicals at most `Z^m` and a zero of real part at least `a` up to height
`T` in the whole source family; then the rows number at most the density bound. The constants precede the rows. -/
theorem actual_geometry_high_label_count {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hloss : 0<loss) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀Bmask bΦ : ℝ,
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
      ∀(q m a T : ℝ),q ≤ Q → 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      Function.Injective key →
      ∀ labels : Finset κ,
      ∀ st : κ → NaturalState Z Bmask bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          T) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^m) →
      (labels.card : ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hcount⟩ := actual_whole_joint_high_row_count M H hH (secondFixedDictionary η₀) η₀ B Q loss
    hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro Z hZ Bmask bΦ κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key q m a T hq ha ha' hT hinj labels st hQM hQη z hz hchar hpuncture hrow hzero hsupport
    hnorm hmissing
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
  let back := Function.invFun key
  have hb (k : κ) : back (key k)=k := Function.leftInverse_invFun hinj k
  have hh := hcount left u₀ unit Z hZ q m a T Bmask bΦ hq ha ha' hT
    (labels.image key) (fun j=>st (back j)) (fun j=>hQM (back j))
    (fun j=>hQη (back j)) (fun j=>z (back j)) (fun j=>hz (back j))
    (fun j=>naturalRow (st (back j)).character (z (back j)) ((st (back j)).row_ne_zero (z (back j)) (hz (back j))))
    (fun j=>index (back j)) (fun j=>holes (back j))
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact (hd k).1)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hmask k)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hzero k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact hsupported k)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact heq k)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact hsupport k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact hnorm k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact hmissing k hk)
  rw [Finset.card_image_of_injective labels hinj] at hh
  exact hh

/-- High shell energy for actual geometric second rows, for either first orientation and second sign: the energy is
at most the pointwise bound times the number of rows. The rows are counted by the caller. -/
theorem actual_geometry_selected_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l)),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (a e allowance Kcontrol T : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      Function.Injective key →
      ∀ labels : Finset κ,
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
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
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
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)*labels.card := by
  obtain ⟨bound,hbound,hboundJoint⟩ := actual_child_selected_high_shell
    (α:=α) (bp:=bp) M H hH η₀ ε hε hap N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed K ξ hK bin column datum first row hfirst
    left unit hf rawKey key a e allowance Kcontrol T i ha ha' hKcontrol hT
    hinj labels st hQM hQη z hz hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  exact he.2 left u₀ unit a e allowance Kcontrol T i ha ha' hKcontrol hT
    key hinj labels st hQM hQη z hz hi
    s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hledger

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
