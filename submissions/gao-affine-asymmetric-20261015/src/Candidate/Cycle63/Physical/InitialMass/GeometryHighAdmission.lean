import Candidate.Cycle63.Physical.InitialMass.GeometryHighBins
import Candidate.Cycle63.Physical.InitialMass.GeometryClosedRowBudget

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O

/-- A larger support ceiling preserves the literal retained state. -/
def widenHighState {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ)(hbΦ : 2≤bΦ) : NaturalState Z Bmask bΦ :=
  { st with
    radial_support := by
      intro x hx
      exact (st.radial_support hx).trans hbΦ }

lemma widen_high_state_fields {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ)(hbΦ : 2≤bΦ) :
    (widenHighState st bΦ hbΦ).character=st.character ∧
      (widenHighState st bΦ hbΦ).fixedModulus=st.fixedModulus ∧
      (widenHighState st bΦ hbΦ).puncture=st.puncture ∧
      (widenHighState st bΦ hbΦ).radial=st.radial ∧
      (widenHighState st bΦ hbΦ).width=st.width := ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma actual_geometry_child_puncture_ne_zero {ι : Type*}[Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(hR : R≠0)
    (K Z ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    R*geometryColumnIdeal reflected s R seed K Z ξ hK bin column≠0 := by
  apply mul_ne_zero hR
  cases reflected
  · exact (geometryFirstSource s R seed K Z ξ hK bin column.1).hC.1
  · exact (geometryFirstSource s R seed K Z ξ hK bin column.1).hD.1

/-- Selection of one representative per literal joint key makes an
indicator cost at most one, without an analytic energy assumption. -/
lemma joint_fiber_indicator_selection {α β : Type*} (rows : Finset α) (key : ↥rows → β)
    (target : β) (pick : (j : Finset.univ.image key) → ↥rows)
    (hp : ∀j,key (pick j)=j.val) :
    (∑j : Finset.univ.image key,if key (pick j)=target then (1:ℝ) else 0)≤1 := by
  simp only [hp]
  by_cases ht : target∈Finset.univ.image key
  · let j₀ : Finset.univ.image key:=⟨target,ht⟩
    have he (j : Finset.univ.image key) : j.val=target ↔ j=j₀ := by
      constructor
      · intro h; apply Subtype.ext; exact h
      · intro h; exact congrArg Subtype.val h
    simp only [he]
    rw [Fintype.sum_ite_eq']
  · have he (j : Finset.univ.image key) : j.val≠target := by
      intro h
      exact ht (h ▸ j.property)
    simp only [he,ite_false,Finset.sum_const_zero]
    norm_num

/-- The fiber budget concerns the entire actual second source, including
its seed, projector and live support gates; no first-label count is charged. -/
theorem actual_geometry_high_row_fiber_bound (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0<K),
      Squarefree seed → Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → K≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block)),
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : rows=>key r=target)).card:ℝ)≤D*Z^(2*ε) := by
  obtain ⟨D,hD,hrows⟩ := actual_geometry_closed_row_budget η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows] with Z hz
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index block label left unit hunit hf rows key target
  let cost : rows→ℝ:=fun r=>if key r=target then 1 else 0
  have hh:=hz hZ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows cost 1
    (by intro r; dsimp [cost]; split <;> norm_num)
    (fun pick hp=>joint_fiber_indicator_selection rows key target pick hp)
  simpa only [cost,Finset.sum_boole,mul_one] using hh
/-- All retained-state and fixed-dictionary gates of the physical high shell,
including its width, follow from the actual nonexceptional row and cutoff. -/
theorem actual_geometry_high_state_admission {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ a reserve b Mcap : ℝ)(N : ℕ)
    (hK : 0<K)(hZ : 1<Z)(hb : 0<b)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hradius : (d r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter)(Bmask : ℝ)(Q M : Ideal O)
    (hQM : Q≤M)(hQη : Q≤η₀.modulus)
    (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤Z^Bmask)
    (m : O)(hm : m≠0)(hml : ConcretePrimeRowBridge.goodLambda∣m)(hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η ψ Q m
      (d r.val.1).block.frequency (if second then -r.val.2.2.2.val else r.val.2.2.2.val))
    (hwidth :
      let src:=geometryFirstSource s R seed K Z ξ hK bin j.1
      let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
      let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-Real.logb Z (normValue (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D))+
        Real.logb Z ((∏p∈(d r.val.1).inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)))≤Mcap) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let hP : puncture≠0 := mul_ne_zero hR (by
      split <;> first | exact (d r.val.1).hD.1 | exact (d r.val.1).hC.1)
    let st := retainedState Z Bmask hZ ((d r.val.1).τ ψ) Q puncture hP hPN
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let holes := (d r.val.1).input.η.modulus*puncture
    st.fixedModulus≤M ∧ st.fixedModulus≤η₀.modulus ∧
      st.character=(d r.val.1).τ ψ ∧ st.puncture=puncture ∧
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture ∧
      st.width≤Mcap ∧ holes≠0 ∧ ∃hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z puncture hP st holes
  have hd:=actual_geometry_natural_state reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK hZ
    bin j d first r hparent hfirst hR ψ Bmask Q hPN m hm hml hm2 hkeep
  have hw:=actual_geometry_second_width reflected s R seed K Z ξ a reserve b N hK hZ hb bin j d r
    hparent hradius Bmask ψ Q puncture hP hPN
  exact ⟨hQM,hQη,rfl,rfl,hd.2.1,hw.trans hwidth,hd.2.2⟩


/-- The actual geometric child inherits the original profile dictionary and
plain-scale caps. Both common allocations retain the same fixed control. -/
theorem actual_geometry_child_profile_admission {ι : Type*}[Fintype ι][DecidableEq ι]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (N : ℕ)(Cs bs : ℝ)(hCs : 1≤Cs)(hbs : 1≤bs)
    (s : Input ι)(hcard : Fintype.card ι≤N)(hM : ∀j,s.M j≤Cs)
    (hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (η₀ : Character)(θ : ι→RayQuotient.Characters M H)(w σ v : ι→ℝ)
    (W : ℝ→ℂ)(B₀ Z cap : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W B₀ Z)
    {ap bp : ℝ}(p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ))(hW₂ : s.W₂=(p.profile 1:ℝ→ℂ))
    (hb₁p : s.b₁=bp)(hb₂p : s.b₂=bp)
    (hscale : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap)
    (reflected : Bool)(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (alloc : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK bin column))
    (t : ℝ) :
    let C:=geometryColumnIdeal reflected s R seed K Z ξ hK bin column
    let χ:=geometryColumnCharacter reflected s R seed K Z ξ hK bin column
    let src:=child s C R alloc χ t
    Matches M H hH src η₀ (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val)
      (fun j=>v j.val) W B₀ Z ∧
      src.W₁=(p.profile 0:ℝ→ℂ) ∧ src.W₂=(p.profile 1:ℝ→ℂ) ∧ src.b₁=bp ∧ src.b₂=bp ∧
      (∀second j,Cycle63.Physical.sourcePlainScales src.toData.toSource second j≤Z^cap) ∧
      ∀(C₂ R₂ : Ideal O)(B₂ : actualAllocations src.pools C₂)(χ₂ : Character)(t₂ : ℝ),
        wholeControl (commonData (withHeight src χ₂ t₂) C₂ R₂ B₂)≤2*bs*Cs^N := by
  intro C χ src
  refine ⟨actual_child_matches M H hH s η₀ θ w σ v W B₀ Z hm C R alloc χ t,
    hW₁,hW₂,hb₁p,hb₂p,?_,?_⟩
  · intro second j
    exact (actual_child_plain_scale_le s C R alloc χ t second j).trans (hscale second j)
  · intro C₂ R₂ B₂ χ₂ t₂
    exact actual_two_common_control_fixed N Cs bs hCs hbs s hcard hM hb₁ hb₂ C R alloc χ t
      C₂ R₂ B₂ χ₂ t₂

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.joint_fiber_indicator_selection
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_high_row_fiber_bound

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_high_state_admission

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_child_profile_admission

#print axioms OAI.SevenEighths.Cycle63InitialMass.widen_high_state_fields

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_child_puncture_ne_zero
