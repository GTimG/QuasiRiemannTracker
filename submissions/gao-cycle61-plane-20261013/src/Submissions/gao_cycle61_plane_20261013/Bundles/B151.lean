/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B115
import Submissions.gao_cycle61_plane_20261013.Bundles.B134
import Submissions.gao_cycle61_plane_20261013.Bundles.B145
import Submissions.gao_cycle61_plane_20261013.Bundles.B147
import Submissions.gao_cycle61_plane_20261013.Bundles.B150

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighAdmission; sha256 52a23f414a1662096ffe467caec4b6a962843ec6fd33ef0ab8c60a264ba99d14 -/
section
                                                    
                                                           

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O

/-- A larger support ceiling preserves the literal retained state. -/
def widenHighState {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ)(hbΦ : 2≤ bΦ) : NaturalState Z Bmask bΦ :=
  { st with
    radial_support := by
      intro x hx
      exact (st.radial_support hx).trans hbΦ }

lemma widen_high_state_fields {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ)(hbΦ : 2≤ bΦ) :
    (widenHighState st bΦ hbΦ).character=st.character ∧
      (widenHighState st bΦ hbΦ).fixedModulus=st.fixedModulus ∧
      (widenHighState st bΦ hbΦ).puncture=st.puncture ∧
      (widenHighState st bΦ hbΦ).radial=st.radial ∧
      (widenHighState st bΦ hbΦ).width=st.width := ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma actual_geometry_child_puncture_ne_zero {ι : Type*}[Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(hR : R≠0)
    (K Z ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
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
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0< K),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → K≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
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
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
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
      ((Finset.univ.filter (fun r : rows=>key r=target)).card:ℝ)≤ D*Z^(2*ε) := by
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
    (hK : 0< K)(hZ : 1< Z)(hb : 0< b)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hradius : (d r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter)(Bmask : ℝ)(Q M : Ideal O)
    (hQM : Q≤ M)(hQη : Q≤η₀.modulus)
    (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤ Z^Bmask)
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
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)))≤ Mcap) :
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
    st.fixedModulus≤ M ∧ st.fixedModulus≤η₀.modulus ∧
      st.character=(d r.val.1).τ ψ ∧ st.puncture=puncture ∧
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture ∧
      st.width≤ Mcap ∧ holes≠0 ∧ ∃hz : st.radial.keep z,
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
    (hH : RayOrthogonality.globalUnits M≤ H)
    (N : ℕ)(Cs bs : ℝ)(hCs : 1≤ Cs)(hbs : 1≤ bs)
    (s : Input ι)(hcard : Fintype.card ι≤ N)(hM : ∀j,s.M j≤ Cs)
    (hb₁ : s.b₁≤ bs)(hb₂ : s.b₂≤ bs)
    (η₀ : Character)(θ : ι→ RayQuotient.Characters M H)(w σ v : ι→ℝ)
    (W : ℝ→ℂ)(B₀ Z cap : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W B₀ Z)
    {ap bp : ℝ}(p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ))(hW₂ : s.W₂=(p.profile 1:ℝ→ℂ))
    (hb₁p : s.b₁=bp)(hb₂p : s.b₂=bp)
    (hscale : ∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap)
    (reflected : Bool)(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)
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
      (∀second j,Cycle61.Physical.sourcePlainScales src.toData.toSource second j≤ Z^cap) ∧
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.joint_fiber_indicator_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_row_fiber_bound

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_state_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_child_profile_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.widen_high_state_fields

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_child_puncture_ne_zero

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighAdmission -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLowAdmission; sha256 78ee29d1c67feecdcc6b58c9dafe56383650234b181e690f02faf57b041b6f41 -/
section
                                                     
                                                         
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSourceLiveColumn CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open Cycle61FinalLow CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonHeightEnvelope CenteredMomentCommonRawScale
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Both allocations are literal; the first coordinate retains its live column. -/
def geometryLowChain (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    Chain s :=
  {C₁:=geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val,
    R₁:=R,B₁:=q.2,
    η₁:=geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val,t₁:=t,
    E₂:=E₂,R₂:=R₂,B₂:=B₂}

omit [DecidableEq α] in
theorem actual_geometry_low_chain_fields (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (bin : ℤ×(Fin 5→ℤ)) (t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)
    (B₂ : actualAllocations (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    let chain:=geometryLowChain reflected s R seed K Z ξ hK bin t q E₂ R₂ B₂
    chain.C₁=geometryColumnIdeal reflected s R seed K Z ξ hK bin q.1.val ∧
      chain.R₁=R ∧ HEq chain.B₁ q.2 ∧
      chain.η₁=geometryColumnCharacter reflected s R seed K Z ξ hK bin q.1.val ∧
      chain.t₁=t ∧ chain.first=geometryLowFirstChild reflected s R seed K Z ξ hK bin t q :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

abbrev GeometryLowSecondIndex (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) :=
  ActualSecondBlockIndex
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ

/-- The second datum comes from the actual retained-energy expansion, with
its original character family, rows and physical cutoff. -/
def geometryLowSecondDatum (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    SecondInputDatum α :=
  actualSecondBlockDatum (liveIndices q.2.val)
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ
    (first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _) n

section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "src" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
local notation "firstIdeal" => geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val

/-- The selected second ideal and puncture are the literal block fields. -/
def geometryLowActualChain (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C)) : Chain s :=
  geometryLowChain reflected s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    bin t q (if second then (datum).D else (datum).C) (datum).R B₂

/-- Admission uses an actual live row once for geometry; it does not select
an allocation separately at each frequency in the low energy sum. -/
def geometryLowActualGeometry (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C))
    (r : secondLiveRows (fun _:Unit=>(datum).block))
    (hf₁ : frozenCoefficient q.2.val firstIdeal R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then (datum).D else (datum).C) (datum).R (src).ν (src).W (src).P≠0) :
    LiveMainGeometry s
      (geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂)
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b N :=
  actualGeometryLow reflected s
    (geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂)
    R seed Z Mrow amp ξ reserve b N hZ bin q.1.val rfl rfl datum r rfl rfl
    (by
      cases second
      · exact Or.inl rfl
      · exact Or.inr rfl) hf₁ hf₂

theorem actual_geometry_low_admission_fields (second : Bool)
    (B₂ : actualAllocations (src).pools (if second then (datum).D else (datum).C))
    (r : secondLiveRows (fun _:Unit=>(datum).block))
    (hf₁ : frozenCoefficient q.2.val firstIdeal R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val (if second then (datum).D else (datum).C) (datum).R (src).ν (src).W (src).P≠0) :
    let chain:=geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let g:=geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂ r hf₁ hf₂
    chain.C₁=firstIdeal ∧ chain.R₁=R ∧ HEq chain.B₁ q.2 ∧
      chain.η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val ∧
      chain.t₁=t ∧ chain.first=src ∧
      g.reflected=reflected ∧
      g.C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).C ∧
      g.D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).D ∧
      HEq g.E₀ (geometryFirstSource s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val.1).inactive ∧
      g.datum=datum ∧ g.row=r ∧
      g.datum.radius=frequencyRadius
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
          (geometryFirstLabel s R seed (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ :=
  ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

lemma actual_geometry_low_second_puncture (hR : R≠0) (second : Bool) :
    (datum).R*(if second then (datum).D else (datum).C)≠0 := by
  have hp : (datum).R≠0 := actual_geometry_child_puncture_ne_zero reflected s R seed hR
    (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  apply mul_ne_zero hp
  cases second
  · exact (datum).hC.1
  · exact (datum).hD.1

end Actual

/-- The constructor's literal first child inherits Matches, original plain
profiles, both plain caps and the fixed two-allocation control. -/
theorem actual_geometry_low_chain_profile_admission
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤ H)
    (N : ℕ)(Cs bs : ℝ)(hCs : 1≤ Cs)(hbs : 1≤ bs)
    (s : Input α)(hcard : Fintype.card α≤ N)(hM : ∀j,s.M j≤ Cs)
    (hb₁ : s.b₁≤ bs)(hb₂ : s.b₂≤ bs)
    (η₀ : Character)(θ : α→ RayQuotient.Characters M H)(w σ v : α→ℝ)
    (W : ℝ→ℂ)(B₀ Z cap : ℝ)(hm : Matches M H hH s η₀ θ w σ v W B₀ Z)
    {ap bp : ℝ}(p : Profiles ap bp)
    (hW₁ : s.W₁=(p.profile 0:ℝ→ℂ))(hW₂ : s.W₂=(p.profile 1:ℝ→ℂ))
    (hb₁p : s.b₁=bp)(hb₂p : s.b₂=bp)
    (hscale : ∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap)
    (reflected : Bool)(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (q : GeometryLowFirstIndex reflected s R seed K Z ξ hK bin)
    (E₂ R₂ : Ideal O)(B₂ : actualAllocations
      (geometryLowFirstChild reflected s R seed K Z ξ hK bin t q).pools E₂) :
    let chain:=geometryLowChain reflected s R seed K Z ξ hK bin t q E₂ R₂ B₂
    Matches M H hH chain.first η₀ (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val)
      (fun j=>v j.val) W B₀ Z ∧
      chain.first.W₁=(p.profile 0:ℝ→ℂ) ∧ chain.first.W₂=(p.profile 1:ℝ→ℂ) ∧
      chain.first.b₁=bp ∧ chain.first.b₂=bp ∧
      (∀second j,Cycle61.Physical.sourcePlainScales chain.first.toData.toSource second j≤ Z^cap) ∧
      ∀(χ : Character)(height : ℝ),
        Cycle61HighResidual.wholeControl (chain.final χ height)≤2*bs*Cs^N := by
  intro chain
  obtain ⟨hmatch,hp₁,hp₂,hb₁',hb₂',hcaps,hcontrol⟩ := actual_geometry_child_profile_admission
    M H hH N Cs bs hCs hbs s hcard hM hb₁ hb₂ η₀ θ w σ v W B₀ Z cap hm p
    hW₁ hW₂ hb₁p hb₂p hscale reflected R seed K ξ hK bin q.1.val q.2 t
  exact ⟨hmatch,hp₁,hp₂,hb₁',hb₂',hcaps,fun χ height=>hcontrol E₂ R₂ B₂ χ height⟩


end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryLowChain
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_chain_fields
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryLowSecondDatum
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryLowActualChain
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryLowActualGeometry
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_admission_fields
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_second_puncture
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_chain_profile_admission

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLowAdmission -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLowColumn; sha256 73af3a89174566304facfbf6eb35ae53125d789b21cef4400b2d1d25a6095331 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _



/-- The first projector divides both ideals in the literal second block. -/
theorem actual_geometry_low_column_seed (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
    d.seed∣d.C ∧ d.seed∣d.D := by
  exact (actual_retained_block_gates (liveIndices q.2.val)
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) (fun _=>logAnnulus) q.1.val q.1.property)
    hw₁ hw₂
    (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val))
    (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)) Z ξ
    (first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _) n) |>.imp_right (fun h=>h.1)

section Column
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
set_option quotPrecheck false in
local notation "d" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
set_option quotPrecheck false in
local notation "firstChild" => geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
variable (second : Bool)
/-- A literal child identification rewrites the complete low column sum.
It leaves the common allocation fixed and imposes no energy hypothesis. -/
theorem actual_geometry_low_column_sum (χ : RayFourExpansion.RayCharacter) (v : ℝ)
    (actualChild : Input (liveIndices q.2.val))
    (hchild : actualChild=withHeight firstChild ((d).τ χ) v)
    (Ds : Finset (Ideal O)) (zs : Finset O) (weight : O→ℝ)
    (hE : Supported (if second then (d).D else (d).C)) :
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn actualChild (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2)=
    (∑D∈Ds,∑z∈zs,weight z*
      ‖normalizedColumn (withHeight firstChild ((d).τ χ) v)
        (if second then (d).D else (d).C) hE (d).R (d).seed D z‖^2) := by
  rw [hchild]


end Column
end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_column_seed
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_column_sum

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLowColumn -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLowPayment; sha256 d5e3f88b7319410248248b12d52c2227b6ae7a7ca9355a2c1f2e2dc0410a0a5b -/
section
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle61Moment Cycle61FinalCapacity CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Actual child scalar costs are summed over the full first/second label
and projector shell, with no squarefree restriction on either ideal label. -/
theorem eventual_actual_geometry_low_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
      ∀(reflected second : Bool)(T p exponent error εcommon M a ξ reserve : ℝ),
      0≤εcommon → 1≤ T → p≤ B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤ exponent) →
      ∀(Ds : FirstSourceLabel→ Finset (Ideal O))
        (children : FirstSourceLabel→ Ideal O→ Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      ∀Rfirst : Ideal O,
      ∀alloc : (l : FirstSourceLabel)→(D : Ideal O)→(v : FirstSourceLabel)→
        actualAllocations s.pools (if reflected then l.1.2 else l.1.1),
      ∀(χ : FirstSourceLabel→ Ideal O→ FirstSourceLabel→ Character)
        (t : FirstSourceLabel→ Ideal O→ FirstSourceLabel→ℝ),
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,
        frozenCoefficient (alloc l D v).val (if reflected then l.1.2 else l.1.1)
          Rfirst s.ν s.W s.P≠0) →
      (∑l∈labels,∑D∈Ds l,∑v∈children l D,
        Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
          volume (child s (if reflected then l.1.2 else l.1.1) Rfirst
            (alloc l D v) (χ l D v) (t l D v)))*
          (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
          Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
            (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
            v.1.1 v.1.2 v.2.val+a+error))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hlabels⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a ξ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ Rfirst alloc χ t halloc
  have hbudget := hlabels reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbudget
  apply le_trans _ hbudget
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro v hv
  have hh := hz.2 s hcard hlow reflected second l (hsup l hl).1 (hsup l hl).2
    (heq l hl) Rfirst (alloc l D v) (χ l D v) (t l D v) (halloc l hl D hD v hv)
    v.1.1 v.1.2 (hsup₂ l hl D hD v hv).1 (hsup₂ l hl D hD v hv).2 v.2.val
    M a ξ reserve error εcommon B hecommon (by
      cases second
      · exact (hnorm₂ l hl D hD v hv).1
      · exact (hnorm₂ l hl D hD v hv).2)
  simpa only [add_assoc] using hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_low_label_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLowPayment -/
