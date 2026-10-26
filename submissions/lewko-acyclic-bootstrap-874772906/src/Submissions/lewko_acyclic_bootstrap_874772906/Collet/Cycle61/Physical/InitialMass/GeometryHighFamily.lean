import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryHighActualShell

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentCommonPairedSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O

/-- A finite family is reduced to one maximizing representative per joint
key. The complete cost is selected, so its physical scalar stays inside the
joint sum. This statement supplies no analytic bound on that sum. -/
theorem high_family_max_selection {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→Key)(cost : Row→ℝ)(W : ℝ)(hW : 0≤W)
    (hc : ∀r,0≤cost r)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W) :
    ∃pick : (k : Finset.univ.image key)→Row,
      (∀k,key (pick k)=k.val) ∧ Function.Injective (fun k=>key (pick k)) ∧
      (∑r,cost r)≤W*(∑k : Finset.univ.image key,cost (pick k)) := by
  let keys:=Finset.univ.image key
  let fiber:=fun k : Key=>Finset.univ.filter (fun r=>key r=k)
  have hn (k : keys) : (fiber k.val).Nonempty := by
    obtain ⟨r,hr,he⟩:=Finset.mem_image.mp k.property
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩
  choose pick hp hm using (fun k : keys=>Finset.exists_max_image (fiber k.val) cost (hn k))
  have hk : ∀k,key (pick k)=k.val:=fun k=>(Finset.mem_filter.mp (hp k)).2
  refine ⟨pick,hk,?_,?_⟩
  · intro k l he
    apply Subtype.ext
    exact (hk k).symm.trans (he.trans (hk l))
  · apply joint_fiber_selection key cost W _ hW hc (fun k _=>hfiber k)
    intro other hother
    apply Finset.sum_le_sum
    intro k _
    exact hm k (other k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hother k⟩)

/-- The physical second normalized column, with its source character and
reflection inherited from the literal retained row. -/
def highNormalizedRowCost {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) : ℝ :=
  let v:=d r.val.1
  let E:=if second then v.D else v.C
  let hE : Supported E:=by dsimp only [E]; split <;> first | exact v.hD | exact v.hC
  let ψ:=if second then r.val.2.2.1⁻¹ else r.val.2.1
  let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
  ∑L∈Ds,‖normalizedColumn (withHeight v.input (v.τ ψ) t) E hE v.R v.seed L z‖^2

lemma high_normalized_row_cost_nonneg {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) :
    0≤highNormalizedRowCost second d r t Ds := by
  dsimp only [highNormalizedRowCost]
  exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- Genuine live-block fibers pay for the actual normalized columns with
the physical first scalar still inside the selected joint sum. Constants
precede the original source and every moving label. -/
theorem actual_geometry_high_normalized_family_selection (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → (Z^Dfirst)≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(εmass : ℝ)
        (height : rows→ℝ)(Ds : rows→Finset (Ideal O)),
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * highNormalizedRowCost second datum r.val (height r) (Ds r)
      ∃pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) ∧ Function.Injective (fun j=>key (pick j)) ∧
        Function.Injective (fun j=>if second then reflectedNonzeroJointLabel (key (pick j)) else key (pick j)) ∧
        (∑r : rows,cost r)≤(D*Z^(2*ε))*(∑j : Finset.univ.image key,cost (pick j)) := by
  obtain ⟨D,hD,hrows⟩:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows] with Z hz
  intro hZ α Label _ _ _ reflected s R seed Dfirst a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf rows second W εmass height Ds key cost
  have hbnd:=hz hZ reflected s R seed (Z^Dfirst) a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows
  obtain ⟨pick,hpick,hinjpick,hsum⟩:=high_family_max_selection key cost (D*Z^(2*ε))
    (by positivity) (fun r=>mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hK bin _)
      (high_normalized_row_cost_nonneg second datum r.val (height r) (Ds r))) hbnd
  refine ⟨pick,hpick,hinjpick,?_,hsum⟩
  cases second
  · exact hinjpick
  · intro j k h
    apply hinjpick
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

/-- Canonical retained states for a selected family, widened only in their
support ceiling. Dictionary, puncture, mask, width and retained-profile
gates follow pointwise from actual source admission. -/
theorem actual_geometry_high_family_states {ι α Label κ : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ a reserve b Mcap Bmask bΦ : ℝ)(N : ℕ)
    (hK : 0<K)(hZ : 1<Z)(hb : 0<b)(hbΦ : 2≤bΦ)(bin : ℤ×(Fin 5→ℤ))
    (column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (datum : Label→SecondInputDatum α)(first : Label→FirstSourceLabel)
    (row : κ→secondLiveRows (fun l=>(datum l).block))
    (hparent : ∀k,(datum (row k).val.1).input.η=
      geometryColumnCharacter reflected s R seed K Z ξ hK bin (column k))
    (hradius : ∀k,(datum (row k).val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin (column k))) Z ξ)
    (hfirst : ∀k,first (row k).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column k))
    (hR : ∀k,(datum (row k).val.1).R≠0)(ψ : κ→RayCharacter)(Q M : Ideal O)
    (hQM : Q≤M)(hQη : Q≤η₀.modulus)
    (hPN : ∀k,(((datum (row k).val.1).R*
      (if second then (datum (row k).val.1).D else (datum (row k).val.1).C)).absNorm:ℝ)≤Z^Bmask)
    (m : κ→O)(hm : ∀k,m k≠0)(hml : ∀k,ConcretePrimeRowBridge.goodLambda∣m k)
    (hm2 : ∀k,(2:O)∣m k)
    (hkeep : ∀k,CenteredMomentRestrictedEnergy.nonexceptional (datum (row k).val.1).input.η
      (ψ k) Q (m k) (datum (row k).val.1).block.frequency
      (if second then -(row k).val.2.2.2.val else (row k).val.2.2.2.val))
    (hwidth : ∀k,
      let src:=geometryFirstSource s R seed K Z ξ hK bin (column k).1
      let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
      let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator (datum (row k).val.1).C (datum (row k).val.1).D))+
        Real.logb Z ((∏p∈(datum (row k).val.1).inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)))≤Mcap) :
    let unit:=fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf:=fun k=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK
      bin (column k) datum first (row k) (hfirst k)
    let key₀:=fun k=>secondEncodedNonzeroRow (fun l=>(datum l).block) first (row k) (!reflected) u₀ unit (hf k)
    let key:=fun k=>if second then reflectedNonzeroJointLabel (key₀ k) else key₀ k
    let z:=fun k=>if second then -(row k).val.2.2.2.val else (row k).val.2.2.2.val
    let puncture:=fun k=>(datum (row k).val.1).R*
      (if second then (datum (row k).val.1).D else (datum (row k).val.1).C)
    let hP : ∀k,puncture k≠0:=fun k=>mul_ne_zero (hR k) (by
      split <;> first | exact (datum (row k).val.1).hD.1 | exact (datum (row k).val.1).hC.1)
    let base:=fun k=>retainedState Z Bmask hZ ((datum (row k).val.1).τ (ψ k)) Q
      (puncture k) (hP k) (hPN k) (datum (row k).val.1).radius
      (datum (row k).val.1).C (datum (row k).val.1).D (datum (row k).val.1).inactive
    let st:=fun k=>widenHighState (base k) bΦ hbΦ
    ∀k,(st k).fixedModulus≤M ∧ (st k).fixedModulus≤η₀.modulus ∧
      (st k).character=(datum (row k).val.1).τ (ψ k) ∧ (st k).puncture=puncture k ∧
      (st k).mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator (puncture k) ∧
      (st k).width≤Mcap ∧ (datum (row k).val.1).input.η.modulus*puncture k≠0 ∧
      ∃hz : (st k).radial.keep (z k),
        (st k).radial.profile (‖eisEmbedding (z k)‖^2/(st k).radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow (st k).character (z k) ((st k).row_ne_zero (z k) hz)).character
          (st k).puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin (column k),ψ k))
          (nonzeroJointSourceRow (key k)).val (nonzeroJointSourceRow (key k)).property).character
          ((datum (row k).val.1).input.η.modulus*puncture k)) I := by
  intro unit hf key₀ key z puncture hP base st k
  have had:=actual_geometry_high_state_admission reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed
    K Z ξ a reserve b Mcap N hK hZ hb bin (column k) datum first (row k)
    (hparent k) (hradius k) (hfirst k) (hR k) (ψ k) Bmask Q M hQM hQη (hPN k)
    (m k) (hm k) (hml k) (hm2 k) (hkeep k) (hwidth k)
  simpa only [st,widenHighState,NaturalState.mask,NaturalState.width] using had


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_family_max_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_normalized_family_selection

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_family_states
