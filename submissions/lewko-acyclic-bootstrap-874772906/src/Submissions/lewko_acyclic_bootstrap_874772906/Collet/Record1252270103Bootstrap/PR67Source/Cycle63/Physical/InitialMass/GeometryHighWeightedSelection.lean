import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedContraction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentCommonPairedSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondEnergySplit
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope

/-- Restricting a finite row family does not increase any original key
fiber. The embedding may retain original block-nonzero evidence separately. -/
theorem high_restricted_key_fiber {Row Original Key : Type*}
    [Fintype Row] [Fintype Original] [DecidableEq Key]
    (embed : Row→Original) (hinj : Function.Injective embed)
    (key : Original→Key) (W : ℝ)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W) :
    ∀k,((Finset.univ.filter (fun r=>key (embed r)=k)).card:ℝ)≤W := by
  intro k
  let selected := Finset.univ.filter (fun r : Row=>key (embed r)=k)
  have hsub : selected.image embed⊆Finset.univ.filter (fun r=>key r=k) := by
    intro r hr
    obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hq).2⟩
  calc
    _=((selected.image embed).card:ℝ) := by
      rw [Finset.card_image_of_injective _ hinj]
    _≤((Finset.univ.filter (fun r=>key r=k)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _≤W := hfiber k

/-- A genuine full source-row datum admits the ordinary rows without
altering labels, rays or Fourier coordinates. The full-row identity is
structural and holds definitionally for actualSecondBlockDatum. -/
def ordinaryHighOriginalRow {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (d : Label→SecondInputDatum α)
    (χ : Label→RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)) :
    secondLiveRows (fun l=>(d l).block) := by
  let z : (d r.val.1).rows := ⟨r.val.2.2.2.val,by
    rw [hrows]
    exact (Finset.mem_filter.mp r.val.2.2.2.property).1⟩
  refine ⟨⟨r.val.1,r.val.2.1,r.val.2.2.1,z⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  exact (Finset.mem_filter.mp r.property).2

theorem ordinary_high_original_row_injective
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α)(χ : Label→RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) :
    Function.Injective (ordinaryHighOriginalRow d χ Q m hrows) := by
  intro r s h
  apply Subtype.ext
  have hl : r.val.1=s.val.1:=congrArg (fun q=>q.val.1) h
  rcases r with ⟨⟨l,χr,ψr,zr⟩,hr⟩
  rcases s with ⟨⟨k,χs,ψs,zs⟩,hs⟩
  dsimp only at hl
  subst k
  have hc : χr=χs:=congrArg (fun q=>q.val.2.1) h
  have hp : ψr=ψs:=congrArg (fun q=>q.val.2.2.1) h
  have hz : zr=zs:=Subtype.ext (congrArg (fun q=>q.val.2.2.2.val) h)
  subst χs ψs zs
  rfl

/-- The complete normalized row cost is unchanged by the inclusion. -/
@[simp] theorem ordinary_high_original_row_cost
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α)(χ : Label→RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))
    (second : Bool)(t : ℝ)(Ds : Finset (Ideal O)) :
    highNormalizedRowCost second d (ordinaryHighOriginalRow d χ Q m hrows r) t Ds=
      highNormalizedRowCost second (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l))
        r t Ds := by
  unfold highNormalizedRowCost
  dsimp only [ordinarySecondDatum,ordinaryHighOriginalRow]

/-- Genuine live-block fibers pay for the actual normalized columns with
the physical first scalar and arbitrary nonnegative outer factor inside the
selected joint sum. Constants
precede the original source and every moving label. -/
theorem actual_geometry_high_weighted_normalized_family_selection (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → (Z^Dfirst)≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
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
        (height : rows→ℝ)(Ds : rows→Finset (Ideal O))
        (outer : rows→ℝ)(_houter : ∀r,0≤outer r),
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      ∃pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) ∧ Function.Injective (fun j=>key (pick j)) ∧
        Function.Injective (fun j=>if second then reflectedNonzeroJointLabel (key (pick j)) else key (pick j)) ∧
        (∑r : rows,cost r)≤(D*Z^(2*ε))*(∑j : Finset.univ.image key,cost (pick j)) := by
  have hrows:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  obtain ⟨D,hD,hrows⟩:=hrows
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows] with Z hz
  intro hZ α Label _ _ _ reflected s R seed Dfirst a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf rows second W εmass height Ds outer houter key cost
  have hbnd:=hz hZ reflected s R seed (Z^Dfirst) a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows
  have hsum:=high_family_max_selection key cost (D*Z^(2*ε))
    (by positivity) (fun r=>mul_nonneg
      (mul_nonneg
        (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hK bin _)
        (houter r))
      (high_normalized_row_cost_nonneg second datum r.val (height r) (Ds r))) hbnd
  obtain ⟨pick,hpick,hinjpick,hsum⟩:=hsum
  refine ⟨pick,hpick,hinjpick,?_,hsum⟩
  cases second
  · exact hinjpick
  · intro j k h
    apply hinjpick
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
