/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryHighWeightedSelection
import Candidate.Cycle63.Moment.JointHighDensity

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63HighResidual ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondEnergySplit CenteredMomentFirstAmplificationChoice
local instance mainOrdinaryFiberSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- An injective change of key cannot enlarge a fiber, including the literal
reflected nonzero joint label. -/
theorem main_injective_key_fiber {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→Key) (f : Key→Key) (hf : Function.Injective f) (W : ℝ) (hW : 0≤W)
    (hbound : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W) :
    ∀k,((Finset.univ.filter (fun r=>f (key r)=k)).card:ℝ)≤W := by
  intro k
  by_cases hex : ∃r,f (key r)=k
  · obtain ⟨r₀,hr₀⟩:=hex
    have he (r : Row) : f (key r)=k ↔ key r=key r₀ := by
      rw [←hr₀]
      exact hf.eq_iff
    simp only [he]
    exact hbound (key r₀)
  · have he (r : Row) : f (key r)≠k := fun h=>hex ⟨r,h⟩
    simp only [he,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
    exact hW

/-- Transfer the full original fiber certificate to any ordinary subset
through the exact row inclusion, without asking its restricted block to be
nonzero. The original finite image is the sole larger family. -/
theorem main_ordinary_key_fiber
    {α Label Key : Type*} [Fintype α] [DecidableEq α] [Fintype Label] [DecidableEq Key]
    (d : Label→SecondInputDatum α) (χ : Label→RayCharacter) (Q : Label→ Ideal O) (m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (key : secondLiveRows (fun l=>(d l).block)→Key) (W : ℝ)
    (hfull : ∀rows : Finset (secondLiveRows (fun l=>(d l).block)),∀k,
      ((Finset.univ.filter (fun r : rows=>key r.val=k)).card:ℝ)≤W)
    (rows : Finset (secondLiveRows
      (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))) :
    ∀k,((Finset.univ.filter (fun r : rows=>
      key (ordinaryHighOriginalRow d χ Q m hrows r.val)=k)).card:ℝ)≤W := by
  let embed:=ordinaryHighOriginalRow d χ Q m hrows
  let image:=rows.image embed
  let into : rows→image:=fun r=>⟨embed r.val,Finset.mem_image.mpr ⟨r.val,r.property,rfl⟩⟩
  have hinj : Function.Injective into := by
    intro r s h
    apply Subtype.ext
    exact ordinary_high_original_row_injective d χ Q m hrows (congrArg Subtype.val h)
  exact high_restricted_key_fiber into hinj (fun r : image=>key r.val) W (hfull image)

/-- The restricted and original nonzero encodings agree even when their
nonzero proofs were obtained through different physical admission receipts. -/
theorem ordinary_main_nonzero_key_eq
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α)(χ : Label→RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (first : Label→FirstSourceLabel) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first (ordinaryHighOriginalRow d χ Q m hrows r))≠0)
    (ho : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block) first r)≠0) :
    secondEncodedNonzeroRow (fun l=>(d l).block) first
      (ordinaryHighOriginalRow d χ Q m hrows r) left u₀ unit hf=
    secondEncodedNonzeroRow (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)
      first r left u₀ unit ho := by
  apply Subtype.ext
  dsimp only [secondEncodedNonzeroRow,secondEncodedRow,ordinarySecondDatum,ordinaryHighOriginalRow,
    SecondInputDatum.block,originalSecondBlock]

theorem actual_geometry_main_ordinary_row_fiber_bound (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0<K),
      Squarefree seed → Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → K≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
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
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(χ₀ : Index→RayCharacter)(Q : Index→ Ideal O)(m : Index→O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) (χ₀ q) (Q q) (m q)
      let fullRows : ∀q,(datum q).rows=sourceRows (datum q).C (datum q).D (datum q).inactive (datum q).radius := fun _=>rfl
      let embed:=ordinaryHighOriginalRow datum χ₀ Q m fullRows
      ∀(rows : Finset (secondLiveRows (fun q=>(ordinary q).block))),
      (∀r∈rows,(datum r.val.1).block.value ballProfile≠0) →
      ∀second : Bool,
      let key := fun r : rows=>secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : rows=>
        (if second then reflectedNonzeroJointLabel (key r) else key r)=target)).card:ℝ)≤D*Z^(2*ε) := by
  have hbase:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  obtain ⟨D,hD,hbase⟩:=hbase
  refine ⟨D,hD,?_⟩
  filter_upwards [hbase] with Z hz
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf χ₀ Q m ordinary fullRows embed rows _hnonzero second key target
  have hfull:=hz hZ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc
  have hraw:=main_ordinary_key_fiber datum χ₀ Q m fullRows
    (fun r=>secondEncodedNonzeroRow block label r left u₀ unit (hf r)) (D*Z^(2*ε)) hfull rows
  cases second
  · exact hraw target
  · apply main_injective_key_fiber key reflectedNonzeroJointLabel _ (D*Z^(2*ε)) (by positivity) hraw target
    intro j k h
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

end
end OAI.SevenEighths.Cycle63InitialMass
