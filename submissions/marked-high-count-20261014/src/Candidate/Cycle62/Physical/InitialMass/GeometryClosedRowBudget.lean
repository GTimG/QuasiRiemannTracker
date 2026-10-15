import Candidate.Cycle62.Physical.InitialMass.GeometrySelectedRows
import Candidate.Cycle62.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle62.Physical.InitialMass.GeometryCoarseSupport

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle62Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

/-- Joint row selection for actual geometry, with the coarse frequency bound
derived from the source and retained support. Only the selected joint energy
remains as an analytic input. -/
theorem actual_geometry_closed_row_budget (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
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
      let hunit : ∀l,unit l≠0 := fun l=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r,0≤cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
      (∑r : rows,cost r)≤(D*Z^(2*ε))*E := by
  obtain ⟨D,hD,hrows⟩ := actual_geometry_selected_row_budget N b bs ε
    (Mmax+5*Amax+6*ε) Amax Mmax ξ hb hbs hε (by positivity) hA hM hξ
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows,eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ b ε N
    (zero_lt_one.trans_le hb) hε,
    (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (b^N*bs*bs))] with Z hz hsupport hconstant
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index block label left unit hunit hf rows cost E hcost key hpick
  have hS : sourceRadius s≤Z^(Amax+ε) := by
    calc
      _≤(b^N*bs*bs)*volume s := (radius_bound N b bs bs hb hbs hbs s hcard he).2
      _≤Z^ε*Z^Amax := mul_le_mul hconstant hV (volume_pos s).le (by positivity)
      _=_ := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]
  apply hz hZ reflected s R seed K (3*a) reserve t hK hcard he hV hKM
    hs₁ hs₂ (by positivity) hreserve bin column hinj alloc halloc left u₀ unit hu₀ hunit
    rows cost E _ hcost hpick
  intro r
  let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
    (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
  have hh := hsupport hZ reflected s R seed K ξ a reserve Mmax (Amax+ε) hK hseed hs₁ hs₂
    hS hKM hξ hξε ha hreserve bin (column r.val.val.1.1).val datum label r.val rfl rfl
  dsimp only at hh
  change CenteredMomentSectorLocalization.normValue (jointSourceRow left u₀ unit
    (secondEncodedRow block label r.val))≤_
  convert hh.1 using 1 <;> congr 1 <;> ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_closed_row_budget
