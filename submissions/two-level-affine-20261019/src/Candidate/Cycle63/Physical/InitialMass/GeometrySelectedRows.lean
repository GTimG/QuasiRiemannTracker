import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.SecondEncodedGates
import Candidate.Cycle63.Moment.JointHighDensity

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic

/-- The selected actual first common children feed the second joint-row
bound. All source-radius, cutoff, seed and dyad gates are derived from the
original source; distinct joint rows remain for the density estimate. -/
theorem actual_geometry_selected_row_budget (N : ℕ)(b bs ε Brow Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)(hBrow : 0≤Brow)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K sigma reserve t : ℝ)(hK : 0<K),
      Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → K≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ sigma → 0≤ reserve →
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
      let Kmain := firstMainRadius reflected K (volume s) Z ξ sigma reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ sigma reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2).block
      let label := fun q : Index=>first q.1
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)(hu₀ : u₀≠0)(hunit : ∀l,unit l≠0),
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow block label r.val)}).absNorm:ℝ)≤Z^Brow) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
      (∑r : rows,cost r)≤(D*Z^(2*ε))*E := by
  have hrows := actual_retained_source_row_budget Brow (Amax+ε) (Mmax+ξ/2) (b^(2*N)) ε
    hBrow (by positivity) (by positivity) (by positivity) hε
  obtain ⟨D,hD,hrows⟩ := hrows
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows,eventual_geometry_child_source_cap N b bs ε hb hbs hε] with Z hz hchild
  intro hZ α Label _ _ _ reflected s R seed K sigma reserve t hK hcard he hV hKM
    hs₁ hs₂ hsigma hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index block label left u₀ unit hu₀ hunit hf rows cost E hnorm hcost key hpick
  exact hz.2 slots source (fun l=>R*C l) projector hprojector hz₁ hz₂ first Kmain Tsec ξ
    (Z^(Amax+ε)) hKm hinj
    (fun l=>hchild.2 s Amax hcard he hV (C l) R (alloc l) (χ l) t (halloc l)) le_rfl
    (fun l=>actual_geometry_main_cutoff_cap reflected s R seed K Z ξ sigma reserve b Mmax N
      hK hZ (zero_lt_one.trans_le hb) hξ hsigma hreserve hKM bin (column l).val)
    left u₀ unit hf rows cost E hnorm hcost hpick

end
end OAI.SevenEighths.Cycle63InitialMass
