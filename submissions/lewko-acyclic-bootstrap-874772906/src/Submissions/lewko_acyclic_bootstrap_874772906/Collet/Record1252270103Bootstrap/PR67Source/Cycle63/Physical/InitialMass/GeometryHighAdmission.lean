import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryClosedRowBudget
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.State
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope

/-- A larger support ceiling preserves the literal retained state. -/
def widenHighState {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ)(hbΦ : 2≤bΦ) : NaturalState Z Bmask bΦ :=
  { st with
    radial_support := by
      intro x hx
      exact (st.radial_support hx).trans hbΦ }

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
  have hrows := actual_geometry_closed_row_budget η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  obtain ⟨D,hD,hrows⟩ := hrows
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

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
