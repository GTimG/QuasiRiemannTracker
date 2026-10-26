import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighNormalizedPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryCoarseSidePayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowQuantitativePayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local instance geometryMainHighQuantitativeSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

section CanonicalPartition
open RayFourExpansion ConcretePrimeRowBridge CenteredMomentSourceMass Cycle63Moment.LowBranch
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- The high row keeps the low partition's literal buffered choice when
its actual retained state is widened. -/
theorem actual_main_high_canonical_row_admission
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1<Z) (hbΦ : 2≤bΦ) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (z : mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)) :
    let base : NaturalState Z Bmask 2 :=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let st:=widenHighState base bΦ hbΦ
    let keep:=(actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
      Z Bmask hZ second hP hPN (fun _=>True) z.val z.property).1
    1≤(st.radial.profile (normValue z.val/st.radial.scale)).re ∧
    st.radial.profile (normValue z.val/st.radial.scale)≠0 ∧ z.val≠0 ∧
    GeometryZeroBin M H hH st η₀ hQM hQη z.val keep e T
      (mainLowCanonicalSelector M H hH d χ₀ χ ψ Q hQ m hm hml hm2 Z Bmask hZ second
        hP hPN η₀ hQM hQη e T he hT hβlo hβhi z) := by
  intro base st keep
  have ha:=actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  have hw : 1≤(st.radial.profile (normValue z.val/st.radial.scale)).re:=ha.2.2
  have hn : st.radial.profile (normValue z.val/st.radial.scale)≠0:=by
    intro h; rw [h] at hw; norm_num at hw
  have hb:=actual_main_low_canonical_zero_bin M H hH d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN η₀ hQM hQη e T he hT hβlo hβhi z
  exact ⟨hw,hn,st.row_ne_zero _ keep,
    main_high_widen_zero_bin M H hH base bΦ hbΦ η₀ hQM hQη z.val keep e T _ hb⟩

variable [Cycle63.AffineLedger] in
/-- Every ordinary live row uses the literal shared selector before any shell restriction. -/
theorem actual_main_high_canonical_family_admission
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1<Z) (hbΦ : 2≤bΦ) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let rows:=secondLiveRows (fun l=>(ordinary l).block)
    let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
    let base:=fun r : rows=>retainedState Z Bmask hZ
      (if second then (d r.val.1).τ r.val.2.2.1⁻¹ else (d r.val.1).τ r.val.2.1) Q
      ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
      (hP r.val.1) (hPN r.val.1)
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let st:=fun r=>widenHighState (base r) bΦ hbΦ
    let select:=mainLowFamilyCanonicalSelector M H hH d χ₀ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi
    ∃keep : ∀r : rows,(st r).radial.keep (signed r),∀r : rows,
      1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
      (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧ signed r≠0 ∧
      GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e T (select r) := by
  intro ordinary rows signed base st select
  let sourceRow : (r : rows)→mainLowSourceRows second (ordinary r.val.1) (fun _=>True) := fun r=>
    (⟨signed r,by
      apply (mem_main_low_source_rows second (ordinary r.val.1) (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩ :
      mainLowSourceRows second (ordinary r.val.1) (fun _=>True))
  obtain ⟨keep,oldSelect,hold⟩ := actual_main_high_widened_selector M H hH d χ₀ Q hQ m hm hml hm2
    Z Bmask bΦ hZ hbΦ second hP hPN η₀ hQM hQη e T he hT hβlo hβhi
  refine ⟨keep,?_⟩
  intro r
  have hg := actual_main_high_canonical_row_admission M H hH (d r.val.1) (χ₀ r.val.1)
    r.val.2.1 r.val.2.2.1 Q hQ m hm hml hm2 Z Bmask bΦ hZ hbΦ second
    (hP r.val.1) (hPN r.val.1) η₀ hQM hQη e T he hT hβlo hβhi (sourceRow r)
  exact ⟨(hold r).1,(hold r).2.1,(hold r).2.2.1,hg.2.2.2⟩

end CanonicalPartition

private theorem geometry_high_coarse_sum_association {ι : Type*} (rows : Finset ι)
    {m k n l q : rows→ℝ} {A : ℝ}
    (h : (∑r : rows,m r*(k r*n r/l r)*q r)≤A) :
    (∑r : rows,m r*k r*n r/l r*q r)≤A := by
  convert h using 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The all-projector source estimate retains the first physical mass and
restores its side factor only in the coarse exponent. -/
def MainHighCoarseSideSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset (secondLiveRows (fun q=>(datum q).block)))(second : Bool)(W : 𝓢(ℝ,ℂ))
        (height : rows→ℝ)(Ds : rows→Finset (Ideal O))(control B₁ B₂ : ℝ),
      0≤ control → 0≤B₁ → 0≤B₂ →
      (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (firstIndex r.val.val.1.1).1.val *
        (firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
          (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex r.val.val.1.1).1.val)/
          volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
          (firstIndex r.val.val.1.1)))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap*
        highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤K*control*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        Z^exponent

theorem actual_main_high_original_coarse_side_payment {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,
      MainHighCoarseSideSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  let coarse : ℝ := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε
  let Cside : ℝ := geometrySupportConstant N lo ap ap
  have hside : 0<Cside := geometrySupportConstant_pos N lo ap ap hlo hap hap
  let receipt := actual_geometry_main_all_projector_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  let Kc := Classical.choose receipt
  have hKc := (Classical.choose_spec receipt).1
  have hcoarse := (Classical.choose_spec receipt).2
  refine ⟨Kc*(1+Cside⁻¹^2),by positivity,?_⟩
  filter_upwards [hcoarse] with Z hc
  unfold MainHighCoarseSideSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs cost
  classical
  have hraw := hc hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin (fun l=>(firstIndex l).1) hinj (fun l=>(firstIndex l).2) halloc
    rows second W height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs
  have hraw' := geometry_high_coarse_sum_association rows hraw
  by_cases hr : rows.Nonempty
  · obtain ⟨r,hr⟩ := hr
    have hunit := actual_geometry_coarse_side_unit reflected Cside hside s R seed
      (Z^Dfirst) Z ξ B hZ.le hB hseed hs₁ hs₂ hsource bin (firstIndex r.val.1.1).1.val.1
    exact geometry_coarse_side_bound reflected Cside Z B coarse _ Kc control bin
      (zero_lt_one.trans hZ) hKc.le hcontrol hunit hraw'
  · have hzero : (∑r : rows,cost r)=0 := by
      apply Finset.sum_eq_zero
      intro r _
      exact False.elim (hr ⟨r.val,r.property⟩)
    rw [hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcontrol)
      (geometry_high_factor_pos reflected Cside bin hside).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
