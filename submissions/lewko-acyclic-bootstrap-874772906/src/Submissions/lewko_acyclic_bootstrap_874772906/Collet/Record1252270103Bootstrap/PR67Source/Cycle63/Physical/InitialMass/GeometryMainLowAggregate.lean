import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondProjectorShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLabelDisintegration
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondChildLowPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle63FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate CenteredMomentSourceMass CenteredMomentRankinRadical
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
open Cycle63Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open CenteredMomentWholeDivisorShell
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainLowAggregateSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

universe u v
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum

/-- The occupied first labels and projectors, with no extension of an
allocation to a zero or unsupported ideal. -/
def selectedLowFirstLabels {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) : Finset FirstSourceLabel :=
  Finset.univ.image first

def selectedLowFirstProjectors {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (l : FirstSourceLabel) : Finset (Ideal O) :=
  (Finset.univ.filter (fun j=>first j=l)).image seed

abbrev SelectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O) :=
  (l : selectedLowFirstLabels first) × selectedLowFirstProjectors first seed l.val

def selectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O) (j : Label) :
    SelectedLowFirstPair first seed :=
  ⟨⟨first j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩,
    ⟨seed j,Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩⟩⟩

theorem selected_low_first_pair_bijective {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Function.Bijective (selectedLowFirstPair first seed) := by
  constructor
  · intro j k h
    apply hinj
    exact Prod.ext (congrArg (fun x=>(x.1.val)) h) (congrArg (fun x=>x.2.val) h)
  · intro x
    obtain ⟨j,hj,hseed⟩ := Finset.mem_image.mp x.2.property
    have hfirst : first j=x.1.val := (Finset.mem_filter.mp hj).2
    refine ⟨j,?_⟩
    apply Sigma.ext
    · exact Subtype.ext hfirst
    · apply (Subtype.heq_iff_coe_eq (fun D=>by
        dsimp only [selectedLowFirstPair]
        rw [hfirst])).mpr
      exact hseed

def selectedLowFirstPairEquiv {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Label ≃ SelectedLowFirstPair first seed :=
  Equiv.ofBijective _ (selected_low_first_pair_bijective first seed hinj)

/-- Reindex the entire selected child cost, after the second-label sum has
been formed. The inverse pair index keeps the actual first allocation. -/
theorem selected_low_first_cost_reindex {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel) (cost : Label→FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost j v)=
      ∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first seed l.val,
          ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩),
            cost ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩) v := by
  calc
    _=∑p : SelectedLowFirstPair first seed,
        ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm p),
          cost ((selectedLowFirstPairEquiv first seed hinj).symm p) v :=
      Fintype.sum_equiv (selectedLowFirstPairEquiv first seed hinj) _ _ (fun j=>by simp)
    _=_ := Fintype.sum_sigma _

theorem selected_low_pair_inverse_fields {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (p : SelectedLowFirstPair first seed) :
    first ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.1.val ∧
      seed ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.2.val := by
  have h := (selectedLowFirstPairEquiv first seed hinj).apply_symm_apply p
  exact ⟨congrArg (fun x=>x.1.val) h,congrArg (fun x=>x.2.val) h⟩

def selectedLowSupportedChildren {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel)
    (l : FirstSourceLabel) (D : Ideal O) : Finset FirstSourceLabel :=
  if h : l∈selectedLowFirstLabels first ∧ D∈selectedLowFirstProjectors first seed l then
    children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨⟨l,h.1⟩,⟨D,h.2⟩⟩)
  else ∅

@[simp] theorem selected_low_supported_children_at {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel) (p : SelectedLowFirstPair first seed) :
    selectedLowSupportedChildren first seed hinj children p.1.val p.2.val=
      children ((selectedLowFirstPairEquiv first seed hinj).symm p) := by
  unfold selectedLowSupportedChildren
  rw [dite_eq_left (show p.1.val∈selectedLowFirstLabels first ∧
    p.2.val∈selectedLowFirstProjectors first seed p.1.val from ⟨p.1.property,p.2.property⟩)]

/-- The supported payment domain is exactly the image of selected first
pairs, with the dependent second children retained in every occupied fiber. -/
theorem selected_low_supported_sum {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel)
    (cost : FirstSourceLabel→FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost (first j) v)=
      ∑l∈selectedLowFirstLabels first,∑D∈selectedLowFirstProjectors first seed l,
        ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v := by
  rw [selected_low_first_cost_reindex first seed hinj children (fun j v=>cost (first j) v)]
  calc
    _=∑l : selectedLowFirstLabels first,∑D : selectedLowFirstProjectors first seed l.val,
        ∑v∈selectedLowSupportedChildren first seed hinj children l.val D.val,cost l.val v := by
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun D _ => ?_
      rw [selected_low_supported_children_at first seed hinj children ⟨l,D⟩,
        (selected_low_pair_inverse_fields first seed hinj ⟨l,D⟩).1]
    _=_ := by
      rw [Finset.sum_coe_sort (selectedLowFirstLabels first)
        (fun l=>∑D : selectedLowFirstProjectors first seed l,
          ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)]
      refine Finset.sum_congr rfl fun l _ => ?_
      exact Finset.sum_coe_sort (selectedLowFirstProjectors first seed l)
        (fun D=>∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)

/-- Pay the selected first-pair fibers once. Supported second labels are
summed with their reciprocal norm; the first labels and projector ideals
are reindexed injectively, without an additional first-family count. -/
theorem actual_selected_low_supported_budget (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀{Label : Type*}[Fintype Label]
    (reflected second : Bool)(Z T A p exponent error : ℝ),
    2≤Z → 1≤T → p≤B → ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    ∀(first : Label→FirstSourceLabel)(seed : Label→ Ideal O),
    Function.Injective (fun j=>(first j,seed j)) →
    (∀j,Supported (first j).1.1 ∧ Supported (first j).1.2) →
    (∀j,primeSupport (first j).1.1=primeSupport (first j).1.2) →
    (∀j,seed₀∣(first j).1.1 ∧ seed₀∣(first j).1.2) →
    (∀j,((first j).1.1.absNorm:ℝ)≤Z^B ∧ ((first j).1.2.absNorm:ℝ)≤Z^B) →
    (∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤Z^p) →
    (∀j,lowGeometryExponent reflected Z A (first j)≤exponent) →
    (∀j,Squarefree (seed j)) →
    (∀j,T≤((seed j).absNorm:ℝ) ∧ ((seed j).absNorm:ℝ)<2*T) →
    ∀children : Label→Finset FirstSourceLabel,
    (∀j,∀v∈children j,Supported v.1.1 ∧ Supported v.1.2) →
    (∀j,∀v∈children j,primeSupport v.1.1=primeSupport v.1.2) →
    (∀j,∀v∈children j,seed j∣v.1.1 ∧ seed j∣v.1.2) →
    (∀j,∀v∈children j,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
    (∑j,∑v∈children j,Z^(lowGeometryExponent reflected Z A (first j)+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
      K₀*Z^(p+exponent+error+ε)/(seed₀.absNorm:ℝ) := by
  have hbudget := actual_low_full_label_budget B ε hB hε
  obtain ⟨K₀,hK₀,hbudget⟩ := hbudget
  refine ⟨K₀,hK₀,?_⟩
  intro Label _ reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0 first seed hinj
    hsup heq hseed hnorm hrad hgeom hsq hdyad children hsup₂ heq₂ hseed₂ hnorm₂
  rw [selected_low_supported_sum first seed hinj children
    (fun l v=>Z^(lowGeometryExponent reflected Z A l+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))]
  apply hbudget reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0
    (selectedLowFirstLabels first)
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hsup j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact heq j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hseed j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hnorm j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hrad j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hgeom j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hsq j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hdyad j
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hsup₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact heq₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    have hf := (selected_low_pair_inverse_fields first seed hinj ⟨⟨l,hl⟩,⟨D,hD⟩⟩).2
    simpa only [hf] using hseed₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hnorm₂ _ v hv

/-- Actual selected second blocks pay their child volume and canonical
scalar before the supported reciprocal-norm sum. The common four-dyad
box is paid once, independently of the number of first labels. -/
theorem eventual_actual_selected_low_second_payment
    (N : ℕ) (lo εv : ℝ) (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→ Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(ξ unit M a reserve error εcommon Bnorm : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤Z^Bnorm) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,ActualSecondBlockIndex.IsInactive q.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal unit Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+(unit-M)+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ unit M a reserve error εcommon Bnorm hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox pay
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hpay (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :
      0≤pay l v := by
    dsimp only [pay]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _) (div_nonneg
        (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ (first l)).le
        (volume_pos (src l)).le))
      (mul_nonneg (normalizer_pos _ _ (hgate l v hv).1 _).le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ.le _)
  have hdis := actual_second_joint_positive_disintegration
    (fun l=>liveIndices (alloc l).val) src R seed K Tsec Z ξ rows hU box hbox
    (fun l v _=>pay l v) (fun l v hv _ _=>hpay l v hv)
  apply hdis.trans
  have hpoint : ∀l,∀v∈actualSecondLabels (src l) (R l) (seed l),pay l v≤
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
        error+(unit-M)+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    intro l v hv
    have hg := hgate l v hv
    have hnorm : ((if second then v.1.2 else v.1.1).absNorm:ℝ)≤Z^Bnorm := by
      cases second
      · exact hg.2.2.2.2.2.1.trans (hsource l)
      · exact hg.2.2.2.2.2.2.trans (hsource l)
    exact hz.2 s hn hs reflected second (first l) (hfirst l).1 (hfirst l).2 (heq l)
      Rfirst (alloc l) (χ l) (t l) (halloc l) v.1.1 v.1.2 hg.1 hg.2.1 v.2.val
      unit M a ξ reserve error εcommon Bnorm hecommon hnorm
  calc
    _≤∑_n∈box,∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+(unit-M)+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun l _ => ?_
      exact Finset.sum_le_sum (hpoint l)
    _=_ := by simp

/-- The selected original second scalar sum is fully paid on its finite
supported first-label/projector fibers. -/
theorem eventual_actual_selected_low_second_paid
    (N : ℕ) (lo εv B ε : ℝ) (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧
    ∀ᶠZ : ℝ in atTop,2≤Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→ Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(ξ unit M a reserve error εcommon : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤Z^B) →
    ∀(T p exponent : ℝ),1≤T → p≤B →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤Z^B ∧ ((first l).1.2.absNorm:ℝ)≤Z^B) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
    (∀l,T≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*T) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,ActualSecondBlockIndex.IsInactive q.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal unit Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(K₀*Z^(p+exponent+error+(unit-M)+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ)) := by
  let hbase := actual_selected_low_supported_budget.{0} B ε hB hε
  let K₀ := Classical.choose hbase
  let hlabels := Classical.choose_spec hbase
  refine ⟨K₀,hlabels.1,?_⟩
  filter_upwards [eventual_actual_selected_low_second_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ unit M a reserve error εcommon hseed hw₁ hw₂ hecommon hsource
    T p exponent hT hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hdyad
    rows hU box hbox pay
  have hpaid := hz.2 s hn hs reflected second first hfirst heq Rfirst alloc χ t halloc
    R seed K Tsec ξ unit M a reserve error εcommon B hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hbound := hlabels.2 (Label:=Label) reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+(unit-M)+εv+B*εcommon) hZ2 hT hp seed₀ hs₀ hs₀0 first seed hinj hfirst heq
    hfirstseed hfirstnorm hrad hgeom hseed hdyad
    (fun l=>actualSecondLabels (src l) (R l) (seed l))
    (fun l v hv=>⟨(hgate l v hv).1,(hgate l v hv).2.1⟩)
    (fun l v hv=>(hgate l v hv).2.2.1)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.1,(hgate l v hv).2.2.2.2.1⟩)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.2.2.1.trans (hsource l),
      (hgate l v hv).2.2.2.2.2.2.trans (hsource l)⟩)
  have hexp : p+exponent+(error+(unit-M)+εv+B*εcommon)+ε=
      p+exponent+error+(unit-M)+εv+B*εcommon+ε := by ring
  rw [hexp] at hbound
  apply hpaid.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg box.card)
  simpa only [src,K₀,add_assoc] using hbound

/-- The actual second-projector union pays the low theorem's shell-scale
factor once, uniformly before all moving block labels and allocations. -/
theorem actual_second_low_weighted_shells (N : ℕ)(U εshell ε : ℝ)
    (hU : 0≤U)(heshell : 0≤εshell)(he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{Label : Type*}[Fintype Label](d : Label→SecondInputDatum α),
    (∀l,Fintype.card (d l).slots≤N) →
    (∀l i I,I∈(d l).input.pools i→(I.absNorm:ℝ)≤Z^U) →
    (∑n∈selectedShells (sharedProjectors (fun l=>(d l).block.divisors)),
      (2*dyadicScale n)^(3*εshell))≤
        C*Z^(ε+3*(((N:ℝ)+2)*U)*εshell) := by
  have hbound := actual_second_projector_shell_subpower (α:=α) N U ε hU he
  obtain ⟨C₀,hC₀,hbound⟩ := hbound
  refine ⟨C₀*(2:ℝ)^(3*εshell),mul_pos hC₀ (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ d hN hpool
  let L := ((N:ℝ)+2)*U
  let shells := selectedShells (sharedProjectors (fun l=>(d l).block.divisors))
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hpower : 0≤3*εshell := mul_nonneg (by norm_num) heshell
  have hscale (n : ℤ)(hn : n∈shells) : dyadicScale n≤Z^L :=
    (shared_projector_shell_scale (fun l=>(d l).block.divisors) Z L
      (fun l D hD=>(second_datum_projector_cap (d l) N Z U (hN l) hz.1.le hU
        (hpool l) D hD).2) n hn).2
  have hp (n : ℤ)(hn : n∈shells) :
      (2*dyadicScale n)^(3*εshell)≤(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := by
    calc
      _≤(2*Z^L)^(3*εshell) := Real.rpow_le_rpow (mul_nonneg (by norm_num) (dyadicScale_pos n).le)
        (mul_le_mul_of_nonneg_left (hscale n hn) (by norm_num)) hpower
      _=_ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ.le _),
          ←Real.rpow_mul hZ.le]
        congr 1
        ring_nf
  calc
    _≤∑_n∈shells,(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := Finset.sum_le_sum hp
    _=(shells.card:ℝ)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) := by simp
    _≤(C₀*Z^ε)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) :=
      mul_le_mul_of_nonneg_right (hz.2 d hN hpool) (by positivity)
    _=_ := by dsimp only [L]; rw [Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
