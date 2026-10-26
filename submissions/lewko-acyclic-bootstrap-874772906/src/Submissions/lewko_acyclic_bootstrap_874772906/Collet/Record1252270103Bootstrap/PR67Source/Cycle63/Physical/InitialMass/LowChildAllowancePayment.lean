import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowAggregate
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSelectedRadicalBudget
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildLabelGate
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The payment of the second labels of the selected low columns with the allowance of the labels: the pay of a second
label times the allowance is at most `Z` to the exponent of the first label with its surplus over the norm of the common
radical of the second label, and the sums over the first and the second labels are paid by the pointwise budget of the
labels. Released under Apache 2.0. -/
set_option autoImplicit false
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
local instance lowChildAllowanceSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local irreducible] actualSecondLabels

/-- A pay bounded by `Z^a / E` times the allowance `Z` to `sur + (log E - log rad)` is bounded by `Z^(a + sur) / rad`:
the factor `E` of the allowance cancels the reciprocal norm of the own second ideal. -/
theorem allowance_pointwise {Z E rad pay0 a sur : ℝ} (hZ : 1<Z) (hE : 0<E) (hrad : 0<rad)
    (h : pay0≤Z^a/E) :
    pay0*Z^(sur+(Real.logb Z E-Real.logb Z rad))≤Z^(a+sur)/rad := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hexp : Z^(sur+(Real.logb Z E-Real.logb Z rad))=Z^sur*E/rad := by
    rw [Real.rpow_add hZ0,Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hE,Real.rpow_logb hZ0 hZ.ne' hrad]
    ring
  rw [hexp,Real.rpow_add hZ0]
  have hsur : 0≤Z^sur := Real.rpow_nonneg hZ0.le _
  calc pay0*(Z^sur*E/rad)=(pay0*E)*Z^sur/rad := by ring
    _≤(Z^a/E*E)*Z^sur/rad := by
        gcongr
    _=Z^a*Z^sur/rad := by rw [div_mul_cancel₀ _ hE.ne']

/-- A summand with the allowance is the summand over the reciprocal norm of the common radical: the exponent
`log E - log rad` of the allowance turns the reciprocal norm of the own second ideal into that of the radical. -/
theorem allowance_term {Z E rad g e : ℝ} (hZ : 1<Z) (hE : 0<E) (hrad : 0<rad) :
    Z^(g+(e+(Real.logb Z E-Real.logb Z rad)))/E=Z^(g+e)/rad := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hexp : Z^(g+(e+(Real.logb Z E-Real.logb Z rad)))=Z^(g+e)*E/rad := by
    rw [← add_assoc,Real.rpow_add hZ0,Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hE,
      Real.rpow_logb hZ0 hZ.ne' hrad]
    ring
  rw [hexp]
  field_simp

/-- Actual selected second blocks pay their child volume and canonical scalar, times the allowance of their labels,
before the supported sum over the reciprocal norm of the common radical. The common four-dyad box is paid once. -/
theorem eventual_selected_low_allowance_payment
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
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)*
        Z^(lowAllowance Z (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 (if second then v.1.2 else v.1.1))
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+(unit-M)+εv+Bnorm*εcommon)/((commonRadical v.1.1 v.1.2).absNorm:ℝ)) := by
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ unit M a reserve error εcommon Bnorm hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox pay
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hradpos (v : FirstSourceLabel) :
      0<((commonRadical v.1.1 v.1.2).absNorm:ℝ) :=
    CenteredMomentFirstScale.norm_pos (commonRadical v.1.1 v.1.2) (commonRadical_ne_zero _ _)
  have hpay (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :
      0≤pay l v := by
    dsimp only [pay]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _) (div_nonneg
        (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ (first l)).le
        (volume_pos (src l)).le))
      (mul_nonneg (normalizer_pos _ _ (hgate l v hv).1 _).le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ.le _))
      (Real.rpow_nonneg hZ.le _)
  have hdis := actual_second_joint_positive_disintegration
    (fun l=>liveIndices (alloc l).val) src R seed K Tsec Z ξ rows hU box hbox
    (fun l v _=>pay l v) (fun l v hv _ _=>hpay l v hv)
  apply hdis.trans
  have hpoint : ∀l,∀v∈actualSecondLabels (src l) (R l) (seed l),pay l v≤
      Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+
        error+(unit-M)+εv+Bnorm*εcommon)/((commonRadical v.1.1 v.1.2).absNorm:ℝ) := by
    intro l v hv
    have hg := hgate l v hv
    have hnorm : ((if second then v.1.2 else v.1.1).absNorm:ℝ)≤Z^Bnorm := by
      cases second
      · exact hg.2.2.2.2.2.1.trans (hsource l)
      · exact hg.2.2.2.2.2.2.trans (hsource l)
    have hE : 0<((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      cases second
      · exact CenteredMomentFirstScale.norm_pos v.1.1 hg.1.1
      · exact CenteredMomentFirstScale.norm_pos v.1.2 hg.2.1.1
    have hbase := hz.2 s hn hs reflected second (first l) (hfirst l).1 (hfirst l).2 (heq l)
      Rfirst (alloc l) (χ l) (t l) (halloc l) v.1.1 v.1.2 hg.1 hg.2.1 v.2.val
      unit M a ξ reserve error εcommon Bnorm hecommon hnorm
    have h := allowance_pointwise (sur:=lowSurplus Z (if reflected then (first l).1.2 else (first l).1.1)
      (if reflected then (first l).1.1 else (first l).1.2)) hz.1 hE (hradpos v) hbase
    have hexp : lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+error+(unit-M)+εv+
        Bnorm*εcommon+lowSurplus Z (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2)=
        lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+error+(unit-M)+εv+Bnorm*εcommon := by
      unfold lowAllowedExponent
      ring
    rw [hexp] at h
    exact h
  calc
    _≤∑_n∈box,∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+(unit-M)+εv+Bnorm*εcommon)/((commonRadical v.1.1 v.1.2).absNorm:ℝ) := by
      refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun l _ => ?_
      exact Finset.sum_le_sum (hpoint l)
    _=_ := by simp

/-- The selected second blocks with the allowance of their labels are fully paid on the finite supported first-label
and projector fibers: the sum is at most the box times the pointwise budget of the labels, with the exponent
`lowAllowedExponent` of the first labels bounded by `exponent`. -/
theorem eventual_selected_low_allowance_paid
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
    (∀l,lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
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
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)*
        Z^(lowAllowance Z (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 (if second then v.1.2 else v.1.1))
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(K₀*Z^(p+exponent+error+(unit-M)+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ)) := by
  obtain ⟨K₀,hK₀,hbudget⟩ := actual_selected_low_supported_pointwise_budget.{0} B ε hB hε
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [eventual_selected_low_allowance_payment N lo εv hlo hev,
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
  have hE (l : Label) (v : FirstSourceLabel) (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :
      0<((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    have hg := hgate l v hv
    cases second
    · exact CenteredMomentFirstScale.norm_pos v.1.1 hg.1.1
    · exact CenteredMomentFirstScale.norm_pos v.1.2 hg.2.1.1
  have hradpos (v : FirstSourceLabel) : 0<((commonRadical v.1.1 v.1.2).absNorm:ℝ) :=
    CenteredMomentFirstScale.norm_pos (commonRadical v.1.1 v.1.2) (commonRadical_ne_zero _ _)
  have hZ1 : 1<Z := by linarith
  let e : ℝ := error+(unit-M)+εv+B*εcommon
  have hbound := hbudget (Label:=Label) second Z T p exponent e hZ2 hT hp seed₀ hs₀ hs₀0 first seed hinj hfirst heq
    hfirstseed hfirstnorm hrad (fun f=>lowAllowedExponent reflected Z (Real.logb Z (volume s)) f)
    (fun _ v=>e+(Real.logb Z ((if second then v.1.2 else v.1.1).absNorm:ℝ)-
      Real.logb Z ((commonRadical v.1.1 v.1.2).absNorm:ℝ)))
    hgeom hseed hdyad
    (fun l=>actualSecondLabels (src l) (R l) (seed l))
    (fun l v hv=>⟨(hgate l v hv).1,(hgate l v hv).2.1⟩)
    (fun l v hv=>(hgate l v hv).2.2.1)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.1,(hgate l v hv).2.2.2.2.1⟩)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.2.2.1.trans (hsource l),
      (hgate l v hv).2.2.2.2.2.2.trans (hsource l)⟩)
    (fun l v hv=>by
      have h := allowance_term (g:=0) (e:=e) hZ1 (hE l v hv) (hradpos v)
      simp only [zero_add] at h
      exact h.le)
  have hconv : (∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
      Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+
        (e+(Real.logb Z ((if second then v.1.2 else v.1.1).absNorm:ℝ)-
          Real.logb Z ((commonRadical v.1.1 v.1.2).absNorm:ℝ))))/
        ((if second then v.1.2 else v.1.1).absNorm:ℝ))=
      ∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+e)/
          ((commonRadical v.1.1 v.1.2).absNorm:ℝ) := by
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun v hv => ?_
    exact allowance_term hZ1 (hE l v hv) (hradpos v)
  have hexp : p+exponent+e+ε=p+exponent+error+(unit-M)+εv+B*εcommon+ε := by
    dsimp only [e]; ring
  rw [hexp] at hbound
  have hbound' : (∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
      Z^(lowAllowedExponent reflected Z (Real.logb Z (volume s)) (first l)+
        error+(unit-M)+εv+B*εcommon)/((commonRadical v.1.1 v.1.2).absNorm:ℝ))≤
      K₀*Z^(p+exponent+error+(unit-M)+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ) := by
    have h := hbound
    rw [hconv] at h
    simpa only [e,add_assoc] using h
  apply hpaid.trans
  exact mul_le_mul_of_nonneg_left hbound' (Nat.cast_nonneg box.card)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
