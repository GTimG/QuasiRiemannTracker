import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainNormalized
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorColumnFamily
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorScalarPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss ActualEisensteinCubic
open Cycle63Moment Cycle63FinalError CenteredMomentPrimeElements
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedRows ConcretePrimeRowBridge
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondInputCapacitySource
open CenteredMomentFirstScale CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon Cycle63FinalErrorCapacity
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open CenteredMomentCommonProfile CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic
open CenteredMomentAmplificationErrorEnergy CenteredMomentSecondBlockAggregate
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open Filter CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationActiveFactor
local instance errorNormalizedDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Negation preserves the actual retained source disk and radial filter. -/
theorem actual_error_source_rows_neg (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (R : ℝ) (z : O) :
    -z∈sourceRows C D U R ↔ z∈sourceRows C D U R := by
  have hn (w : O) : normValue (-w)=normValue w := by
    rw [normValue_eq_embedding,normValue_eq_embedding]
    simp
  unfold sourceRows liveRows retainedRows
  simp only [Finset.mem_filter,mem_rowNormDisk,mul_neg,hn,Ideal.span_singleton_neg]

/-- The right physical column uses the same complete ordinary set after
negating its row; the fixed inducing filter retains both ray characters. -/
theorem actual_error_ordinary_rows_neg (η : Character) (χ ψ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)})
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (z : O) :
    -z∈partRows false η ψ Q fixedBadMask C D U R ↔
      z∈partRows false η χ Q fixedBadMask C D U R := by
  constructor
  · intro hz
    have hn := geometry_nonexceptional_pair η ψ χ⁻¹ χ⁻¹ Q hQ fixedBadMask
      (dvd_mul_right _ _)
      (dvd_mul_left _ _) C D U R (-z) hz
    apply Finset.mem_filter.mpr
    refine ⟨(actual_error_source_rows_neg C D U R z).mp (Finset.mem_filter.mp hz).1,?_⟩
    simpa only [Bool.false_eq_true,ite_false,inv_inv,neg_neg] using hn.2
  · intro hz
    have hn := geometry_nonexceptional_pair η χ ψ⁻¹ ψ⁻¹ Q hQ fixedBadMask
      (dvd_mul_right _ _)
      (dvd_mul_left _ _) C D U R z hz
    apply Finset.mem_filter.mpr
    refine ⟨(actual_error_source_rows_neg C D U R z).mpr (Finset.mem_filter.mp hz).1,?_⟩
    simpa only [Bool.false_eq_true,ite_false,inv_inv] using hn.2

/-- Complete ordinary columns dominate the full positive live-row sum.
Residual projectors and both rays remain inside the label sum. -/
theorem actual_error_ordinary_normalized_columns {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ap≤x)
    (χ₀ : Label→RayCharacter) (Q : Ideal O) (reflected : Bool) (t u : ℝ) :
    let datum := fun l=>ordinarySecondDatum (d l) (χ₀ l) Q fixedBadMask
    secondNormalizedSum reflected datum
      (secondEffectiveWeight (fun l=>(datum l).block) w W) t u≤
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        (‖w l‖*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈partRows false (d l).input.η (χ₀ l) Q fixedBadMask
            (d l).C (d l).D (d l).inactive (d l).radius,
            (if reflected then
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z)‖^2
             else
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z‖^2) := by
  intro datum
  apply (actual_main_effective_normalized_columns N a ap ha hap datum w W
    hcard hlower hW₁ hW₂ reflected t u).trans
  refine Finset.sum_le_sum fun l hl => Finset.sum_le_sum fun χ hχ => Finset.sum_le_sum fun ψ hψ => ?_
  let c := ‖w l‖*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive
  have hc : 0≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (div_nonneg (d l).K_pos.le (lowerFactor_pos N a ap ha hap).le))
      (normalizer_pos (d l).C (d l).D (d l).hC (d l).inactive).le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun D hD => ?_
  let f := fun z : O=>
    if reflected then
      ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
        ((d l).input.t+2*Real.pi*(u-(-t))))
        (d l).D (d l).hD (d l).R (d l).seed D (-z)‖^2
    else
      ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
        ((d l).input.t+2*Real.pi*(u-t)))
        (d l).C (d l).hC (d l).R (d l).seed D z‖^2
  have hf : ∀z,0≤f z := by intro z; dsimp only [f]; split_ifs <;> exact sq_nonneg _
  change (∑z∈secondLiveColumnRows (datum l).block,c*f z.val)≤ c*∑z∈(datum l).block.rows,f z
  rw [←Finset.sum_coe_sort (datum l).block.rows f,Finset.mul_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun z _ _=>mul_nonneg hc (hf z.val))

/-- The actual extracted-prime coefficient, before either common norm
payment or prime cardinality cancellation. -/
def errorNormalizedCoefficient (P : Finset (Ideal O)) (weight V : ℝ)
    (p : O) (i : Fin 3) : ℝ :=
  (56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i)/V

theorem error_normalized_coefficient_nonneg (P : Finset (Ideal O)) (weight V : ℝ)
    (hw : 0≤weight) (hV : 0<V) (p : O) (i : Fin 3) :
    0≤errorNormalizedCoefficient P weight V p i := by
  unfold errorNormalizedCoefficient
  have hcost := localErrorCost_nonneg p (errorIndex i)
  positivity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Choose the actual live common allocation from the original physical
block, once before the full ordinary column and all shifted heights. -/
theorem actual_geometry_error_live_common_allocation (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂) (second : Bool) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      frozenCoefficient B₂.val (if second then d.D else d.C) d.R
        d.input.ν d.input.W d.input.P≠0 := by
  intro d
  have hs := actual_geometry_error_seed_gates reflected s R seed Z Mrow amp ξ reserve b t N
    hZ bin q p i Bp υ v hw₁ hw₂ n.val
  have hseed : d.seed∣(if second then d.D else d.C) := by
    cases second
    · exact hs.1
    · exact hs.2
  have hne : d.block.value ballProfile≠0 := (Finset.mem_filter.mp n.property).2
  exact actual_second_input_live_allocation d second hseed ballProfile hne

/-- A different finite extraction menu may be chosen at each first
projector. Unioning its second labels pays that menu's cardinality once. -/
theorem actual_error_dependent_projector_reciprocal (B ε : ℝ)
    (hB : 0≤B) (he : 0<ε) :
    ∃Ks : ℝ,0<Ks ∧ ∀(second : Bool)(Z T : ℝ),2≤Z → 1≤T →
    ∀(Ds : Finset (Ideal O)),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(β : Ds→Type*)[∀D,Fintype (β D)](children : (D : Ds)→β D→Finset FirstSourceLabel)
      (n : ℕ),
      (∀D,Fintype.card (β D)≤n) →
      (∀D b,∀v∈children D b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀D b,∀v∈children D b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀D b,∀v∈children D b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀D b,∀v∈children D b,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑D : Ds,∑b : β D,∑v∈children D b,
        1/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤(n:ℝ)*(Ks*Z^ε) := by
  have hpay := actual_low_reciprocal_projector_shell B ε hB he
  obtain ⟨Ks,hKs,hpay⟩ := hpay
  refine ⟨Ks,hKs,?_⟩
  intro second Z T hZ hT Ds hDs hdyad β _ children n hcard hsup heq hdiv hnorm
  let union : Ideal O→Finset FirstSourceLabel := fun D=>
    if h : D∈Ds then Finset.univ.biUnion (children ⟨D,h⟩) else ∅
  have hmem (D : Ds)(v : FirstSourceLabel) :
      v∈union D.val ↔ ∃b : β D,v∈children D b := by
    simp only [union,dite_eq_left D.property,Finset.mem_biUnion,Finset.mem_univ,true_and]
  have hh := hpay second Z T hZ hT Ds hDs hdyad union
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hsup ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact heq ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hdiv ⟨D,hD⟩ b v hb)
    (fun D hD v hv=>by obtain ⟨b,hb⟩ := (hmem ⟨D,hD⟩ v).mp hv; exact hnorm ⟨D,hD⟩ b v hb)
  have hpoint (D : Ds) :
      (∑b : β D,∑v∈children D b,1/((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
        (n:ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
    have hn : 0≤∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by positivity
    calc
      _ ≤ ∑_b : β D,∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
        refine Finset.sum_le_sum fun b _ => ?_
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun v hv=>(hmem D v).mpr ⟨b,hv⟩)
        intro v _ _
        positivity
      _ = (Fintype.card (β D):ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard D) hn
  calc
    _ ≤ ∑D : Ds,(n:ℝ)*(∑v∈union D.val,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) :=
      Finset.sum_le_sum (fun D _=>hpoint D)
    _ = (n:ℝ)*(∑D∈Ds,∑v∈union D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
      rw [←Finset.sum_coe_sort Ds (fun D : Ideal O=>
        ∑v∈union D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)),Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

variable [Cycle63.AffineLedger] in
/-- Genuine extracted payment with the first allocation chosen separately
at every first residual projector. The original seed is not replaced by
that projector; its saving is provided by the second-label shell sum. -/
theorem eventual_actual_error_projector_dependent_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (he : 0<ε) :
    ∃Ks : ℝ,0<Ks ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
    ∀(reflected second : Bool)(l : FirstSourceLabel),
      Supported l.1.1 → Supported l.1.2 → primeSupport l.1.1=primeSupport l.1.2 →
    ∀(T error εcommon unit M a δ reserve : ℝ),1≤T → 0≤εcommon →
    ∀(Ds : Finset (Ideal O)),(∀D∈Ds,Squarefree D) →
      (∀D∈Ds,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : Ds→actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
      (χ : Ds→ Character)(t : ℝ),
      (∀D,frozenCoefficient (alloc D).val (if reflected then l.1.2 else l.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u := fun D=>child s (if reflected then l.1.2 else l.1.1) Rfirst (alloc D) (χ D) t
    ∀(p : O)(k : ℕ),p≠0 → Prime (Ideal.span {p}) →
      (∀D,∀j I,I∈(u D).slots j→ IsCoprime (Ideal.span {p}) I) →
    let Bps := fun D=>errorLiftedActiveAllocations (u D) (Ideal.span {p}) k
    ∀(υ : (D : Ds)→Bps D→ Character)(vheight : ℝ)
      (children : (D : Ds)→Bps D→Finset FirstSourceLabel),
      (∀D b,∀v∈children D b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀D b,∀v∈children D b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀D b,∀v∈children D b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀D b,∀v∈children D b,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        extractedErrorLabelScalar reflected second l v Z unit M a δ reserve error εcommon
          (volume s) (volume (child (u D) ((Ideal.span {p})^k)
            (Rfirst*(if reflected then l.1.2 else l.1.1))
            Bp.val (υ D Bp) vheight)) p k)≤
      Ks*(k+1:ℝ)*Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon+ε-unit*branchReserve k) := by
  have hpay := actual_error_dependent_projector_reciprocal B ε hB he
  obtain ⟨Ks,hKs,hpay⟩ := hpay
  refine ⟨Ks,hKs,?_⟩
  filter_upwards [eventual_actual_twice_error_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq T error εcommon unit M a δ reserve
    hT hecommon Ds hDs hdyad Rfirst alloc χ t halloc u p k hp hprime hslot Bps υ vheight
    children hsup heq₂ hdiv hnorm
  have hZ : 0<Z := by linarith
  have halloccount (D : Ds) : Fintype.card (Bps D)≤k+1 := by
    have hh := actual_amplification_allocations_card (u D).pools (Ideal.span {p}) hprime k
      (by intro j I hI; exact ⟨(u D).pools_ne _ _ hI,hslot D j I hI⟩)
    have hsub : (errorLiftedActiveAllocations (u D) (Ideal.span {p}) k).card≤
        (actualAllocations (u D).pools ((Ideal.span {p})^k)).card :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
    dsimp only [Bps]
    rw [Fintype.card_coe]
    exact hsub.trans hh
  let exponent := lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
    error+εv+B*εcommon-unit*branchReserve k
  have hpoint (D : Ds)(Bp : Bps D)(v : FirstSourceLabel)(hv : v∈children D Bp) :
      extractedErrorLabelScalar reflected second l v Z unit M a δ reserve error εcommon
        (volume s) (volume (child (u D) ((Ideal.span {p})^k)
          (Rfirst*(if reflected then l.1.2 else l.1.1)) Bp.val (υ D Bp) vheight)) p k≤
      Z^exponent/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    have hm := hz.2 s hcard hlow reflected second l hC hD heq Rfirst (alloc D) (χ D) t
      (halloc D) p hp k (hslot D) Bp.val (υ D Bp) vheight
      v.1.1 v.1.2 (hsup D Bp v hv).1 (hsup D Bp v hv).2 v.2.val
      M a δ reserve (error-unit*branchReserve k) εcommon B hecommon (by
        cases second
        · exact (hnorm D Bp v hv).1
        · exact (hnorm D Bp v hv).2)
    convert hm using 1 <;>
      (dsimp only [extractedErrorLabelScalar,exponent,u,CenteredMomentAmplificationChildSourceCaps.twiceChild]; try ring_nf)
  have hsum := hpay second Z T hZ2 hT Ds hDs hdyad (fun D=>↥(Bps D)) children (k+1)
    halloccount hsup heq₂ hdiv hnorm
  simp only [Nat.cast_add,Nat.cast_one] at hsum
  calc
    _ ≤ ∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        Z^exponent/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      refine Finset.sum_le_sum fun D _ => Finset.sum_le_sum fun Bp _ => ?_
      exact Finset.sum_le_sum (fun v hv=>hpoint D Bp v hv)
    _ = Z^exponent*(∑D : Ds,∑Bp : Bps D,∑v∈children D Bp,
        1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
      simp only [Finset.mul_sum,mul_one_div]
    _ ≤ Z^exponent*((k+1:ℝ)*(Ks*Z^ε)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hZ.le _)
    _ = _ := by
      rw [show lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon+ε-unit*branchReserve k=exponent+ε by dsimp [exponent]; ring,
        Real.rpow_add hZ]
      ring

set_option backward.isDefEq.respectTransparency false in
variable [Cycle63.AffineLedger] in
/-- Original first-label counting and exact prime averaging after the
projector-dependent extraction payment. The two seeds remain distinct. -/
theorem eventual_actual_error_dependent_full_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (he : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon unit M a δ reserve : ℝ),
      1≤T → p≤B → 0≤εcommon →
    ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
    ∀(Ds : labels→Finset (Ideal O)),(∀l D,D∈Ds l→Squarefree D) →
      (∀l D,D∈Ds l→T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : labels)→Ds l→actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1))
      (χ : (l : labels)→Ds l→ Character)(t : ℝ),
      (∀l D,frozenCoefficient (alloc l D).val (if reflected then l.val.1.2 else l.val.1.1)
        Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc l D).val) := fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l D) (χ l D) t
    ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
      (∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→ IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l D q i→ Character)
      (vheight : ℝ)
      (children : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l D q i→Finset FirstSourceLabel),
      (∀l D q i ψ b,∀v∈children l D q i ψ b,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,D.val∣v.1.1 ∧ D.val∣v.1.2) →
      (∀l D q i ψ b,∀v∈children l D q i ψ b,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        ∑l : labels,∑ψ : RayCharacter,∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
          extractedErrorLabelScalar reflected second l.val v Z unit M a δ reserve error εcommon
            (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
            q.val (errorIndex i+1))≤
      K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ)*
        ∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*Z^(-unit*branchReserve (errorIndex i+1)) := by
  have hfirst := actual_first_low_label_count B (ε/2) hB (half_pos he)
  obtain ⟨Kf,hKf,hfirst⟩ := hfirst
  obtain ⟨Ks,hKs,hsecond⟩ := eventual_actual_error_projector_dependent_payment N lo εv B (ε/2)
    hlo hev hB (half_pos he)
  let Kray : ℝ := Fintype.card RayCharacter
  have hKray : 0<Kray := by dsimp [Kray]; exact_mod_cast Fintype.card_pos
  refine ⟨56*Kray*Kf*Ks,by positivity,?_⟩
  filter_upwards [hsecond] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon unit M a δ reserve hT hp hecommon
    seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Ds hDs hdyad Rfirst alloc χ t halloc
    u P hne hprime hbad hslot Bps υ vheight children hsup₂ heq₂ hdiv hnorm₂
  have hZ : 0<Z := by linarith [hz.1]
  have hcount := hfirst Z (by linarith [hz.1]) p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpair (l : labels)(q : elementPool P)(i : Fin 3)(ψ : RayCharacter) :
      (∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
        extractedErrorLabelScalar reflected second l.val v Z unit M a δ reserve error εcommon
          (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
          q.val (errorIndex i+1))≤
      Ks*(errorIndex i+2:ℝ)*Z^(exponent+error+εv+B*εcommon+ε/2-unit*branchReserve (errorIndex i+1)) := by
    have hq := elementPool_data P hprime hbad q.val q.property
    have hh := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1
      (hsup l.val l.property).2 (heq l.val l.property) T error εcommon unit M a δ reserve hT hecommon
      (Ds l) (hDs l) (hdyad l) Rfirst (alloc l) (χ l) t (halloc l)
      q.val (errorIndex i+1) hq.1.ne_zero (hprime _ hq.2.1) (fun D=>hslot l D q)
      (fun D=>υ l D q i ψ) vheight (fun D=>children l D q i ψ)
      (fun D=>hsup₂ l D q i ψ) (fun D=>heq₂ l D q i ψ) (fun D=>hdiv l D q i ψ)
      (fun D=>hnorm₂ l D q i ψ)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [show (errorIndex i:ℝ)+1+1=(errorIndex i:ℝ)+2 by ring] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hz.1])
    linarith [hgeom l.val l.property]
  have htotal (q : elementPool P)(i : Fin 3) :
      (∑l : labels,∑ψ : RayCharacter,∑D : Ds l,∑Bp : Bps l D q i,∑v∈children l D q i ψ Bp,
        extractedErrorLabelScalar reflected second l.val v Z unit M a δ reserve error εcommon
          (volume s) (volume (child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight))
          q.val (errorIndex i+1))≤
      Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
        Z^(-unit*branchReserve (errorIndex i+1)) := by
    let E := Ks*(errorIndex i+2:ℝ)*Z^(exponent+error+εv+B*εcommon+ε/2-unit*branchReserve (errorIndex i+1))
    calc
      _ ≤ ∑_l : labels,∑_ψ : RayCharacter,E :=
        Finset.sum_le_sum (fun l _=>Finset.sum_le_sum (fun ψ _=>hpair l q i ψ))
      _ = (labels.card:ℝ)*(Kray*E) := by simp [Kray]
      _ ≤ (Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Kray*E) :=
        mul_le_mul_of_nonneg_right hcount (by dsimp [E]; positivity)
      _ = _ := by
        dsimp [E]
        simp only [Real.rpow_add hZ,Real.rpow_sub hZ]
        have heps : Z^ε=Z^(ε/2)*Z^(ε/2) := by rw [←Real.rpow_add hZ,add_halves]
        rw [heps,neg_mul,Real.rpow_neg hZ.le]
        ring
  have hpcount : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hprime hbad]
  have hpc : (0:ℝ)<P.card := by exact_mod_cast hne.card_pos
  calc
    _ ≤ (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        (Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-unit*branchReserve (errorIndex i+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun q _=>Finset.sum_le_sum
        (fun i _=>mul_le_mul_of_nonneg_left (htotal q i) (by positivity)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hpcount,Finset.mul_sum]
      field_simp
      refine Finset.sum_congr rfl fun i hi => ?_
      ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
