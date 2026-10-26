/- Copyright (c) 2026 Sil. Apache-2.0.
Actual first retained cutoff, positive dyadic enlargement, and sharp
fixed-f second physical radius, with its full source-support constant.
No prime-amplification, energy estimate, or desired source gate is assumed.
-/
import Candidate.FourthPower.OuterFreshSelected
import Candidate.FourthPower.OuterFreshSource
import Candidate.FourthPower.OuterFreshNonexceptionalFamily
import Candidate.FourthPower.MixedFirstCutoffs
import Candidate.FourthPower.OuterFreshDeclaredRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshCutoffAllowance
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open CenteredMomentFirstScale CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open CenteredMomentSecondHeightFamily CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical
open CenteredMomentSecondRadicalBudget CenteredMomentSecondChildRadialWidth
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstLiveRemainders MixedOriginalNormCap
open MixedFirstExceptionalNormalization MixedFirstExceptionalWindow MixedFirstGeometricCaps
open MixedFirstCutoffs MixedSupplierFourthRow MixedSupplierSource
open MixedFirstLiveSource MixedLiveNormalization MixedCommonCoefficient
open MixedFirstNonexceptionalAllocation
open OuterFreshSource OuterFreshSelected OuterFreshNonexceptionalFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def effectiveVolume (s : Source ι a b) : ℝ := sourceVolume s/pairNorm s.d

theorem effectiveVolume_pos (s : Source ι a b) : 0<effectiveVolume s :=
  div_pos (sourceVolume_pos s) (pairNorm_pos s.hd.1 s.hd.2)

/-- Actual genuine-common extraction supplies the logarithmic source
discrepancy used below. Its premise is the literal nonzero frozen
coefficient, not a new asserted capacity/volume bound. -/
theorem first_allocation_error (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools s) G) (Z : ℝ) (hZ : 1<Z)
    (hfrozen : frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0) :
    Real.logb Z (effectiveVolume (allocatedLiveSource s hb cover G B))-
      Real.logb Z (sourceVolume s)+Real.logb Z (G.absNorm:ℝ)≤
        (Fintype.card ι:ℝ)*Real.logb Z (2:ℝ) := by
  let hB:=(allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hprod:=(Finset.mem_filter.mp B.property).2
  have hP:∀i,0<s.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hr:=rawReduction_pos B.val hB s.P hP
  have hnorm:=(actual_reduction_norm B.val hB G s.R hprod s.ν s.Wslot s.P hP
    1 2 zero_lt_one s.hW hfrozen).2
  rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hnorm
  have hn:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (ideal_norm_one_le hG)) hnorm
  rw [Real.logb_mul (by positivity : (0:ℝ)<2^Fintype.card ι).ne' hr.ne',
    Real.logb_pow] at hn
  have hv:=live_volume_ratio B.val hB s.d s.T s.P hP
  change (s.T*(∏i : liveIndices B.val,s.P i.val)) /
    pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))=
    ((s.T*∏i,s.P i)/pairNorm s.d)/rawReduction B.val s.P at hv
  have he:effectiveVolume (allocatedLiveSource s hb cover G B)=
      effectiveVolume s/rawReduction B.val s.P := by
    change (s.X₁*s.X₂*(∏i : liveIndices B.val,s.P i.val)) /
      pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))=
      ((s.X₁*s.X₂*∏i,s.P i)/pairNorm s.d)/rawReduction B.val s.P
    rw [s.hpX]
    exact hv
  have hpair:1≤pairNorm s.d := by
    exact one_le_mul_of_one_le_of_one_le (ideal_norm_one_le s.hd.1) (ideal_norm_one_le s.hd.2)
  have hV:effectiveVolume s≤sourceVolume s:=div_le_self (sourceVolume_pos s).le hpair
  have hl:=Real.logb_le_logb_of_le hZ (effectiveVolume_pos s) hV
  rw [he,Real.logb_div (effectiveVolume_pos s).ne' hr.ne']
  linarith

def capConstant (b : ℝ) (N : ℕ) : ℝ := max 1 (b^2*(2:ℝ)^N)

theorem capConstant_pos (b : ℝ) (N : ℕ) : 0<capConstant b N :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem capConstant_mono (b : ℝ) {n N : ℕ} (h : n≤N) : capConstant b n≤capConstant b N :=
  max_le_max_left 1 (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) h) (sq_nonneg b))

/-- Actual sharp support envelope; its constant is uniform over all
source subtypes of bounded cardinality, regardless of their slot values. -/
def secondSourceEnvelope (s : Source ι a b) : ℝ :=
  capConstant b (Fintype.card ι)*effectiveVolume s

/-- This is the actual second Poisson scale. Its comparison required
by the checked tail estimate is equality with X=secondSourceEnvelope.
The support constant must not be omitted from this scale. -/
def secondSourceCutoff (s : Source ι a b) (L : ℝ) : ℝ := secondSourceEnvelope s^2/L

theorem second_cutoff_exact (s : Source ι a b) (L : ℝ) (hL : 0<L) :
    0<secondSourceCutoff s L ∧ secondSourceEnvelope s^2/L≤secondSourceCutoff s L ∧
    sourceNormCap s.P b s.T s.d≤secondSourceEnvelope s := by
  have he:0<secondSourceEnvelope s:=mul_pos (capConstant_pos b _) (effectiveVolume_pos s)
  refine ⟨div_pos (sq_pos_of_pos he) hL,le_rfl,?_⟩
  rw [source_cap_factored]
  unfold secondSourceEnvelope effectiveVolume sourceVolume
  rw [s.hpX]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (div_nonneg (mul_nonneg s.total_pos.le (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))))
      (pairNorm_pos s.hd.1 s.hd.2).le)

/-- Choosing the literal local nominal scale gives Csec=1. The
opposite common norm is at least one, hence the actual D0 floor. -/
theorem actual_retained_deficit (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z ξ : ℝ) (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (n : ℤ)
    (hn : Retained (frequencyRadius (firstCutoff C D E K V) Z ξ) n) :
    -frequencyLoss Z 1 ξ≤deficit C D E K V Z n := by
  have hh:=retained_deficit C D _ (subsetGenerator_supported C D hC E).1
    Z K V (firstCutoff C D E K V) 1 ξ hZ hK hV (by norm_num)
    (by simp only [firstCutoff,one_mul]; exact le_rfl) n hn
  rw [commonPart_of_equal_support D C hD.1 hCD.symm] at hh
  have hd:=Real.logb_nonneg hZ (ideal_norm_one_le hD.1)
  change Real.logb Z (D.absNorm:ℝ)-frequencyLoss Z 1 ξ≤deficit C D E K V Z n at hh
  linarith

/-- The required first row enlargement is already a positive annular
majorant. No inverse-prime amplification or new error family is needed. -/
theorem actual_annular_radius (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (hZ : 1<Z) (hpad : 2≤Z^κ) (n : ℤ) :
    2*dyadicScale n≤nominalChildScale C D E K V Z κ n :=
  annular_scale_le C D E K V Z κ hZ hpad n

def frozenVolume (q : Data ι) : ℝ := ∏i : ↥q.Lᶜ,q.P i.val

theorem frozenVolume_pos (q : Data ι) (hP : ∀i,0<q.P i) : 0<frozenVolume q :=
  Finset.prod_pos (fun i _=>hP i.val)

/-- Exact three-way product partition, including an empty selection. -/
theorem volume_partition (q : Data ι) :
    (∏i,q.P i)=frozenVolume q*selectedVolume q*(∏j : RestIndex q,q.P j.val.val) := by
  have h₁: (∏i : {i // i∉q.Lᶜ},q.P i.val)*frozenVolume q=(∏i,q.P i) := by
    have hLive:(∏i : {i // i∉q.Lᶜ},q.P i.val)=∏i∈Finset.univ\q.Lᶜ,q.P i:=
      (Finset.prod_subtype (F:=inferInstance) (p:=fun i=>i∉q.Lᶜ)
        (Finset.univ\q.Lᶜ) (by simp) q.P).symm
    rw [hLive,frozenVolume,Finset.prod_coe_sort q.Lᶜ q.P]
    exact Finset.prod_sdiff (Finset.subset_univ q.Lᶜ) (f:=q.P)
  have h₂: (∏j : RestIndex q,q.P j.val.val)*selectedVolume q=
      (∏i : {i // i∉q.Lᶜ},q.P i.val) := by
    have hRest:(∏j : RestIndex q,q.P j.val.val)=
        ∏j∈Finset.univ\q.J,q.P j.val:=
      (Finset.prod_subtype (F:=inferInstance) (p:=fun j=>j∉q.J)
        (Finset.univ\q.J) (by simp) (fun j=>q.P j.val)).symm
    rw [hRest,selectedVolume,Finset.prod_coe_sort q.J (fun j=>q.P j.val)]
    exact Finset.prod_sdiff (Finset.subset_univ q.J) (f:=fun j=>q.P j.val)
  rw [←h₁,←h₂]
  ring

/-- The actual residual source has the SAME full ordinary prefix.
Frozen and selected marked volumes are each removed exactly once. -/
theorem residual_effective_volume (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J)) :
    effectiveVolume (residualSource s ha cover u L J x)*
      frozenVolume (supplierData s ha u L J)*selectedVolume (supplierData s ha u L J)=
      effectiveVolume s := by
  have hp:=volume_partition (supplierData s ha u L J)
  change (∏i,s.P i)=frozenVolume (supplierData s ha u L J)*
      selectedVolume (supplierData s ha u L J)*
      (∏j : RestIndex (supplierData s ha u L J),s.P j.val.val) at hp
  change (s.X₁*s.X₂*(∏j : RestIndex (supplierData s ha u L J),s.P j.val.val)/pairNorm s.d)*
      frozenVolume (supplierData s ha u L J)*selectedVolume (supplierData s ha u L J)=
      s.X₁*s.X₂*(∏i,s.P i)/pairNorm s.d
  rw [hp]
  ring

/-- Linear fixed-f conductor cost, using ACTUAL nonzero supplier
weights. The only enlargement is the fixed number of dyadic slot factors. -/
theorem actual_frozen_window (s : Source ι a b) (ha : 0<a)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0) :
    frozenVolume (supplierData s ha u L J)≤
      ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ) ∧
    ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)≤
      (2:ℝ)^Fintype.card ↥Lᶜ*frozenVolume (supplierData s ha u L J) := by
  have hprod : ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)=
      ∏i : ↥Lᶜ,((x i).val.absNorm:ℝ) := by
    simp only [frozenProduct,map_prod,Nat.cast_prod]
    rfl
  constructor
  · rw [hprod]
    apply Finset.prod_le_prod₀ (fun i _=>zero_le_one.trans (s.hP i.val))
    intro i hi
    have hI:=frozen_slot_mem s ha u L J x hx i
    have ham : amplitude (supplierData s ha u L J) i.val (x i)≠0 :=
      Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
    have hW : s.Wslot i.val (((x i).val.absNorm:ℝ)/s.P i.val)≠0 := by
      intro he
      apply ham
      simp only [amplitude,MixedSupplierSplit.slotAmplitude,supplierData,if_pos hI,he,mul_zero]
    have hlo:1≤((x i).val.absNorm:ℝ)/s.P i.val := (s.hW i.val hW).1
    change s.P i.val≤((x i).val.absNorm:ℝ)
    simpa only [one_mul] using
      (le_div_iff₀ (zero_lt_one.trans_le (s.hP i.val))).mp hlo
  ·
   calc
    _=(∏i : ↥Lᶜ,((x i).val.absNorm:ℝ)) := hprod
    _≤∏i : ↥Lᶜ,2*s.P i.val := Finset.prod_le_prod₀
      (fun i _=>Nat.cast_nonneg _) (fun i _=>(s.hpn i.val _ (frozen_slot_mem s ha u L J x hx i)).2)
    _=_ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,frozenVolume,supplierData]

/-- Exact source log identity. The first genuine allocation error e is
DEFINED from the real source; it is not an assumed physical-width bound.
The common-allocation adapter bounds e from the literal nonzero allocation. -/
theorem actual_cutoff_log_identity (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (Jsel : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L Jsel))
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (hK : 0<K) (hV : 0<V) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (n : ℤ) :
    let q:=supplierData s ha u L Jsel
    let r:=residualSource s ha cover u L Jsel x
    let w:=Real.logb Z (frozenVolume q)
    let d:=Real.logb Z (selectedVolume q)
    let c:=Real.logb Z (C.absNorm:ℝ)
    let j:=deficit C D E K V Z n-c
    let e:=Real.logb Z (effectiveVolume s)-Real.logb Z V+c
    Real.logb Z (secondSourceCutoff r (nominalChildScale C D E K V Z κ n))+
      Real.logb Z (τ.modulus.absNorm:ℝ)+w-
      2*Real.logb Z (capConstant b (Fintype.card (RestIndex q)))=
      (inputWidth η K Z-w)+j-max j 0-2*d-κ+2*e := by
  dsimp only
  have hz:=zero_lt_one.trans hZ
  have hp: ∀i,0<(supplierData s ha u L Jsel).P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hf:=frozenVolume_pos (supplierData s ha u L Jsel) hp
  have hd:=selectedVolume_pos (supplierData s ha u L Jsel) hp
  have hr:=effectiveVolume_pos (residualSource s ha cover u L Jsel x)
  have hv:=residual_effective_volume s ha cover u L Jsel x
  have hlog:=congrArg (Real.logb Z) hv
  rw [Real.logb_mul (mul_pos hr hf).ne' hd.ne',Real.logb_mul hr.ne' hf.ne'] at hlog
  have hn:=actual_nominal_log η τ C D hC hD hCD E K V Z hK hV hZ hmod
  rw [secondSourceCutoff,secondSourceEnvelope,nominalChildScale,Real.logb_div
    (sq_pos_of_pos (mul_pos (capConstant_pos b _) hr)).ne'
    (Real.rpow_pos_of_pos hz _).ne',Real.logb_pow,
    Real.logb_mul (capConstant_pos b _).ne' hr.ne',Real.logb_rpow hz hZ.ne']
  unfold deficit
  norm_num only [Nat.cast_ofNat]
  linarith only [hlog,hn]

private theorem cubic_constant_pos : 0<(ReferenceCubicCharacter.conductorConstant:ℝ) := by
  have h₁:=zero_lt_one.trans_le (ideal_norm_one_le (HeckeUnitRows.character (1:Oˣ)).modulus_ne_bot)
  have h₂:=zero_lt_one.trans_le (ideal_norm_one_le
    (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₃:0<((Ideal.span {(72:O)}).absNorm:ℝ):=
    zero_lt_one.trans_le (ideal_norm_one_le (by simp))
  unfold ReferenceCubicCharacter.conductorConstant
  push_cast
  exact mul_pos (mul_pos h₁ h₂) h₃

/-- ALL terms here are fixed before the moving ideals, selected product,
profiles, physical labels and Z. No N(f) is included in this constant. -/
def presentationLoss (b Z : ℝ) (N : ℕ) : ℝ :=
  Real.logb Z (4*(fixedFactor:ℝ))+
  Real.logb Z (ReferenceCubicCharacter.conductorConstant:ℝ)+
  Real.logb Z fixedPresentationCost+(N:ℝ)*Real.logb Z (2:ℝ)+
  2*Real.logb Z (capConstant b N)

theorem presentation_loss_eventually (b : ℝ) (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ presentationLoss b Z N≤ε := by
  let C:ℝ:=4*(fixedFactor:ℝ)*(ReferenceCubicCharacter.conductorConstant:ℝ)*
    fixedPresentationCost*2^N*(capConstant b N)^2
  have hF:0<(fixedFactor:ℝ):=by exact_mod_cast fixedFactor_pos
  have hCubic:=cubic_constant_pos
  have hPresentation:=fixedPresentationCost_pos
  have hCap:=capConstant_pos b N
  have hC:0<C:=by dsimp only [C];positivity
  have hc:∀ᶠZ : ℝ in atTop,C≤Z^ε:=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) C
  filter_upwards [hc,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  have hl:=Real.logb_le_logb_of_le hZ hC hc
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  have he:Real.logb Z C=presentationLoss b Z N := by
    dsimp only [C,presentationLoss]
    simp (disch := positivity) only [Real.logb_mul,Real.logb_pow]
    ring
  rwa [he] at hl

/-- Composed literal cutoff allowance. The genuine-first-source error
is its EXACT logarithmic volume discrepancy e. Actual common allocation
gives e<=card*log_Z 2. The second cutoff is constructed from the actual
residual source, and its full fixed-f modulus cost is paid linearly.
No physical-width bound or child-energy estimate occurs as a premise. -/
theorem actual_physical_width (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (Jsel : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L Jsel))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L Jsel) x≠0)
    (η τ : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z κ ξ₂ : ℝ) (hK : 0<K) (hV : 0<V) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (n : ℤ) (C₂ D₂ : Id) (U : Finset (CommonIndex C₂ D₂)) :
    let q:=supplierData s ha u L Jsel
    let r:=residualSource s ha cover u L Jsel x
    let w:=Real.logb Z (frozenVolume q)
    let d:=Real.logb Z (selectedVolume q)
    let c:=Real.logb Z (C.absNorm:ℝ)
    let j:=deficit C D E K V Z n-c
    let e:=Real.logb Z (effectiveVolume s)-Real.logb Z V+c
    let R₂:=(inputWidth η K Z-w)+j-max j 0-2*d-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    OuterFreshDeclaredRadius.physicalWidth τ (frozenProduct q x) C₂ D₂ U
      (frequencyRadius (secondSourceCutoff r (nominalChildScale C D E K V Z κ n)) Z ξ₂) Z≤
      R₂-κ+2*e+ξ₂/2+presentationLoss b Z (Fintype.card ι) := by
  dsimp only
  have hz:=zero_lt_one.trans hZ
  have hp:∀i,0<(supplierData s ha u L Jsel).P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hf:=frozenVolume_pos (supplierData s ha u L Jsel) hp
  have hfn:0<((frozenProduct (supplierData s ha u L Jsel) x).absNorm:ℝ):=
    zero_lt_one.trans_le (ideal_norm_one_le (frozen_nonzero _ x))
  have htw:0<secondSourceCutoff (residualSource s ha cover u L Jsel x)
      (nominalChildScale C D E K V Z κ n):=
    (second_cutoff_exact _ _ (Real.rpow_pos_of_pos hz _)).1
  have hlog:=actual_cutoff_log_identity s ha cover u L Jsel x η τ C D hC hD hCD E
    K V Z κ hK hV hZ hmod n
  dsimp only at hlog
  have hfw:=Real.logb_le_logb_of_le hZ hfn (actual_frozen_window s ha u L Jsel x hx).2
  rw [Real.logb_mul (by positivity : (0:ℝ)<2^Fintype.card ↥Lᶜ).ne' hf.ne',
    Real.logb_pow] at hfw
  have hcard:Fintype.card ↥Lᶜ≤Fintype.card ι:=Fintype.card_le_of_injective
    (fun i : ↥Lᶜ=>i.val) Subtype.val_injective
  have hdim:(Fintype.card ↥Lᶜ:ℝ)*Real.logb Z (2:ℝ)≤
      (Fintype.card ι:ℝ)*Real.logb Z (2:ℝ):=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.logb_nonneg hZ (by norm_num))
  have hcap:=Real.logb_le_logb_of_le hZ (capConstant_pos b _)
    (capConstant_mono b (rest_card_le (supplierData s ha u L Jsel)))
  unfold OuterFreshDeclaredRadius.physicalWidth presentationLoss
  rw [frequencyRadius,Real.logb_mul htw.ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_rpow hz hZ.ne']
  push_cast
  rw [Real.logb_mul cubic_constant_pos.ne' hfn.ne']
  linarith

end
end Candidate.FourthPower.OuterFreshCutoffAllowance

