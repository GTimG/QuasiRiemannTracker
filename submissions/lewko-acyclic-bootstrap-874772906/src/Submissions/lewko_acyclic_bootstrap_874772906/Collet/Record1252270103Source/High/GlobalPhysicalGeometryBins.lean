/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified common geometry bins, adapted from pinned Cycle61 geometry. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRatioCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryBins

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
open OAI OAI.SevenEighths Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance modifiedGeometryBinsSumDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
/-- Actual equal-support first labels are already their full common parts.
This aligns the raw label norms with the exact normalization exponents. -/
lemma actual_labels_commonPart (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) :
    commonPart q.1.val.1 q.1.val.2=q.1.val.1 ∧
      commonPart q.1.val.2 q.1.val.1=q.1.val.2 := by
  have hg := CenteredMomentFirstSectors.commonLabels_data _ _ _ _ q.1.property
  constructor
  · have he : commonPart q.1.val.1 q.1.val.2=commonPart q.1.val.1 q.1.val.1 := by
      unfold commonPart commonSupport
      rw [←hg.2.2]
    exact he.trans (commonPart_self _ hg.1)
  · have he : commonPart q.1.val.2 q.1.val.1=commonPart q.1.val.2 q.1.val.2 := by
      unfold commonPart commonSupport
      rw [hg.2.2]
    exact he.trans (commonPart_self _ hg.2.1)

/-- The five literal norms: c,d,p,R,E, in the order used by normalization. -/
def geometryIdeals (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) : Fin 5→Ideal O :=
  ![q.1.val.1,q.1.val.2,commonRadical q.1.val.1 q.1.val.2,
    Ideal.span {activeConductor q.1.val.1 q.1.val.2},
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}]

def geometryNorms (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) (i : Fin 5) : ℝ :=
  (geometryIdeals s modifier R seed K Z ξ q i).absNorm

def geometryExponents (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) (i : Fin 5) : ℝ :=
  Real.logb Z (geometryNorms s modifier R seed K Z ξ q i)

def geometryIndex (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) : Fin 5→ℤ :=
  fun i=>⌊Real.logb 2 (geometryNorms s modifier R seed K Z ξ q i)⌋

def geometryBins (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) : Finset (Fin 5→ℤ) :=
  Finset.univ.image (geometryIndex s modifier R seed K Z ξ)

def commonGeometryKey (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : SourceCoordinate s modifier R seed K Z ξ) : ℤ×(Fin 5→ℤ) :=
  (sourceRatioIndex s modifier R seed K Z ξ q,geometryIndex s modifier R seed K Z ξ q)

def commonGeometryBins (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ) : Finset (ℤ×(Fin 5→ℤ)) :=
  Finset.univ.image (commonGeometryKey s modifier R seed K Z ξ)

abbrev CommonGeometryFiber (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (key : ℤ×(Fin 5→ℤ)) :=
  {q : SourceCoordinate s modifier R seed K Z ξ // commonGeometryKey s modifier R seed K Z ξ q=key}

omit [DecidableEq ι] in
lemma commonGeometryFiber_ratio (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s modifier R seed K Z ξ key) :
    sourceRatioIndex s modifier R seed K Z ξ q.val=key.1 := congrArg Prod.fst q.property

/-- Exact grouped physical mass; both ratio and common geometry stay in the
fiber, while every original first label remains inside the joint sum. -/
theorem actual_physical_mass_geometry_groups (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s modifier R seed
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ =
    ∑key∈commonGeometryBins s modifier R seed K Z ξ,
      ‖∑q : CommonGeometryFiber s modifier R seed K Z ξ key,
        normPhase (coordinateBlock s modifier R seed W K Z ξ q.val)*
          coordinateBlock s modifier R seed W K Z ξ q.val‖ := by
  rw [actual_physical_mass_joint_sum]
  simp_rw [normPhase_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  simp_rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q∈(Finset.univ : Finset (SourceCoordinate s modifier R seed K Z ξ))) =>
      Finset.mem_image_of_mem (commonGeometryKey s modifier R seed K Z ξ) hq)]
  apply Finset.sum_congr rfl
  intro key _
  exact Finset.sum_subtype (Finset.univ.filter (fun q : SourceCoordinate s modifier R seed K Z ξ=>
    commonGeometryKey s modifier R seed K Z ξ q=key))
    (fun q=>by simp) (fun q=>‖coordinateBlock s modifier R seed W K Z ξ q‖)

omit [DecidableEq ι] in
lemma actual_geometry_norm_caps (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (q : SourceCoordinate s modifier R seed K Z ξ)
    (i : Fin 5) : 1≤geometryNorms s modifier R seed K Z ξ q i ∧
      geometryNorms s modifier R seed K Z ξ q i≤Z^B := by
  have hg := actual_common_gates s modifier R seed hs hz₁ hz₂ q.1.val.1 q.1.val.2 q.1.property
  have hc := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed)) _ _ q.1.property).1
  have hf := original_factor_caps q.1.val.1 q.1.val.2 hc q.2.1.val
  rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span] at hf
  have one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  fin_cases i
  · change (1:ℝ)≤q.1.val.1.absNorm ∧ (q.1.val.1.absNorm:ℝ)≤Z^B
    exact ⟨one _ hg.1,hg.2.2.2.2.2.1.trans hsource⟩
  · change (1:ℝ)≤q.1.val.2.absNorm ∧ (q.1.val.2.absNorm:ℝ)≤Z^B
    exact ⟨one _ hg.2.1,hg.2.2.2.2.2.2.trans hsource⟩
  · change (1:ℝ)≤(commonRadical q.1.val.1 q.1.val.2).absNorm ∧
      ((commonRadical q.1.val.1 q.1.val.2).absNorm:ℝ)≤Z^B
    exact ⟨one _ (commonRadical_ne_zero _ _),
      (divisor_norm_le _ _ hg.1 ((commonRadical_dvd_commonPart _ _).trans
        (commonPart_dvd _ _ hg.1))).trans (hg.2.2.2.2.2.1.trans hsource)⟩
  · change (1:ℝ)≤(Ideal.span {activeConductor q.1.val.1 q.1.val.2}).absNorm ∧
      ((Ideal.span {activeConductor q.1.val.1 q.1.val.2}).absNorm:ℝ)≤Z^B
    exact ⟨one _ (Ideal.span_singleton_eq_bot.not.mpr (finitePrimeModulus_ne_zero _)),
      hf.2.trans (hg.2.2.2.2.2.1.trans hsource)⟩
  · change (1:ℝ)≤(Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}).absNorm ∧
      ((Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}).absNorm:ℝ)≤Z^B
    exact ⟨one _ (subsetGenerator_supported _ _ hc _).1,
      hf.1.trans (hg.2.2.2.2.2.1.trans hsource)⟩

/-- One log2 bin has width exactly log_Z 2 in exponent coordinates. -/
lemma log_norm_bin_range (Z n : ℝ) (hZ : 1<Z) (_hn : 0<n) :
    (⌊Real.logb 2 n⌋:ℝ)*Real.logb Z 2≤Real.logb Z n ∧
      Real.logb Z n<((⌊Real.logb 2 n⌋:ℝ)+1)*Real.logb Z 2 := by
  have hwidth : 0<Real.logb Z 2 := by
    unfold Real.logb
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos hZ)
  have he : Real.logb Z n=Real.logb 2 n*Real.logb Z 2 := by
    unfold Real.logb
    field_simp
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right (Int.floor_le _) hwidth.le,
    mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) hwidth⟩

omit [DecidableEq ι] in
lemma actual_geometry_fiber_range (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1<Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s modifier R seed K Z ξ key) (i : Fin 5) :
    (key.2 i:ℝ)*Real.logb Z 2≤geometryExponents s modifier R seed K Z ξ q.val i ∧
      geometryExponents s modifier R seed K Z ξ q.val i<((key.2 i:ℝ)+1)*Real.logb Z 2 := by
  have hn := actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource q.val i
  have he := congrFun (congrArg Prod.snd q.property) i
  have hh := log_norm_bin_range Z _ hZ (zero_lt_one.trans_le hn.1)
  simpa only [geometryExponents,geometryIndex,commonGeometryKey] using he ▸ hh

omit [DecidableEq ι] in
lemma geometry_indices_enclosure (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1≤Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B) (q : SourceCoordinate s modifier R seed K Z ξ)
    (i : Fin 5) : geometryIndex s modifier R seed K Z ξ q i ∈ indices 1 (Z^B) := by
  obtain ⟨hlo,hhi⟩ := actual_geometry_norm_caps s modifier R seed K Z ξ B hs hz₁ hz₂ hsource q i
  change ⌊Real.logb 2 (geometryNorms s modifier R seed K Z ξ q i)⌋ ∈ indices 1 (Z^B)
  rw [indices,Finset.mem_Icc]
  simp only [Real.logb_one,Int.ceil_zero]
  refine ⟨Int.floor_nonneg.mpr (Real.logb_nonneg (by norm_num) hlo),?_⟩
  apply Int.floor_mono
  apply Real.logb_le_logb_of_le (by norm_num) (zero_lt_one.trans_le hlo)
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) B
  linarith

omit [DecidableEq ι] in
/-- Five bounded arithmetic norm bins cost a small power, uniformly before
any first label, source or projector is chosen. -/
theorem geometry_bins_subpower (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)(K ξ : ℝ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ((geometryBins s modifier R seed K Z ξ).card:ℝ)≤C*Z^ε := by
  let H : ℝ := 3+B/Real.log 2
  have hH : 0<H := by
    have hh := div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [H]; linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (5:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨32*H^5,by positivity,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (1:ℝ)] with Z ht hexp hZ
  intro s modifier R seed K ξ hs hz₁ hz₂ hsource
  let Box := Fin 5→↥(indices 1 (Z^B))
  have hsub : geometryBins s modifier R seed K Z ξ ⊆
      Finset.univ.image (fun n : Box => fun i => (n i).val) := by
    intro g hg
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hg
    let n : Box := fun i => ⟨geometryIndex s modifier R seed K Z ξ q i,
      geometry_indices_enclosure s modifier R seed K Z ξ B hZ hs hz₁ hz₂ hsource q i⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩
  have hcard : (geometryBins s modifier R seed K Z ξ).card ≤ Fintype.card Box :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  have hsingle : ((indices 1 (Z^B)).card:ℝ)≤H*(1+Real.log Z) := by
    simpa only [Real.logb_one,add_zero] using indices_card_log_bound 1 B Z 1 (Z^B)
      (by norm_num) hB hZ (by norm_num) (Real.one_le_rpow hZ hB) (by simp)
  have hlog : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hexp
    simpa only [Real.log_exp] using hh
  have hpow : (Real.log Z)^5≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hZ) _),one_mul] using ht
  have hc : (Fintype.card Box:ℝ)≤(H*(1+Real.log Z))^5 := by
    simp only [Box,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hsingle 5
  calc
    _ ≤ (Fintype.card Box:ℝ) := by exact_mod_cast hcard
    _ ≤ (H*(1+Real.log Z))^5 := hc
    _ ≤ (H*(2*Real.log Z))^5 := by gcongr; linarith
    _ = (32*H^5)*(Real.log Z)^5 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

omit [DecidableEq ι] in
/-- The actual ratio-and-geometry partition has controlled overhead. No
cardinality of the original label family enters this bound. -/
theorem common_geometry_bins_subpower (A D B ξ ε : ℝ)
    (hA : 0≤A) (hD : 0≤D) (hB : 0≤B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)(R seed : Ideal O)(K : ℝ),0<K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B →
      CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
      ((commonGeometryBins s modifier R seed K Z ξ).card:ℝ)≤C*Z^ε := by
  obtain ⟨Cr,hCr,hr⟩ := actual_ratio_bins_subpower (ι:=ι) A D B ξ (ε/2) hA hD hB hξ (by positivity)
  obtain ⟨Cg,hCg,hg⟩ := geometry_bins_subpower (ι:=ι) B (ε/2) hB (by positivity)
  refine ⟨Cr*Cg,mul_pos hCr hCg,?_⟩
  filter_upwards [hr,hg,eventually_gt_atTop (0:ℝ)] with Z hr hg hZ
  intro s modifier R seed K hK hs hz₁ hz₂ hsource hscap hV hKi
  have hsub : commonGeometryBins s modifier R seed K Z ξ ⊆
      (sourceRatioBins s modifier R seed K Z ξ) ×ˢ (geometryBins s modifier R seed K Z ξ) := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq,Finset.mem_image_of_mem _ hq⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product] at hc
  calc
    _ ≤ ((sourceRatioBins s modifier R seed K Z ξ).card:ℝ)*((geometryBins s modifier R seed K Z ξ).card:ℝ) := by exact_mod_cast hc
    _ ≤ (Cr*Z^(ε/2))*(Cg*Z^(ε/2)) :=
      mul_le_mul (hr s modifier R seed K hK hs hz₁ hz₂ hsource hscap hV hKi)
        (hg s modifier R seed K ξ hs hz₁ hz₂ hscap) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2; ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_labels_commonPart
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_physical_mass_geometry_groups
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_geometry_fiber_range
#print axioms QRH.Record1252270103Source.High.CoupledFirst.common_geometry_bins_subpower
