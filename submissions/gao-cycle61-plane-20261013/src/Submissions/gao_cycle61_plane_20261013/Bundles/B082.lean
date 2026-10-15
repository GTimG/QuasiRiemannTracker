/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B080
import Submissions.gao_cycle61_plane_20261013.Bundles.B081
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.ActiveColumns; sha256 59abb90b4f178d5c2b602ec03aa5e8d0077d1eb64bfef5fd13a194a5416e9d41 -/
section
                                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open RayFourExpansion ConcreteTraceCRT CenteredMomentSmooth
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

abbrev FirstColumnIndex {Label : Type*} (s : Label→FirstBlockSource) :=
  (l : Label) × ↥(s l).divisors × RayCharacter × RayCharacter

def firstSectorColumn {Label : Type*} (s : Label→FirstBlockSource)
    (q : FirstSector s) : FirstColumnIndex s := ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1⟩

def firstColumnRows {Label : Type*} (s : Label→FirstBlockSource)
    (V : Fin 4→ℝ→ℂ) (j : FirstColumnIndex s) : Finset O :=
  (s j.1).rows.filter (fun z=>
    V 0 (Real.log ((s j.1).K/‖eisEmbedding (s j.1).e‖^2/
      ‖eisEmbedding (s j.1).r‖^2/(s j.1).K0))≠0 ∧
      V 1 (Real.log (‖eisEmbedding z‖^2/(s j.1).H0))≠0 ∧ Squarefree j.2.1.val)

/-- Separates only the row coordinate. The common ideal, residual divisor
and both ray indices are retained together in the outer Hilbert index. -/
theorem actual_first_active_columns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ)
    (F : FirstColumnIndex s→O→ℝ) :
    (∑q∈firstActiveSectors s V,F (firstSectorColumn s q) q.2.2.2.2.val)=
      ∑j : FirstColumnIndex s,∑z∈firstColumnRows s V j,F j z := by
  rw [firstActiveSectors,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma,
    Fintype.sum_prod_type,firstSectorColumn,firstRho,firstX,firstColumnRows]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  exact Finset.sum_coe_sort (s l).rows (fun z=>
    if V 0 (Real.log ((s l).K/‖eisEmbedding (s l).e‖^2/‖eisEmbedding (s l).r‖^2/(s l).K0))≠0 ∧
      V 1 (Real.log (‖eisEmbedding z‖^2/(s l).H0))≠0 ∧ Squarefree L.val then F ⟨l,L,χ,ψ⟩ z else 0)

theorem actual_first_column_annulus {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (j : FirstColumnIndex s) (z : O)
    (hz : z∈firstColumnRows s (fun _=>logAnnulus) j) :
    (s j.1).H0/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤(s j.1).H0 := by
  have hmem := Finset.mem_filter.mp hz
  let q : FirstSector s := ⟨j.1,j.2.1,j.2.2.1,j.2.2.2,⟨z,hmem.1⟩⟩
  exact actual_first_active_annulus s q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem.2⟩)

def firstLiveColumns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ) : Finset (FirstColumnIndex s) :=
  Finset.univ.filter (fun j=>(firstColumnRows s V j).Nonempty)

theorem actual_first_live_squarefree {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ) (j : FirstColumnIndex s)
    (hj : j∈firstLiveColumns s V) : Squarefree j.2.1.val := by
  obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hj).2
  exact (Finset.mem_filter.mp hz).2.2.2

theorem actual_first_live_columns {Label : Type*} [Fintype Label]
    (s : Label→FirstBlockSource) (V : Fin 4→ℝ→ℂ)
    (F : FirstColumnIndex s→O→ℝ) :
    (∑q∈firstActiveSectors s V,F (firstSectorColumn s q) q.2.2.2.2.val)=
      ∑j∈firstLiveColumns s V,∑z∈firstColumnRows s V j,F j z := by
  rw [actual_first_active_columns]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hnot
  have hempty : firstColumnRows s V j=∅ := Finset.not_nonempty_iff_eq_empty.mp
    (fun h=>hnot (Finset.mem_filter.mpr ⟨hj,h⟩))
  rw [hempty,Finset.sum_empty]

open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy

/-- The localized Hilbert sum feeds directly into actual common allocation
and child energies, preserving its full outer label and both ray indices. -/
theorem actual_active_common_live_energy {Label ι : Type*} [Fintype Label] [Fintype ι]
    (reflected : Bool) (src : Label→FirstBlockSource) (N : ℕ) (a b : ℝ) (ha : 0< a) (s : Input ι)
    (hcard : Fintype.card ι≤ N) (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (C : FirstColumnIndex src→Ideal O) (R seed : Ideal O)
    (hC : ∀j,Supported (C j)) (hseed : ∀j,seed∣C j)
    (τ : FirstColumnIndex src→Character) (t weight : FirstColumnIndex src→ℝ)
    (hw : ∀j,0≤ weight j) :
    (∑q∈firstActiveSectors src (fun _=>logAnnulus),
      weight (firstSectorColumn src q)*
        ‖allocatedPolynomial (original s R seed) (C (firstSectorColumn src q))
          q.2.1.val (τ (firstSectorColumn src q)) (t (firstSectorColumn src q))
          (volume s) (firstSignedRow reflected q.2.2.2.2.val)‖^2)≤
      ∑j∈firstLiveColumns src (fun _=>logAnnulus),
        weight j*((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
          ∑B : actualAllocations s.pools (C j),
            if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
              (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R j.2.1.val B
                (τ j) (t j) CenteredMomentFirstAnnularMajorant.profile (src j.1).H0
            else 0) := by
  have he := actual_first_live_columns src (fun _=>logAnnulus)
    (fun j z=>weight j*‖allocatedPolynomial (original s R seed) (C j) j.2.1.val
      (τ j) (t j) (volume s) (firstSignedRow reflected z)‖^2)
  change _ = ∑j∈firstLiveColumns src (fun _=>logAnnulus),∑z∈firstColumnRows src (fun _=>logAnnulus) j,
    weight j*‖allocatedPolynomial (original s R seed) (C j) j.2.1.val
      (τ j) (t j) (volume s) (firstSignedRow reflected z)‖^2 at he
  apply le_trans (le_of_eq he)
  simp_rw [←Finset.mul_sum]
  exact actual_joint_annular_live_energy reflected (firstLiveColumns src (fun _=>logAnnulus)) N a b ha s hcard haS hbS C R seed hC hseed τ t
    (fun j=>j.2.1.val) (fun j=>(src j.1).H0) weight (firstColumnRows src (fun _=>logAnnulus))
    (fun j=>(src j.1).H0_pos) hw (actual_first_column_annulus src)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_active_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_column_annulus
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_active_common_live_energy

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_live_squarefree
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_live_columns

end
/- END ORIGINAL Cycle61.Physical.InitialMass.ActiveColumns -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryBins; sha256 48ff6a707df77b08e6f573329c318ea5be76bb817ddc6efc5dcfa5b9e95f253f -/
section
                                             

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle61InitialMass
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
local instance geometryBinsSumDecidableEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
/-- Actual equal-support first labels are already their full common parts.
This aligns the raw label norms with the exact normalization exponents. -/
lemma actual_labels_commonPart (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
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
def geometryIdeals (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) : Fin 5→Ideal O :=
  ![q.1.val.1,q.1.val.2,commonRadical q.1.val.1 q.1.val.2,
    Ideal.span {activeConductor q.1.val.1 q.1.val.2},
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}]

def geometryNorms (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) (i : Fin 5) : ℝ :=
  (geometryIdeals s R seed K Z ξ q i).absNorm

def geometryExponents (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) (i : Fin 5) : ℝ :=
  Real.logb Z (geometryNorms s R seed K Z ξ q i)

def geometryIndex (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) : Fin 5→ℤ :=
  fun i=>⌊Real.logb 2 (geometryNorms s R seed K Z ξ q i)⌋

def geometryBins (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) : Finset (Fin 5→ℤ) :=
  Finset.univ.image (geometryIndex s R seed K Z ξ)

def commonGeometryKey (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) : ℤ×(Fin 5→ℤ) :=
  (sourceRatioIndex s R seed K Z ξ q,geometryIndex s R seed K Z ξ q)

def commonGeometryBins (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) : Finset (ℤ×(Fin 5→ℤ)) :=
  Finset.univ.image (commonGeometryKey s R seed K Z ξ)

abbrev CommonGeometryFiber (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (key : ℤ×(Fin 5→ℤ)) :=
  {q : FirstSourceCoordinate s R seed K Z ξ // commonGeometryKey s R seed K Z ξ q=key}

omit [DecidableEq ι] in
lemma commonGeometryFiber_ratio (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s R seed K Z ξ key) :
    sourceRatioIndex s R seed K Z ξ q.val=key.1 := congrArg Prod.fst q.property

/-- Exact grouped physical mass; both ratio and common geometry stay in the
fiber, while every original first label remains inside the joint sum. -/
theorem actual_physical_mass_geometry_groups (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ =
    ∑key∈commonGeometryBins s R seed K Z ξ,
      ‖∑q : CommonGeometryFiber s R seed K Z ξ key,
        normPhase (coordinateBlock s R seed W K Z ξ q.val)*
          coordinateBlock s R seed W K Z ξ q.val‖ := by
  rw [actual_physical_mass_joint_sum]
  simp_rw [normPhase_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  simp_rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q∈(Finset.univ : Finset (FirstSourceCoordinate s R seed K Z ξ))) =>
      Finset.mem_image_of_mem (commonGeometryKey s R seed K Z ξ) hq)]
  apply Finset.sum_congr rfl
  intro key _
  exact Finset.sum_subtype (Finset.univ.filter (fun q : FirstSourceCoordinate s R seed K Z ξ=>
    commonGeometryKey s R seed K Z ξ q=key))
    (fun q=>by simp) (fun q=>‖coordinateBlock s R seed W K Z ξ q‖)

omit [DecidableEq ι] in
lemma actual_geometry_norm_caps (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (q : FirstSourceCoordinate s R seed K Z ξ)
    (i : Fin 5) : 1≤ geometryNorms s R seed K Z ξ q i ∧
      geometryNorms s R seed K Z ξ q i≤ Z^B := by
  have hg := actual_common_gates s R seed hs hz₁ hz₂ q.1.val.1 q.1.val.2 q.1.property
  have hc := (CenteredMomentSecondRetainedAggregate.commonLabels_supported
    (CenteredMomentActiveSource.activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed)) _ _ q.1.property).1
  have hf := original_factor_caps q.1.val.1 q.1.val.2 hc q.2.1.val
  rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span] at hf
  have one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤ I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  fin_cases i
  · change (1:ℝ)≤ q.1.val.1.absNorm ∧ (q.1.val.1.absNorm:ℝ)≤ Z^B
    exact ⟨one _ hg.1,hg.2.2.2.2.2.1.trans hsource⟩
  · change (1:ℝ)≤ q.1.val.2.absNorm ∧ (q.1.val.2.absNorm:ℝ)≤ Z^B
    exact ⟨one _ hg.2.1,hg.2.2.2.2.2.2.trans hsource⟩
  · change (1:ℝ)≤(commonRadical q.1.val.1 q.1.val.2).absNorm ∧
      ((commonRadical q.1.val.1 q.1.val.2).absNorm:ℝ)≤ Z^B
    exact ⟨one _ (commonRadical_ne_zero _ _),
      (divisor_norm_le _ _ hg.1 ((commonRadical_dvd_commonPart _ _).trans
        (commonPart_dvd _ _ hg.1))).trans (hg.2.2.2.2.2.1.trans hsource)⟩
  · change (1:ℝ)≤(Ideal.span {activeConductor q.1.val.1 q.1.val.2}).absNorm ∧
      ((Ideal.span {activeConductor q.1.val.1 q.1.val.2}).absNorm:ℝ)≤ Z^B
    exact ⟨one _ (Ideal.span_singleton_eq_bot.not.mpr (finitePrimeModulus_ne_zero _)),
      hf.2.trans (hg.2.2.2.2.2.1.trans hsource)⟩
  · change (1:ℝ)≤(Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}).absNorm ∧
      ((Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex q.1.val.1 q.1.val.2=>P.val) q.2.1.val}).absNorm:ℝ)≤ Z^B
    exact ⟨one _ (subsetGenerator_supported _ _ hc _).1,
      hf.1.trans (hg.2.2.2.2.2.1.trans hsource)⟩

/-- One log2 bin has width exactly log_Z 2 in exponent coordinates. -/
lemma log_norm_bin_range (Z n : ℝ) (hZ : 1< Z) (_hn : 0< n) :
    (⌊Real.logb 2 n⌋:ℝ)*Real.logb Z 2≤ Real.logb Z n ∧
      Real.logb Z n<((⌊Real.logb 2 n⌋:ℝ)+1)*Real.logb Z 2 := by
  have hwidth : 0< Real.logb Z 2 := by
    unfold Real.logb
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos hZ)
  have he : Real.logb Z n=Real.logb 2 n*Real.logb Z 2 := by
    unfold Real.logb
    field_simp
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right (Int.floor_le _) hwidth.le,
    mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) hwidth⟩

omit [DecidableEq ι] in
lemma actual_geometry_fiber_range (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1< Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s R seed K Z ξ key) (i : Fin 5) :
    (key.2 i:ℝ)*Real.logb Z 2≤ geometryExponents s R seed K Z ξ q.val i ∧
      geometryExponents s R seed K Z ξ q.val i<((key.2 i:ℝ)+1)*Real.logb Z 2 := by
  have hn := actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val i
  have he := congrFun (congrArg Prod.snd q.property) i
  have hh := log_norm_bin_range Z _ hZ (zero_lt_one.trans_le hn.1)
  simpa only [geometryExponents,geometryIndex,commonGeometryKey] using he ▸ hh

omit [DecidableEq ι] in
lemma geometry_indices_enclosure (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1≤ Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (q : FirstSourceCoordinate s R seed K Z ξ)
    (i : Fin 5) : geometryIndex s R seed K Z ξ q i ∈ indices 1 (Z^B) := by
  obtain ⟨hlo,hhi⟩ := actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q i
  change ⌊Real.logb 2 (geometryNorms s R seed K Z ξ q i)⌋ ∈ indices 1 (Z^B)
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
theorem geometry_bins_subpower (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K ξ : ℝ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      ((geometryBins s R seed K Z ξ).card:ℝ)≤ C*Z^ε := by
  let H : ℝ := 3+B/Real.log 2
  have hH : 0< H := by
    have hh := div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [H]; linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (5:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨32*H^5,by positivity,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (1:ℝ)] with Z ht hexp hZ
  intro s R seed K ξ hs hz₁ hz₂ hsource
  let Box := Fin 5→↥(indices 1 (Z^B))
  have hsub : geometryBins s R seed K Z ξ ⊆
      Finset.univ.image (fun n : Box => fun i => (n i).val) := by
    intro g hg
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hg
    let n : Box := fun i => ⟨geometryIndex s R seed K Z ξ q i,
      geometry_indices_enclosure s R seed K Z ξ B hZ hs hz₁ hz₂ hsource q i⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩
  have hcard : (geometryBins s R seed K Z ξ).card ≤ Fintype.card Box :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  have hsingle : ((indices 1 (Z^B)).card:ℝ)≤ H*(1+Real.log Z) := by
    simpa only [Real.logb_one,add_zero] using indices_card_log_bound 1 B Z 1 (Z^B)
      (by norm_num) hB hZ (by norm_num) (Real.one_le_rpow hZ hB) (by simp)
  have hlog : 1≤ Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hexp
    simpa only [Real.log_exp] using hh
  have hpow : (Real.log Z)^5≤ Z^ε := by
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
    (hA : 0≤ A) (hD : 0≤ D) (hB : 0≤ B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ),0< K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B →
      CenteredMomentAmplificationChildInput.volume s≤ Z^A → K⁻¹≤ Z^D →
      ((commonGeometryBins s R seed K Z ξ).card:ℝ)≤ C*Z^ε := by
  obtain ⟨Cr,hCr,hr⟩ := actual_ratio_bins_subpower (ι:=ι) A D B ξ (ε/2) hA hD hB hξ (by positivity)
  obtain ⟨Cg,hCg,hg⟩ := geometry_bins_subpower (ι:=ι) B (ε/2) hB (by positivity)
  refine ⟨Cr*Cg,mul_pos hCr hCg,?_⟩
  filter_upwards [hr,hg,eventually_gt_atTop (0:ℝ)] with Z hr hg hZ
  intro s R seed K hK hs hz₁ hz₂ hsource hscap hV hKi
  have hsub : commonGeometryBins s R seed K Z ξ ⊆
      (sourceRatioBins s R seed K Z ξ) ×ˢ (geometryBins s R seed K Z ξ) := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq,Finset.mem_image_of_mem _ hq⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product] at hc
  calc
    _ ≤ ((sourceRatioBins s R seed K Z ξ).card:ℝ)*((geometryBins s R seed K Z ξ).card:ℝ) := by exact_mod_cast hc
    _ ≤ (Cr*Z^(ε/2))*(Cg*Z^(ε/2)) :=
      mul_le_mul (hr s R seed K hK hs hz₁ hz₂ hsource hscap hV hKi)
        (hg s R seed K ξ hs hz₁ hz₂ hscap) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_labels_commonPart
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_geometry_groups
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_fiber_range
#print axioms OAI.SevenEighths.Cycle61InitialMass.common_geometry_bins_subpower

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryBins -/

/- BEGIN ORIGINAL Cycle61.Physical.TerminalRadius; sha256 58196818e5eb9a41540d51b2ad24aca91f46baa08eb4dc8731bd103eba8304bf -/
section
                                                             

namespace Cycle61.Physical
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentDescentLedger CenteredMomentCommonRadiusSaving
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

/-- The side allowance is its own positive-part cost, not the sum of the
two sides' allowances. The literal main radius uses sigma=3a. -/
theorem actual_main_side_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (U : Finset (CommonIndex I J)) (K X Z j a δ reserve : ℝ) (hZ : 1 < Z)
    (hmod : τ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) U*
        activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K₀ := nominalLog I J E K X Z
    2*c/3-4*a-5*(δ+reserve)/6 ≤
      firstSaving c (d+K₀-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (max (3*c-5*d-R) 0/6)
        (Real.logb Z (mainCommonRadius Z d K₀ c (3*a) δ reserve)-j) a := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  have hg := canonical_saving_gates η τ m I J hI hJ U Z hZ hmod
  have hq := canonical_active_log_le η τ m I J U Z hZ hmod
  dsimp only at hg hq
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have hs := main_saving_lower
    (Real.logb Z ((commonPart I J).absNorm:ℝ))
    (Real.logb Z ((commonPart J I).absNorm:ℝ))
    (nominalLog I J E K X Z-j) (Real.logb Z (τ.modulus.absNorm:ℝ))
    (max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
      5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6)
    (3*a) δ reserve hg.1 hq.1 (by positivity) (by linarith [hq.2])
  convert hs using 1 <;> congr 1 <;> ring

/-- The actual extracted common parts supply the primewise balance used
after the two joint side-energy estimates. -/
theorem actual_joint_side_exponent (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (Z M A E : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let Bc := max (3*c-5*d-R) 0/6
    let Bd := max (3*d-5*c-R) 0/6
    M-A-R/2-E+((p+A-c+R+E+Bc)+(p+A-d+R+E+Bd))/2 ≤ M := by
  dsimp only
  have hb := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hb
  linarith

end
end Cycle61.Physical

#print axioms Cycle61.Physical.actual_main_side_saving
#print axioms Cycle61.Physical.actual_joint_side_exponent

end
/- END ORIGINAL Cycle61.Physical.TerminalRadius -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.Normalization; sha256 4601d18bb627f201d4d638f19ac72f9006fc30eb47cab32d79cfc002a19d4dfa -/
section
                                      
                                                                           

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstScale
open CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

lemma outside_power (K V E R Z : ℝ) (hK : 0< K) (hV : 0< V)
    (hE : 0< E) (hR : 0< R) (hZ : 1< Z) :
    K/(V*E*Real.sqrt R)=
      Z^(Real.logb Z K-Real.logb Z V-Real.logb Z E-Real.logb Z R/2) := by
  have hz := zero_lt_one.trans hZ
  have hs : Z^(Real.logb Z R/2)=Real.sqrt R := by
    rw [div_eq_mul_inv,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hR]
    norm_num [Real.sqrt_eq_rpow]
  rw [Real.rpow_sub hz,Real.rpow_sub hz,Real.rpow_sub hz,
    Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hV,
    Real.rpow_logb hz hZ.ne' hE,hs]
  ring

/-- The literal first-transform scalar, after canceling both actual column
scales, leaves exactly the active half-radical and inactive whole radical.
The inactive Möbius weight remains visible. -/
theorem actual_scalar_outside (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (K A₀ B₀ V Z : ℝ)
    (hK : 0< K) (hA : 0< A₀) (hB : 0< B₀) (hV : 0< V) (hZ : 1< Z) :
    ‖scalar C D hC E K A₀ B₀‖*Real.sqrt A₀*Real.sqrt B₀/V =
      ‖inactiveWeight C D E‖*
      Z^(Real.logb Z K-Real.logb Z V-
        Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)/2) := by
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hroot : Real.sqrt ((Ideal.span {activeConductor C D}).absNorm:ℝ)=
      ‖eisEmbedding (activeConductor C D)‖ := by
    rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]
  rw [←outside_power K V _ _ Z hK hV hE hR hZ,hroot,
    ←eisEmbedding_norm_sq_eq_absNorm_span,scalar_norm C D hC E K A₀ B₀ hK hA hB]
  have ha : Real.sqrt A₀≠0 := (Real.sqrt_pos.mpr hA).ne'
  have hb : Real.sqrt B₀≠0 := (Real.sqrt_pos.mpr hB).ne'
  field_simp

/-- The actual Möbius coefficient costs at most one. The dyadic column
normalizers are canceled before using the common radical side bounds. -/
theorem actual_scalar_outside_le (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (M A₀ B₀ V Z : ℝ)
    (hA : 0< A₀) (hB : 0< B₀) (hV : 0< V) (hZ : 1< Z) :
    ‖scalar C D hC E (Z^M) A₀ B₀‖*Real.sqrt A₀*Real.sqrt B₀/V ≤
      Z^(M-Real.logb Z V-
        Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)/2) := by
  have hz := zero_lt_one.trans hZ
  rw [actual_scalar_outside C D hC E _ _ _ _ _ (Real.rpow_pos_of_pos hz _) hA hB hV hZ,
    Real.logb_rpow hz hZ.ne']
  exact mul_le_of_le_one_left (Real.rpow_nonneg hz.le _)
    (QuadraticInitialBound.norm_ideal_moebius_le_one _)

/-- Exact balance for one common label. Global joint Cauchy requires the
cross-label geometry-bin payment proved in GeometryPayment. -/
theorem actual_joint_power (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (Z M A E : ℝ) (hZ : 1< Z) :
    let c := Real.logb Z ((commonPart C D).absNorm:ℝ)
    let d := Real.logb Z ((commonPart D C).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    let Bc := max (3*c-5*d-R) 0/6
    let Bd := max (3*d-5*c-R) 0/6
    Z^(M-A-R/2-E)*Real.sqrt (Z^(p+A-c+R+E+Bc))*
      Real.sqrt (Z^(p+A-d+R+E+Bd)) ≤ Z^M := by
  dsimp only
  have hz := zero_lt_one.trans hZ
  simp only [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hh := Cycle61.Physical.actual_joint_side_exponent C D hC hD Z M A E hZ
  dsimp only at hh
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_scalar_outside
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_scalar_outside_le
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_power

end
/- END ORIGINAL Cycle61.Physical.InitialMass.Normalization -/
