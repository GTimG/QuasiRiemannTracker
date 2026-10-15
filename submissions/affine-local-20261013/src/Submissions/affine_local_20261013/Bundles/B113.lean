/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.affine_local_20261013.Bundles.B067
import Submissions.affine_local_20261013.Bundles.B071
import Submissions.affine_local_20261013.Bundles.B084
import Submissions.affine_local_20261013.Bundles.B088
import Submissions.affine_local_20261013.Bundles.B102
import Submissions.affine_local_20261013.Bundles.B108
import Submissions.affine_local_20261013.Bundles.B109
import Submissions.affine_local_20261013.Bundles.B111
import Submissions.affine_local_20261013.Bundles.B112
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary

/- BEGIN ORIGINAL MODULE Analytic.JointPacketSecondSectors ; sha256 2acf21a8524d9ebb060f2195955b67284a29ed4966dc246b2902b03232ed863f -/
section




/-! A fixed finite partition of all actual second-source packets. Its
coordinates depend only on the second arithmetic labels, so canonical
recovery and both first-ray choices preserve each cell exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open NonzeroJointSourceRow CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

namespace ActualFirstSecondSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem packet_second_norm_cap
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (x : Packet src R seed Kfirst radius side K Radius H) :
    ((packetLabel hs hz₁ hz₂ x).second.val.1.absNorm : ℝ) ≤ sourceRadius src ∧
      ((packetLabel hs hz₁ hz₂ x).second.val.2.absNorm : ℝ) ≤ sourceRadius src := by
  have hc := sourceFirstCommon_supported (original src R seed) side x.1.1.1
  have hh := actual_common_cumulative_norm src R seed
    (sourceFirstCommon side x.1.1.1.val) x.1.2.1.val hc hz₁ hz₂ x.2.1.1.1
  have hNC : (1:ℝ) ≤ (sourceFirstCommon side x.1.1.1.val).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hc.1)
  simp only [map_mul,Nat.cast_mul] at hh
  constructor
  · change (x.2.1.1.1.val.1.absNorm : ℝ) ≤ _
    nlinarith [Nat.cast_nonneg (α := ℝ) x.2.1.1.1.val.1.absNorm]
  · change (x.2.1.1.1.val.2.absNorm : ℝ) ≤ _
    nlinarith [Nat.cast_nonneg (α := ℝ) x.2.1.1.1.val.2.absNorm]

/-- The second-sector coordinates are independent of every ray and the
chosen total extension outside the actual arithmetic image. -/
theorem packet_source_second_width
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (rowDefault : NonzeroJointSourceRow (original src R seed) side)
    (η : Character) (χ ξ χ₂ ξ₂ : RayCharacter)
    (x : Packet src R seed Kfirst radius side K Radius H) (hz : (row x).z ≠ 0)
    (Z : ℝ) :
    (sourceKernel src R seed side hs hz₁ hz₂ rowDefault η χ ξ χ₂ ξ₂
      (label ⟨row x,hz⟩)).secondWidthCoordinates Z =
      (packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z := by
  simp only [sourceKernel,recover_label]
  rfl

end ActualFirstSecondSource

/-- The number of second sectors is fixed before the scale, source, all
arithmetic labels, rays, dyadics and frequency rows. The code is total;
no dummy sector or proof-dependent membership extension is required. -/
theorem uniform_actual_packet_second_sectors (e : ℝ) (he : 0 < e) :
    ∃ N : ℕ, ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
      (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
      (side : Bool) (K Radius H : ActualFirstSecondSource.First src R seed Kfirst radius → ℝ)
      (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
      (Z : ℝ), 1 < Z → sourceRadius src ≤ Z →
      ∃ code : ActualFirstSecondSource.Packet src R seed Kfirst radius side K Radius H →
          Fin 4 → Fin (N+1),
        ∀ x j, 0 ≤ secondWidthEdge e (code x) j ∧
          secondWidthEdge e (code x) j ≤
            (ActualFirstSecondSource.packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j ∧
          (ActualFirstSecondSource.packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j <
            secondWidthEdge e (code x) j+e := by
  obtain ⟨N,hN⟩ := exists_nat_ge (1/e)
  refine ⟨N,?_⟩
  intro ι inst inst' src R seed Kfirst radius side K Radius H hs hz₁ hz₂ Z hZ hcap
  have hb (x : ActualFirstSecondSource.Packet src R seed Kfirst radius side K Radius H) j :=
    (ActualFirstSecondSource.packetLabel hs hz₁ hz₂ x).second_width_coordinates_bounds Z 1 hZ
      (by simpa only [Real.rpow_one] using
        (ActualFirstSecondSource.packet_second_norm_cap hs hz₁ hz₂ x).1.trans hcap)
      (by simpa only [Real.rpow_one] using
        (ActualFirstSecondSource.packet_second_norm_cap hs hz₁ hz₂ x).2.trans hcap) j
  let code : ActualFirstSecondSource.Packet src R seed Kfirst radius side K Radius H →
      Fin 4 → Fin (N+1) := fun x j =>
    ⟨Nat.floor ((ActualFirstSecondSource.packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j/e),
      Nat.lt_succ_of_le (Nat.floor_le_of_le ((div_le_iff₀ he).mpr
        ((hb x j).2.trans ((div_le_iff₀ he).mp hN))))⟩
  refine ⟨code,?_⟩
  intro x j
  have hl := Nat.floor_le (div_nonneg (hb x j).1 he.le)
  have hh := Nat.lt_floor_add_one
    ((ActualFirstSecondSource.packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j/e)
  change 0 ≤ (Nat.floor (_/e) : ℝ)*e ∧ (Nat.floor (_/e) : ℝ)*e ≤ _ ∧
    _ < (Nat.floor (_/e) : ℝ)*e+e
  refine ⟨by positivity,(le_div_iff₀ he).mp hl,?_⟩
  have hh' := (div_lt_iff₀ he).mp hh
  nlinarith

namespace ActualFirstSecondSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

/-- The exact lower-edge sector gate for the canonical arithmetic image
of any packet cell, for arbitrary first-ray choices. -/
theorem packet_cell_second_sector
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (fallback : First src R seed Kfirst radius)
    (rowDefault : NonzeroJointSourceRow (original src R seed) side)
    (η : Character) (χ ξ χ₂ ξ₂ : RayCharacter)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    {N : ℕ} (code : Packet src R seed Kfirst radius side K Radius H → Fin 4 → Fin (N+1))
    (cell : Fin 4 → Fin (N+1)) (Z e : ℝ)
    (hcode : ∀ x∈X, ∀ j, 0 ≤ secondWidthEdge e (code x) j ∧
      secondWidthEdge e (code x) j ≤ (packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j ∧
      (packetLabel hs hz₁ hz₂ x).secondWidthCoordinates Z j < secondWidthEdge e (code x) j+e)
    (hzero : ∀ x∈X.filter (fun x => code x=cell), (row x).z≠0)
    (v : JointReconstructionLabel)
    (hv : v ∈ (rayRows fallback (X.filter (fun x => code x=cell)) hzero χ ξ).image label) :
    ∀ j, 0 ≤ secondWidthEdge e cell j ∧
      secondWidthEdge e cell j ≤
        (sourceKernel src R seed side hs hz₁ hz₂ rowDefault η χ ξ⁻¹ χ₂ ξ₂ v).secondWidthCoordinates Z j ∧
      (sourceKernel src R seed side hs hz₁ hz₂ rowDefault η χ ξ⁻¹ χ₂ ξ₂ v).secondWidthCoordinates Z j ≤
        secondWidthEdge e cell j+e := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback _ hzero χ ξ q hq
  have hqeq : q = ⟨row x,by simpa only [hrow] using q.property⟩ := Subtype.ext hrow.symm
  rw [hqeq]
  rw [packet_source_second_width hs hz₁ hz₂ rowDefault η χ ξ⁻¹ χ₂ ξ₂ x _ Z]
  have hc := Finset.mem_filter.mp hx
  intro j
  have hh := hcode x hc.1 j
  rw [hc.2] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.packet_second_norm_cap
#print axioms ActualFirstSecondSource.packet_source_second_width
#print axioms uniform_actual_packet_second_sectors
#print axioms ActualFirstSecondSource.packet_cell_second_sector
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPacketSecondSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentAuxiliaryGates ; sha256 55bf556a74992cd6f252880270b73eb5eb418c75f3209d1cd0367a83ab656187 -/
section




/-! Fixed profile bounds and polynomial scale caps for the coherent
zero and discarded terms. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSourceSecondZeroEnergy
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coherentAbsoluteProfileBound (N : ℕ) (Mslot B₁ B₂ upper b₁ b₂ : ℝ) : ℝ :=
  2*128^(N+2)*(max 1 Mslot)^N*B₁*B₂*(max 1 upper)^N*max 1 b₁*max 1 b₂

lemma originalAbsoluteProfile_fixed (s : Input ι) (Mslot B₁ B₂ upper b₁ b₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hM : ∀ i,s.M i ≤ Mslot)
    (hu : s.upper ≤ upper) (hb₁ : |s.b₁| ≤ b₁) (hb₂ : |s.b₂| ≤ b₂) :
    0 ≤ originalAbsoluteProfile s B₁ B₂ ∧
    originalAbsoluteProfile s B₁ B₂ ≤
      coherentAbsoluteProfileBound (Fintype.card ι) Mslot B₁ B₂ upper b₁ b₂ := by
  have hM0 (i) : 0 ≤ s.M i := zero_le_one.trans (s.M_ge_one i)
  have hprod : (∏ i,s.M i) ≤ (max 1 Mslot)^Fintype.card ι := by
    calc
      _ ≤ ∏ _i : ι,max 1 Mslot :=
        Finset.prod_le_prod₀ (fun i _ => hM0 i) (fun i _ => (hM i).trans (le_max_right _ _))
      _ = _ := by simp
  constructor
  · unfold originalAbsoluteProfile
    have hm := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => hM0 i)
    positivity
  · unfold originalAbsoluteProfile coherentAbsoluteProfileBound
    gcongr
    · exact (le_abs_self _).trans hb₁
    · exact (le_abs_self _).trans hb₂

lemma FirstJointLabel.sideWidth_bounds (q : FirstJointLabel ι) (left : Bool) (Z B : ℝ)
    (hZ : 1 < Z) (hC : (q.C.absNorm : ℝ) ≤ Z^B) (hD : (q.D.absNorm : ℝ) ≤ Z^B) :
    0 ≤ q.sideWidth left Z ∧ q.sideWidth left Z ≤ B := by
  have hn : 0 < ((q.sideCommon left).absNorm : ℝ) :=
    CenteredMomentFirstScale.norm_pos _ (q.sideCommon_supported left).1
  have hn1 : (1:ℝ) ≤ (q.sideCommon left).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (q.sideCommon_supported left).1)
  have hcap : ((q.sideCommon left).absNorm : ℝ) ≤ Z^B := by
    cases left <;> assumption
  refine ⟨Real.logb_nonneg hZ hn1,?_⟩
  have hh := Real.logb_le_logb_of_le hZ hn hcap
  simpa only [FirstJointLabel.sideWidth,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

lemma firstLowMainScale_polynomial_cap (q : FirstJointLabel ι) (left : Bool)
    (Z A omega : ℝ) (hZ : 1 < Z) (hA : A ≤ 1) (homega : omega ≤ 1)
    (hC : (q.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hD : (q.D.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    0 < firstLowMainScale q left Z A 1 omega ∧
    firstLowMainScale q left Z A 1 omega ≤ Z^(10:ℝ) := by
  have hc := q.sideWidth_bounds left Z 1 hZ hC hD
  have hd := q.sideWidth_bounds (!left) Z 1 hZ hC hD
  have hw := q.width_coordinates_bounds Z 1 hZ (by norm_num) hC hD
  have hr := (hw 3).2
  have he := (hw 4).2
  norm_num [FirstJointLabel.widthCoordinates] at hr he
  have hm : max (q.sideWidth (!left) Z-q.sideWidth left Z) 0 ≤ 1 :=
    max_le (by linarith) (by norm_num)
  constructor
  · unfold firstLowMainScale; positivity
  · unfold firstLowMainScale
    rw [←q.activeWidth_normValue,←q.punctureWidth_normValue]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    change 2*A-q.sideWidth left Z-q.sideWidth (!left) Z+q.activeWidth Z+
      q.punctureWidth Z-1+max (q.sideWidth (!left) Z-q.sideWidth left Z) 0+6*(3/500)+omega ≤ 10
    linarith

lemma first_actual_common_caps (s : Input ι) (R seed : Ideal O)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (K : ℝ) (radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (i : FirstSourceOuterIndex s R seed K radius) (Z : ℝ)
    (hsource : sourceRadius s ≤ Z^(1:ℝ)) :
    ((firstSourceOuterLabel s R seed K radius i).C.absNorm : ℝ) ≤ Z^(1:ℝ) ∧
    ((firstSourceOuterLabel s R seed K radius i).D.absNorm : ℝ) ≤ Z^(1:ℝ) := by
  have hh := actual_common_gates s R seed hs hz₁ hz₂ i.1.val.1 i.1.val.2 i.1.property
  exact ⟨hh.2.2.2.2.2.1.trans hsource,hh.2.2.2.2.2.2.trans hsource⟩

#print axioms firstLowMainScale_polynomial_cap
#print axioms originalAbsoluteProfile_fixed
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentAuxiliaryGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalLiteralTarget ; sha256 ec2c474b63207bc61fd8b9a7c54efe3bbfc9ae7dcec3a2b6b1b5e1a2bb0655e1 -/
section



/-! The coherent exceptional first target in the local length window.
All loss parameters, profile constants and the allowed height exponent
are fixed before the live source and arithmetic labels. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentRankinRadical CenteredMomentFirstMixedAllowance
open CenteredMomentSecondBlockAggregate CenteredMomentSecondEnergySplit
open CenteredMomentSecondExceptionalSourceFamily RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance coherentExceptionalLiteralDecidableSum : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_literal_first_coherent_exceptional_target
    (Mpool : Ideal O) [NeZero Mpool] (Hpool : Subgroup (O ⧸ Mpool)ˣ)
    (hHpool : RayOrthogonality.globalUnits Mpool ≤ Hpool)
    (Sbad : Finset (Ideal O))
    (a b Mslot upper bplain₁ bplain₂ BRmask τ ξ reserve : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hMslot : 0 ≤ Mslot) (hBRmask : 0 ≤ BRmask)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hreserve : 0 ≤ reserve)
    (hbudget : ξ+reserve ≤ lowLocalTiny)
    (lo hi : ι → ℝ) (hlo : ∀ i,0 < lo i)
    (ηfirst : Character) (profile : Profiles a b) (W : 𝓢(ℝ,ℂ)) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τ ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72:O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ (src : Input ι) (w : ι → ℝ),
      (∀ i,0 ≤ w i) → (∀ i,src.P i = Z^(w i)) →
      (∀ i,src.lo i = lo i) → (∀ i,src.hi i = hi i) →
      (∀ i,src.M i ≤ Mslot) → src.upper ≤ upper →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ →
      src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 → src.η = ηfirst →
      0 < sourceRadius src →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
      Z^(1/4:ℝ) ≤ src.X₁ → Z^(1/4:ℝ) ≤ src.X₂ →
      Z^(1/4:ℝ) ≤ src.Y₁ → Z^(1/4:ℝ) ≤ src.Y₂ →
    ∀ (R seed : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BRmask →
      Squarefree seed → seed ≠ 0 →
    let radius := actualLowFirstRadius src R seed Z Z ξ
    let omega := lowLiteralOmega (Fintype.card ι) upper bplain₁ bplain₂ ξ reserve Z
    let q := firstSourceOuterLabel src R seed Z radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Z radius))
      (ref : FirstJointLabel ι) (left : Bool),
      (∀ i ∈ labels,
        (q i).radicalWidth Z ≤ ref.radicalWidth Z+1/10000 ∧
        -2*(q i).sideWidth left Z+(q i).activeWidth Z+(q i).punctureWidth Z+(q i).sideAllowance left Z ≤
          -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z+1/10000) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    ∀ (t : ((i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain,|t k| ≤ Z^ν) →
    ∀ (χ : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2:O) ∣ m →
    (∑ k ∈ domain,
      ‖firstCoherentExceptionalPart src R seed Z radius k left Z
        (Real.logb Z (volume src.toData)) omega ξ (t k) W χ Q m‖/
        (volume src.toData*actualHighPrimeCount Mpool Hpool Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/100) := by
  obtain ⟨ν,hν,hντ,hmain⟩ := actual_local_first_coherent_exceptional_target
    Mpool Hpool hHpool Sbad a b Mslot upper bplain₁ bplain₂ BRmask τ 3 1
    ha hb hMslot hBRmask hτ (by norm_num) (by norm_num) lo hi hlo ηfirst profile W
  refine ⟨ν,hν,hντ,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨C,hC,hmain⟩ := hmain Q hQ hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain,eventually_low_literal_omega (Fintype.card ι) upper bplain₁ bplain₂ ξ reserve hξ hreserve hbudget,
    eventually_low_fixed_profile_gates (ι := ι) upper bplain₁ bplain₂ b (1/1000) (by norm_num)]
    with Z hmain homega hfixed
  intro hZ src w hw hscale hloSrc hhiSrc hMs hupper hhiAbs hb₁ hb₂ hp₁ hp₂ hη hsource₀
    hn₁ hn₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R seed hR hRcap hs hs0 radius omega q labels ref left hsector domain t ht
    χ m hm hmLam hm2
  let A := Real.logb Z (volume src.toData)
  have hAeq := original_volume_log src Z w hZ hscale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) A
    hAeq hn₁ hn₂ hwSum hcapacity).1
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupper).1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hξcap : ξ ≤ 1/1000 := by norm_num [lowLocalTiny] at hbudget; linarith
  have hradius : ∀ p E,radius p E ≤ 1*Z^(3:ℝ) :=
    actualLowFirstRadius_le src R seed Z Z ξ hZ.le hZ (by linarith) hsource₀.le hsource
  exact hmain hZ src w hw hscale hloSrc hhiSrc hMs hupper hhiAbs hb₁ hb₂ hp₁ hp₂ hη hsource₀
    hn₁ hn₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R seed hR hRcap hs hs0 radius hradius
    labels ref left omega ξ homega.2.1 (homega.2.2.trans (by norm_num [lowLocalTiny])) hξ.le hξcap
    hsector t ht χ m hm hmLam hm2

#print axioms actual_literal_first_coherent_exceptional_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstRetainedActual ; sha256 e325fdfbcbefe5cbabeefc941240d183f796e4c2a9a137ce960e096799de8a79 -/
section




/-! The original retained first energy is bounded by precisely the
literal first blocks used by the joint source estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcretePrimeRowBridge CenteredMomentLogDyadic
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstRetainedNorm
open CenteredMomentSourceRow CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance firstRetainedActualDecidableSum : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_retained_norm_actual_first_blocks (src : Input ι) (R seed : Ideal O)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0 < K) :
    let radius := actualLowFirstRadius src R seed K Z ξ
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy src.η
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 t
      (finiteColumns (Fintype.piFinset src.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient src R seed) W K (sourceRadius src) Z ξ‖ ≤
    ∑ i : FirstSourceOuterIndex src R seed K radius,
      ‖firstPhysicalValue src R seed K radius (fun _ => t) W (fun _ => logAnnulus) i‖ := by
  intro radius
  have hh := original_retained_full_sectorMass src R seed hz₁ hz₂
    (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 t
    (finiteColumns (Fintype.piFinset src.pools)) W K (sourceRadius src) Z ξ hK
  apply hh.trans_eq
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  unfold sectorMass
  rw [Fintype.sum_sigma]
  rw [←Finset.sum_coe_sort]
  rfl

#print axioms original_retained_norm_actual_first_blocks
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstRetainedActual -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLivePacketGates ; sha256 5823bc189375a56ca72754cc21422bf8e6983175008da348902ce0e519db76c9 -/
section



/-! Literal nonzero-block and radial support facts survive any finite
packet cell restriction. No geometric or analytic bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockHarmonicMass CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem rayTarget_mono (fallback : First src R seed Kfirst radius)
    (X Y : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hX : ∀ x∈X,(row x).z≠0) (hY : ∀ x∈Y,(row x).z≠0)
    (hsub : X⊆Y) (χ ξ : RayCharacter) :
    rayTarget fallback X hX χ ξ ⊆ rayTarget fallback Y hY χ ξ := by
  intro y hy
  obtain ⟨x,hx,hχ,hξ,hz,rfl⟩ := mem_rayTarget_witness fallback X hX χ ξ y hy
  apply Finset.mem_image.mpr
  refine ⟨⟨x,Finset.mem_filter.mpr ⟨hsub hx,hχ,hξ⟩⟩,Finset.mem_attach _ _,?_⟩
  rfl

theorem rayRows_mono (fallback : First src R seed Kfirst radius)
    (X Y : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hX : ∀ x∈X,(row x).z≠0) (hY : ∀ x∈Y,(row x).z≠0)
    (hsub : X⊆Y) (χ ξ : RayCharacter) :
    rayRows fallback X hX χ ξ ⊆ rayRows fallback Y hY χ ξ :=
  Finset.image_subset_image (rayTarget_mono fallback X Y hX hY hsub χ ξ)

variable (src R seed Kfirst radius side) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
  (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))

theorem live_subset_physical
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) :
    ∀ x∈X, ∃ rows : Finset O,
      activePhysicalRows (parent src R seed Kfirst radius side x.1) (t x.1)
        (columns src R seed Kfirst radius side x.1) (beta src R seed Kfirst radius side x.1)
        W (mainScale src R seed Kfirst radius side Z A M omega x.1)
        (mainRadius src R seed Kfirst radius side Z A M omega ξ x.1)
        (mainHeight src R seed Kfirst radius side x.1) x.2.1 rows ≠ 0 := by
  intro x hx
  have hm := (Finset.mem_sigma.mp (Finset.mem_sigma.mp (hX hx)).2).2
  exact ⟨binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b x.1 x.2.1,
    (liveBinRows_gates src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W
      x.1 x.2.1 x.2.2 hm).2⟩

#print axioms live_subset_physical
#print axioms rayRows_mono
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLivePacketGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketData ; sha256 294540c6aacecc52973886a062c74039a3759b405c27a557309a8c20a6e17675 -/
section





/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

variable
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ))
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂)
    (Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss : ℝ)
    (hBdyad₁ : 0 ≤ Bdyad₁) (hLdyad₁ : 0 ≤ Ldyad₁) (hCrdyad₁ : 0 < Crdyad₁)
    (hBdyad₂ : 0 ≤ Bdyad₂) (hLdyad₂ : 0 ≤ Ldyad₂) (hCrdyad₂ : 0 < Crdyad₂)
    (hdyadicLoss : 0 < dyadicLoss)
    (rowAbsorb : ℝ) (hrowAbsorb : 0 < rowAbsorb)
    (haSource_eq : aSource = (∏ j, lo j)*a₁*a₂)
variable (Z τ ν : ℝ)

/- This proposition lists literal source data and their geometric gates.
It contains no pointwise, density, population, or target-bound premise. -/
@[irreducible] def HighPacketSourceData (value exponent : ℝ) : Prop :=
  ∃ d : (ℝ),
  ∃ P : (ℝ),
  ∃ W : (ℝ),
  ∃ p : (DensityWindow),
  ∃ i : (ℕ),
  ∃ input : (Input Slot),
  ∃ puncture : (Ideal O),
  ∃ seed : (Ideal O),
  ∃ hpuncture : (puncture ≠ 0),
  ∃ hseed : (Squarefree seed),
  ∃ hz₁ : (input.W₁ 0 = 0),
  ∃ hz₂ : (input.W₂ 0 = 0),
  ∃ hinputη : (input.η=η),
  ∃ side : (Bool),
  ∃ ξ₁ : (RayCharacter),
  ∃ ξ₂ : (RayCharacter),
  ∃ fallback : (NonzeroJointSourceRow (original input puncture seed) side),
  ∃ K₁ : (ℝ),
  ∃ radius : ((p : Labels input puncture seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ),
  ∃ fallbackFirst : (First input puncture seed K₁ radius),
  ∃ K : (First input puncture seed K₁ radius → ℝ),
  ∃ Radius : (First input puncture seed K₁ radius → ℝ),
  ∃ Height : (First input puncture seed K₁ radius → ℝ),
  ∃ X : (Finset (Packet input puncture seed K₁ radius side K Radius Height)),
  ∃ hzero : (∀ x∈X,(row x).z≠0),
  ∃ R : (JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O),
  ∃ hR : (∀ v label, R v label ≠ 0),
  ∃ height : (First input puncture seed K₁ radius → ℝ),
  ∃ tbase : (let Kfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => K₁;
let Rfirst := fun q : NonzeroJointSourceRow (original input puncture seed) side => radius q.val.first q.val.E;
let Hfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => sourceRadius input;
(q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ),
  ∃ firstU : (let Kfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => K₁;
let Rfirst := fun q : NonzeroJointSourceRow (original input puncture seed) side => radius q.val.first q.val.E;
let Hfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => sourceRadius input;
(q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ),
  ∃ firstTheta : (let Kfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => K₁;
let Rfirst := fun q : NonzeroJointSourceRow (original input puncture seed) side => radius q.val.first q.val.E;
let Hfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => sourceRadius input;
(q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ),
  ∃ σ : (JointReconstructionLabel → Slot → ℝ),
  ∃ freq : (JointReconstructionLabel → Slot → ℝ),
  ∃ θ : (JointReconstructionLabel → Slot → RayQuotient.Characters M H),
  ∃ slotWidth : (JointReconstructionLabel → Slot → ℝ),
  ∃ Bmask : (ℝ),
  ∃ A : (ℝ),
  ∃ c : (ℝ),
  ∃ d₁ : (ℝ),
  ∃ π : (ℝ),
  ∃ R₁ : (ℝ),
  ∃ R₀ : (ℝ),
  ∃ E : (ℝ),
  ∃ Bc : (ℝ),
  ∃ L : (ℝ),
  ∃ b₂ : (ℝ),
  ∃ g₂ : (ℝ),
  ∃ t₂cost : (ℝ),
  ∃ omegaLoss : (ℝ),
  ∃ geometryLoss : (ℝ),
  ∃ lengthLoss : (ℝ),
  ∃ missingLoss : (ℝ),
  ∃ c₂ : (ℝ),
  ∃ d₂ : (ℝ),
  ∃ supportLoss : (ℝ),
  ∃ clipLoss : (ℝ),
  ∃ commonLoss : (ℝ),
  ∃ scalarLoss : (ℝ),
  ∃ rowc : (ℝ),
  ∃ rowd : (ℝ),
  ∃ rowR : (ℝ),
  ∃ rowe : (ℝ),
  ∃ rowomega : (ℝ),
  ∃ rowL : (ℝ),
  ∃ sourceLoss : (ℝ),
  ∃ subsetLoss : (ℝ),
  ∃ ξ : (ℝ),
  ∃ pMissing : (ℝ),
  ∃ rMissing : (ℝ),
  ∃ eMissing : (ℝ),
  ∃ cancelMissing : (ℝ),
  ∃ volumeLoss : (ℝ),
  let qs := rayRows fallbackFirst X hzero ξ₁ ξ₂;
  let Kfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => K₁;
  let Rfirst := fun q : NonzeroJointSourceRow (original input puncture seed) side => radius q.val.first q.val.E;
  let Hfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => sourceRadius input;
  let Ksecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst K ξ₁ ξ₂ q.val;
  let Rsecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst Radius ξ₁ ξ₂ q.val;
  let Hsecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst Height ξ₁ ξ₂ q.val;
  let good := fun (q : NonzeroJointSourceRow (original input puncture seed) side)
        (b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q)) =>
        (⟨q,b⟩ : FiberTarget fallbackFirst ξ₁ ξ₂ K Radius Height side)∈rayTarget fallbackFirst X hzero ξ₁ ξ₂;
  let S := qs.image NonzeroJointSourceRow.label;
  let unit := sourceUnit fallback η ξ₁ ξ₂⁻¹;
  let w := sourceRow fallback η ξ₁ ξ₂⁻¹;
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂⁻¹ 1 1;
  let first := sourceFirst fallback η ξ₁ ξ₂⁻¹;
  let z := sourceFrequency fallback;
  let Ds := fun v => (s v).physicalProjectors;
  let t := fun (q : NonzeroJointSourceRow (original input puncture seed) side)
        (n : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q)) => height (firstAt fallbackFirst q.val ξ₁ ξ₂ n);
  ((dmin ≤ d) ∧
  (d ≤ dmax) ∧
  (2 ≤ Z^d) ∧
  (2 < Z^τ) ∧
  (P ≤ B) ∧
  (W ≤ B) ∧
  (p.upper < p.lower+2*e) ∧
  (i ≤ I) ∧
  (p.height = (3*(i+1 : ℕ))*Z^τ) ∧
  ((∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v))) ∧
  (sourceRadius input ≤ Z^B) ∧
  ((∀ q ∈ qs, 0 < Kfirst q ∧ 0 < Hfirst q ∧
        Rfirst q ≤ Crdyad₁*Z^Ldyad₁ ∧ Hfirst q ≤ Z^Bdyad₁)) ∧
  ((∀ q ∈ qs, ∀ n₁, 0 < Ksecond q n₁ ∧
        Rsecond q n₁ ≤ Crdyad₂*Z^Ldyad₂ ∧ Hsecond q n₁ ≤ Z^Bdyad₂)) ∧
  ((∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain)) ∧
  ((∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j))) ∧
  ((∀ x∈X, ∃ rows : Finset O,
        activePhysicalRows
          (parent input puncture seed K₁ radius side x.1) (height x.1)
          (columns input puncture seed K₁ radius side x.1) (beta input puncture seed K₁ radius side x.1)
          Wkernel (K x.1) (Radius x.1) (Height x.1) x.2.1 rows ≠ 0)) ∧
  (W+Bmask+conductorReserve ≤ d) ∧
  ((∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask)) ∧
  ((∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂)) ∧
  ((∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z)) ∧
  ((∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth)) ∧
  ((∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth)) ∧
  ((∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        t q b.1 = tbase q b.1+2*Real.pi*(firstU q b.1-firstTheta q b.1))) ∧
  ((∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        |tbase q b.1| ≤ Z^ν ∧ |firstU q b.1| ≤ Z^ν ∧ |firstTheta q b.1| ≤ Z^ν)) ∧
  ((∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax)) ∧
  ((∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν)) ∧
  (2*b₂ = c₂+d₂) ∧
  (supportLoss+clipLoss+commonLoss ≤ lengthLoss) ∧
  ((∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A)) ∧
  ((∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ))) ∧
  ((∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss)) ∧
  (Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss) ∧
  (67/100 ≤ 2*p.lower-1) ∧
  (2*p.lower-1 ≤ 3/4) ∧
  (A ≤ 883/1000) ∧
  (0 ≤ π) ∧
  (π ≤ c) ∧
  (π ≤ d₁) ∧
  (R₁ ≤ π) ∧
  (0 ≤ R₀) ∧
  (0 ≤ E) ∧
  (0 ≤ Bc) ∧
  (L ≤ 5*(R₁-R₀)) ∧
  (0 ≤ b₂) ∧
  (g₂ ≤ b₂) ∧
  (0 ≤ t₂cost) ∧
  (0 ≤ geometryLoss) ∧
  (0 ≤ lengthLoss) ∧
  (W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss) ∧
  (P ≤ π-R₁-E+R₀+missingLoss) ∧
  (omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000) ∧
  (A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA) ∧
  (targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000) ∧
  ((∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        Ksecond q b.1 ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss)))) ∧
  ((∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss)) ∧
  (sourceRadius input ≤ Z^(A+sourceLoss)) ∧
  (1-rowR-max (rowc-rowd) 0+rowL-6*(3/500)-rowomega+
        2*sourceLoss+subsetLoss+ξ/2+rowAbsorb ≤ W) ∧
  (pMissing-rMissing-eMissing+cancelMissing ≤ P) ∧
  ((∀ q ∈ qs, Z^rowc ≤ (q.label.C₁.absNorm : ℝ) ∧
        normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(rowe+subsetLoss) ∧
        normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤ Z^rowL ∧
        Z^rMissing ≤ normValue (activeConductor q.label.C₁ q.label.D₁) ∧
        Z^eMissing ≤ normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ∧
        ((commonRadical q.label.C₁ q.label.D₁).absNorm : ℝ) ≤ Z^pMissing ∧
        ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ) ≤ Z^cancelMissing)) ∧
  ((∀ q ∈ qs, ∃ n₁ : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q),
        Z^(2*A-rowc-rowd+rowR+rowe-1+max (rowd-rowc) 0+6*(3/500)+rowomega) ≤ Ksecond q n₁ ∧
        Rsecond q n₁ = frequencyRadius
          ((sourceRadius input/(q.label.C₁.absNorm : ℝ))^2/Ksecond q n₁) Z ξ ∧
        q.val.z ∈ ActualJointSourceRow.liveFrequencyRows q.val.second.val.1 q.val.second.val.2
          q.val.U (Rsecond q n₁))) ∧
  (Z^(A-volumeLoss) ≤ CenteredMomentExceptionalAmplitudePair.volume input.toData)) ∧
  value = (∑ x∈rayPackets X ξ₁ ξ₂,
        packetValue hseed hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume input.toData)
          (actualHighPrimeCount M H Sbad Z) height Wkernel x) ∧ exponent = (π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000+dyadicLoss)

end FixedData
#print axioms HighPacketSourceData
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketData -/
