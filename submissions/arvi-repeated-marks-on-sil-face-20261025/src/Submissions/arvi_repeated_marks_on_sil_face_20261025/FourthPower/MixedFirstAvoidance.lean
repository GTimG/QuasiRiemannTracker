/- Copyright (c) 2026 Sil. Apache-2.0.
Exact supplier avoidance transport on the actual four allocated first
components. The avoided Source need not be Canonical. No conductor is
enlarged, no hole-cardinality condition is added, and no Cauchy is repeated.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstFourParts
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstAvoidance
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondWindowBudget
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedOriginalNormCap MixedOriginalSecondZero MixedSupplierSource
open MixedFirstLiveSource MixedFirstLiveEnergy MixedFirstActualNonexceptional
open MixedFirstAllocatedRemainders MixedFirstFourParts MixedPoissonLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Only the original marked coefficients change. In particular the
whole puncture, pools, heights, both full prefixes, and all caps stay fixed. -/
def avoidSource (s : Source ι a b) (u : Id) : Source ι a b :=
  {s with ν := avoid u s.ν
          hν := by
            intro i I
            by_cases h : I∣u
            · simp only [avoid,if_pos h,norm_zero];norm_num
            · simpa only [avoid,if_neg h] using s.hν i I}

theorem avoided_tuple_pools (s : Source ι a b) (u : Id) :
    tuplePools (avoidSource s u)=tuplePools s := rfl

theorem avoided_enclosure (s : Source ι a b) (u : Id) (cover : OriginalEnclosure s) :
    OriginalEnclosure (avoidSource s u) := cover

/-- Exact live-column equality. The new live seed D, natural coprimality
zeros and the actual original restricted tuple weight are retained. -/
theorem allocated_coefficients (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u G : Id) (hu : u∣s.R*G)
    (B : actualAllocations (tuplePools s) G) (D I : Id) :
    sourceCoefficient (allocatedLiveSource (avoidSource s u) hb cover G B) ha D I=
      sourceCoefficient (allocatedLiveSource s hb cover G B) ha D I := by
  change sourceCoefficient (liveSource (allocationSource (avoidSource s u) hb cover G B)) ha D I=
    sourceCoefficient (liveSource (allocationSource s hb cover G B)) ha D I
  rw [live_source_coefficient,live_source_coefficient]
  split_ifs with hD
  · unfold finiteColumnCoefficient
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [allocationSource,avoidSource]
    rw [live_profile_avoid u G s.R hu]
    intro i
    have hv' := (Finset.mem_filter.mp hv).1
    rw [MixedLiveRows.live_box] at hv'
    exact s.hp i.val _ (Fintype.mem_piFinset.mp hv' (Sum.inl i))
  · rfl

/-- A source-independent description of the four exact positive pieces.
Hsource is the SAME literal sourceNormCap in the subtraction and add-back. -/
def columnComponents (S : Finset Id) (β : Id→ℂ) (Hsource : ℝ)
    (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) : Fin 4→ℝ :=
  ![‖zeroDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S=>β I*heightCoeff τ t I) K W‖,
    ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S=>β I*heightCoeff τ t I)
        K W (retainedWeight (frequencyRadius Tsec Z ξ))-
      partEnergy true τ χ₀ Q m t S β ballProfile (16*K*W^4) Tsec Z ξ Hsource/(W:ℂ)‖,
    ‖partEnergy true τ χ₀ Q m t S β
        ballProfile (16*K*W^4) Tsec Z ξ Hsource/(W:ℂ)‖,
    ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S=>β I*heightCoeff τ t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖]

theorem column_components_nonneg (S : Finset Id) (β : Id→ℂ) (Hsource : ℝ)
    (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) (i : Fin 4) :
    0≤columnComponents S β Hsource τ t K W Tsec Z ξ Q m χ₀ i := by
  fin_cases i <;> exact norm_nonneg _

/-- This is the definition of the existing four components, with their
common allocation sum exposed. No component estimate is assumed. -/
theorem components_as_columns (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G D : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) (i : Fin 4) :
    components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i=
      allocationSum s G (fun B=>
        let live := allocatedLiveSource s hb cover G B
        columnComponents (sourceColumns live) (sourceCoefficient live ha D)
          (sourceNormCap live.P b live.T live.d) τ t K W Tsec Z ξ Q m χ₀ i) := by
  fin_cases i <;> rfl

/-- Actual equality of all four live pieces, before the outer frozen
weight. Dependence of physical labels on beta is transported by equality
of the entire coefficient function, not by a pointwise norm comparison. -/
theorem live_components_equal (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u G : Id) (hu : u∣s.R*G)
    (B : actualAllocations (tuplePools s) G) (D : Id) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) (i : Fin 4) :
    let left := allocatedLiveSource (avoidSource s u) hb cover G B
    let right := allocatedLiveSource s hb cover G B
    columnComponents (sourceColumns left) (sourceCoefficient left ha D)
      (sourceNormCap left.P b left.T left.d) τ t K W Tsec Z ξ Q m χ₀ i=
    columnComponents (sourceColumns right) (sourceCoefficient right ha D)
      (sourceNormCap right.P b right.T right.d) τ t K W Tsec Z ξ Q m χ₀ i := by
  dsimp only
  have he : sourceCoefficient (allocatedLiveSource (avoidSource s u) hb cover G B) ha D=
      sourceCoefficient (allocatedLiveSource s hb cover G B) ha D :=
    funext (allocated_coefficients s ha hb cover u G hu B D)
  rw [he]
  rfl

/-- The only inequality in the transport: the exact frozen avoidance
factor has norm at most one. No comparison of signed live sums occurs. -/
theorem frozen_weight_le (s : Source ι a b) (u G : Id)
    (B : actualAllocations (tuplePools s) G) :
    ‖frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val G s.R (avoid u s.ν) s.Wslot s.P‖^2≤
      ‖frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2 := by
  rw [frozen_coefficient_avoid]
  have he : frozenWeight (punctureProduct s.S s.H) B.val*
      (frozenAvoid u B.val*frozenCoefficient B.val G s.R s.ν s.Wslot s.P)=
      frozenAvoid u B.val*(frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val G s.R s.ν s.Wslot s.P) := by ring
  rw [he,norm_mul]
  apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_right (frozen_avoid_norm u B.val) (norm_nonneg _)).trans_eq
    (one_mul _)

/-- All four actual allocated components of the avoided source are
bounded by the same-geometry unavoided components. In particular the
Canonical hypothesis is needed only for s, never for avoidSource s u. -/
theorem avoided_components_le (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u G : Id) (hu : u∣s.R*G) (D : Id)
    (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) (i : Fin 4) :
    components (avoidSource s u) ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i≤
      components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i := by
  rw [components_as_columns,components_as_columns]
  unfold allocationSum
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  have he := live_components_equal s ha hb cover u G hu B D τ t K W Tsec Z ξ Q m χ₀ i
  exact mul_le_mul (frozen_weight_le s u G B) (le_of_eq he)
    (column_components_nonneg _ _ _ τ t K W Tsec Z ξ Q m χ₀ i) (sq_nonneg _)

/-- Actual first residual energy, not an assumed supplier bound. Apply
the existing positive-Cauchy/four-part theorem once to the avoided source,
then the exact finite transport above. Outside 1/W is unchanged. -/
theorem avoided_actual_energy_four_parts (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (u C G seed D : Id)
    (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C=
      QRH.Record1252270103KernelMass.primeSupport G)
    (hseed : seed∣G) (hu : u∣s.R*G) (τ : Character)
    (t K W Tsec Z ξ : ℝ) (hK : 0<K) (hW : 0<W) (Q : Id) (m : O)
    (χ₀ : RayCharacter) :
    actualEnergy (avoidSource s u) ha C G hG seed D τ t K W≤
      ∑i,components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i :=
  (actual_energy_four_parts (avoidSource s u) ha hb cover C G seed D hC hG hCG hseed
    τ t K W Tsec Z ξ hK hW Q m χ₀).trans
      (Finset.sum_le_sum (fun i _=>
        avoided_components_le s ha hb cover u G hu D τ t K W Tsec Z ξ Q m χ₀ i))

/-- The actual endpoint discharges the live-hole condition using its
whole original puncture and genuine common label. It need not assume it. -/
theorem supplier_avoided_components_le (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (R f seed u G D : Id)
    (hR : s.R=R*f) (hu : u=f*seed) (hseed : seed∣G)
    (τ : Character) (t K W Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) (i : Fin 4) :
    components (avoidSource s u) ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i≤
      components s ha hb cover G D τ t K W Tsec Z ξ Q m χ₀ i := by
  apply avoided_components_le s ha hb cover u G
  rw [hR]
  exact supplier_dvd_puncture R f seed u G hu hseed

end
end Candidate.FourthPower.MixedFirstAvoidance
