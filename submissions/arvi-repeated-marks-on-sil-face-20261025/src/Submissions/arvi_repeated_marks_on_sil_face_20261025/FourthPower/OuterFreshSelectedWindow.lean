/- Copyright (c) 2026 Sil. Apache-2.0.
Exact sharp-character outer windows and genuine-common reconstruction.
The selected cubic factor remains F^2, the artificial divisor remains the
seed of each live source, and the original normalization occurs once.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshSource
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstAvoidance
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstCanonicalGeometry
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstCommonSum
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshConsumer
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstLiveSource
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstSourceWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshSelectedWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentLattice CenteredMomentSourceRectangle CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentLiveDomain
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowSource CenteredMomentChildRows CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSmooth
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedCommonCoefficient MixedCommonRestriction MixedHeightEnergy MixedOriginalSecondZero
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOriginalFrequency
open MixedSupplierReconstruction MixedRestrictedDictionary MixedLiteralAllocation
open MixedFirstLiveSource MixedFirstPhysicalApplication MixedFirstSeededEnergy
open MixedFirstSourceWindow OuterFreshStructure OuterFreshNonexceptionalFamily
open OuterFreshWindowPair
open CanonicalRowCompletion FourierBridge CenteredMomentHeckeExpansion
open CenteredMomentCanonicalFirst CenteredMomentChildAssembly OuterFreshRows
open CenteredMomentUncenteredTerminal
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Exact finite column expansion for an arbitrary fixed test function.
No character or moment estimate enters this identity. -/
private theorem source_weighted_tuples (s : Source ι a b) (ha : 0<a)
    (D : Id) (f : Id→ℂ) :
    (∑I∈sourceColumns s,sourceCoefficient s ha D I*f I)=
      ∑v∈Fintype.piFinset (tuplePools s),originalTuple s ha D v*
        f (finiteTupleProduct v) :=
  finite_column_sum (Fintype.piFinset (tuplePools s)) (originalTuple s ha D) f

/-- Genuine complete-common extraction on the actual supported sector.
The test function may contain the selected cubic twist, physical row,
and Fourier window. Its only support premise is exact vanishing outside
the baseline supported ideals; this is proved below for the actual test. -/
theorem sector_weighted_allocated (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (G seed L : Id)
    (hG : Supported G) (hseed : seed∣G) (f : Id→ℂ)
    (hf : ∀I,¬Supported I→f I=0) :
    (∑I : sectorPool G hG.1 (sourceColumns s),originalResidual s ha seed G L I*f I)=
      ∑B : actualAllocations (tuplePools s) G,
        (frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*
        ∑I∈sourceColumns (allocatedLiveSource s hb cover G B),
          sourceCoefficient (allocatedLiveSource s hb cover G B) ha L I*f I := by
  have hsector :
      (∑I : sectorPool G hG.1 (sourceColumns s),originalResidual s ha seed G L I*f I)=
        ∑I∈residualPool G hG.1 (sourceColumns s),
          (if IsCoprime G I ∧ L∣I then sourceCoefficient s ha seed (G*I) else 0)*f I := by
    rw [Finset.sum_coe_sort (sectorPool G hG.1 (sourceColumns s))
      (fun I=>originalResidual s ha seed G L I*f I)]
    unfold sectorPool
    rw [←supported_residualPool G hG (sourceColumns s)]
    simp only [supportedColumns,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hs : Supported I
    · by_cases hc : IsCoprime G I <;> by_cases hl : L∣I <;>
        simp only [hs,hc,hl,originalResidual,ite_true,ite_false,true_and,false_and,
          and_true,and_false,zero_mul]
    · simp only [hs,ite_false,hf I hs,mul_zero]
  rw [hsector]
  have he := common_masked_column_sum (punctureProduct s.S s.H) (tuplePools s)
    (source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (fun i I hI=>s.hp i I hI) G s.R seed L hG.1 hseed s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 f
  apply he.trans
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun v : ℂ=>(frozenWeight (punctureProduct s.S s.H) B.val*
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*v)
  refine Eq.trans ?_ (source_weighted_tuples (allocatedLiveSource s hb cover G B) ha L f).symm
  apply Finset.sum_congr (live_source_box (allocationSource s hb cover G B)).symm
  intro v hv
  have hm := profile_seed_mask (punctureProduct s.S s.H) (s.R*G) L
    (fun i : liveIndices B.val=>s.ν i.val) (fun i=>s.Wslot i.val) (fun i=>s.P i.val)
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) v
  calc
    _ = (if L∣finiteTupleProduct v then tupleWeight (punctureProduct s.S s.H) v*
          liveProfile B.val G s.R s.ν s.Wslot s.P
            (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 v else 0)*f (finiteTupleProduct v) := by
      split_ifs <;> simp only [zero_mul]
    _ = _ := congrArg (fun w : ℂ=>w*f (finiteTupleProduct v)) hm

def windowAngle (conjugate : Bool) (θ : ℝ) : ℝ := if conjugate then -θ else θ

/-- The same physical log window on both sides. The right side changes
theta to -theta and, at the caller, z to -z; neither is identified away. -/
theorem physical_window (conjugate : Bool) (u θ : ℝ) :
    (if conjugate then star (columnPhase logAnnulus u θ) else columnPhase logAnnulus u θ)=
      columnPhase logAnnulus u (windowAngle conjugate θ) := by
  cases conjugate <;> simp only [windowAngle,Bool.false_eq_true,ite_false,ite_true,
    star_logAnnulus_column]

def residualWindow (conjugate : Bool) (s : Source ι a b) (ha : 0<a)
    (G : Id) (hG : Supported G) (seed L F : Id) (η : Character)
    (t θ X : ℝ) (z : O) : ℂ :=
  ∑I : sectorPool G hG.1 (sourceColumns s),
    (originalResidual s ha seed G L I*selectedTwist F I)*rowWeight η fixedBadMask 1 z t I*
      columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) (windowAngle conjugate θ)

/-- The actual residual window is a finite sum of original selected
windows on the genuine live sources. No artificial seed is discarded. -/
theorem residual_window_allocated (conjugate : Bool) (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (G seed L F : Id)
    (hG : Supported G) (hseed : seed∣G) (η : Character) (t θ X : ℝ) (z : O) :
    residualWindow conjugate s ha G hG seed L F η t θ X z=
      ∑B : actualAllocations (tuplePools s) G,
        (frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*
        windowedPolynomial (allocatedLiveSource s hb cover G B) ha L F
          η fixedBadMask 1 t logAnnulus X (windowAngle conjugate θ) z := by
  let f : Id→ℂ := fun I=>selectedTwist F I*rowWeight η fixedBadMask 1 z t I*
    columnPhase logAnnulus (Real.log ((I.absNorm:ℝ)/X)) (windowAngle conjugate θ)
  have hf (I : Id) (hI : ¬Supported I) : f I=0 := by
    dsimp only [f]
    rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
      (dvd_mul_right _ _) (dvd_mul_left _ _) I hI,mul_zero,zero_mul]
  have he := sector_weighted_allocated s ha hb cover G seed L hG hseed f hf
  simpa only [residualWindow,windowedPolynomial,selectedCoefficient,f,mul_assoc] using he

/-- Sharp physical character identity for the literal outer window.
G is one of the two actual common ideals. Their fixed family absorbs
the old moving parameter and f, while the selected F remains explicit. -/
theorem outer_window_sharp (conjugate : Bool) (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (τ : Character) (ξ χ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (seed G L : Id) (hG : Supported G) (hGE : G=C ∨ G=E) (t θ X : ℝ) (z : O) :
    outerWindow conjugate q x y s seed τ ξ χ (oldMoving C E U) G hG L t θ X z=
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G)*
      (normalization (s.X₁*s.X₂) s.P*
        residualWindow conjugate s ha G hG seed L (selectedProduct q y) (ψ χ) t θ X z) := by
  have hc (I : sectorPool G hG.1 (sourceColumns s)) :
      IsCoprime C I ∨ IsCoprime E I := by
    have hg := (Finset.mem_filter.mp I.property).2
    rcases hGE with h | h
    · exact Or.inl (h ▸ hg)
    · exact Or.inr (h ▸ hg)
  have he (I : sectorPool G hG.1 (sourceColumns s)) :=
    actual_child_coefficient q x y τ ξ χ C E hC hE U ψ hψ seed G L I
      (sectorPool_supported G hG.1 (sourceColumns s) I) (hc I) t z
  have hterm (I : sectorPool G hG.1 (sourceColumns s)) :
      divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
        (movingCoefficient (oldMoving C E U) (sectorElement G hG.1 (sourceColumns s))
          (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*
        idealRowHom z I=
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G)*
        ((originalResidual s ha seed G L I*selectedTwist (selectedProduct q y) I)*
          rowWeight (ψ χ) fixedBadMask 1 z t I) := by
    have hI := sectorPool_supported G hG.1 (sourceColumns s) I
    have hh := he I
    simp only [divisorCoefficient,movingCoefficient,primary_span_supported I hI] at hh
    simp only [divisorCoefficient,movingCoefficient,sectorElement,
      primary_span_supported I hI]
    rw [hh,common_coefficient q x s ha hm seed (G*I)]
    rw [rowWeight_split,heightCoeff_eq_fixed_rowWeight (ψ χ) t I hI]
    unfold originalResidual selectedTwist
    split_ifs <;> ring
  have hsum :
      rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
          (movingCoefficient (oldMoving C E U) (sectorElement G hG.1 (sourceColumns s))
            (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*
          (if conjugate then star (columnPhase logAnnulus
            (Real.log ((I.val.absNorm:ℝ)/X)) θ) else
            columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)) z=
        (gate q x*twist (primaryGenerator (frozenProduct q x))
          (primaryGenerator (selectedProduct q y)) ξ G)*
        residualWindow conjugate s ha G hG seed L (selectedProduct q y) (ψ χ) t θ X z := by
    unfold rowPolynomial residualWindow
    simp only [sectorElement_span,physical_window,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    calc
      _ = (divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
          (movingCoefficient (oldMoving C E U) (sectorElement G hG.1 (sourceColumns s))
            (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*
            idealRowHom z I)*columnPhase logAnnulus
              (Real.log ((I.val.absNorm:ℝ)/X)) (windowAngle conjugate θ) := by ring
      _ = _ := (congrArg (fun v : ℂ=>v*columnPhase logAnnulus
        (Real.log ((I.val.absNorm:ℝ)/X)) (windowAngle conjugate θ)) (hterm I)).trans
          (by ring)
  unfold outerWindow
  rw [hsum]
  ring

/-- Complete exact reconstruction of the actual sharp outer window.
This is the boundary to artificial-seed/prefix reconstruction: all live
sources, their physical profiles and both original ordinary heights are
literal data, with no energy estimate supplied as a hypothesis. -/
theorem outer_window_allocated (conjugate : Bool) (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (hb : 0≤b) (cover : OriginalEnclosure s)
    (τ : Character) (ξ χ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (seed G L : Id) (hG : Supported G) (hGE : G=C ∨ G=E) (hseed : seed∣G)
    (t θ X : ℝ) (z : O) :
    outerWindow conjugate q x y s seed τ ξ χ (oldMoving C E U) G hG L t θ X z=
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G)*
      (normalization (s.X₁*s.X₂) s.P*
        ∑B : actualAllocations (tuplePools s) G,
          (frozenWeight (punctureProduct s.S s.H) B.val*
            frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*
          windowedPolynomial (allocatedLiveSource s hb cover G B) ha L (selectedProduct q y)
            (ψ χ) fixedBadMask 1 t logAnnulus X (windowAngle conjugate θ) z) := by
  rw [outer_window_sharp conjugate q x y s ha hm τ ξ χ C E hC hE U ψ hψ
    seed G L hG hGE t θ X z,
    residual_window_allocated conjugate s ha hb cover G seed L (selectedProduct q y)
      hG hseed (ψ χ) t θ X z]

/-- Exact common Fourier density after genuine extraction. The angle
is theta on the left and -theta on the right; physical z is unchanged
by the integral. Thus the actual right caller retains -z throughout.
The density is chosen before the selected product and every allocation. -/
theorem residual_window_integral_allocated (conjugate : Bool)
    (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G seed L F : Id) (hG : Supported G) (hseed : seed∣G)
    (η : Character) (t θ X : ℝ) (hX : 0<X) (z : O) :
    residualWindow conjugate s ha G hG seed L F η t θ X z=
      ∑B : actualAllocations (tuplePools s) G,
        (frozenWeight (punctureProduct s.S s.H) B.val*
          frozenCoefficient B.val G s.R s.ν s.Wslot s.P)*
        ∫w : ℝ,columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w*
          logPhase (windowAngle conjugate θ-w) (Real.log X)*
          selectedPolynomial (allocatedLiveSource s hb cover G B) ha L F
            η fixedBadMask 1 (t+2*Real.pi*(w-windowAngle conjugate θ)) z := by
  rw [residual_window_allocated conjugate s ha hb cover G seed L F hG hseed η t θ X z]
  apply Finset.sum_congr rfl
  intro B hB
  rw [selected_window_integral (allocatedLiveSource s hb cover G B) ha L F
    η fixedBadMask 1 t logAnnulus logAnnulus_compact logAnnulus_smooth
    X (windowAngle conjugate θ) hX z]

end
end Candidate.FourthPower.OuterFreshSelectedWindow

/- Actual avoidance and canonical provenance for the same windows. -/
namespace Candidate.FourthPower.OuterFreshSelectedWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedOriginalNormCap MixedOriginalTail MixedSupplierFourthRow MixedSupplierSource
open MixedFirstLiveSource MixedFirstAvoidance MixedFirstActualNonexceptional
open MixedFirstPhysicalApplication MixedFirstSourceWindow MixedFirstCommonSum
open MixedCanonicalSource MixedFrozenSource ReferencePrimeEnclosure OuterFreshSource
open OuterFreshWindowPair
open CenteredMomentSourceLiveColumn QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The unavoided companion changes ONLY the marked coefficient.
All original data and the full puncture R*f are unchanged. -/
def unavoidedResidual (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    Source (RestIndex (supplierData s ha u L J)) a b :=
  {residualSource s ha cover u L J x with
    ν := fun j=>s.ν j.val.val
    hν := fun j I=>s.hν j.val.val I}

theorem residual_is_avoided (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    residualSource s ha cover u L J x=
      avoidSource (unavoidedResidual s ha cover u L J x) u := rfl

theorem unavoided_enclosure (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    OriginalEnclosure (unavoidedResidual s ha cover u L J x) := cover

/-- The actual supplier relation discharges the avoidance divisibility
gate after genuine extraction. No cardinality bound on primeSupport u
is used or inferred. -/
theorem actual_allocated_coefficient (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed G : Id)
    (hu : u=frozenProduct (supplierData s ha u L J) x*seed) (hseed : seed∣G)
    (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G)
    (D I : Id) :
    sourceCoefficient (allocatedLiveSource (residualSource s ha cover u L J x)
      hb cover G B) ha D I=
    sourceCoefficient (allocatedLiveSource (unavoidedResidual s ha cover u L J x)
      hb cover G B) ha D I := by
  have hdiv : u∣(unavoidedResidual s ha cover u L J x).R*G :=
    supplier_dvd_puncture s.R (frozenProduct (supplierData s ha u L J) x) seed u G hu hseed
  exact allocated_coefficients (unavoidedResidual s ha cover u L J x) ha hb cover u G hdiv B D I

/-- Exact whole selected window equality, not an inequality between
signed sums. Original F, seed, masks, physical height and window survive. -/
theorem actual_allocated_window (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed G : Id)
    (hu : u=frozenProduct (supplierData s ha u L J) x*seed) (hseed : seed∣G)
    (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G)
    (D F : Id) (η : Character) (m A : O) (t : ℝ) (V : ℝ→ℂ) (X θ : ℝ) (z : O) :
    windowedPolynomial (allocatedLiveSource (residualSource s ha cover u L J x)
      hb cover G B) ha D F η m A t V X θ z=
    windowedPolynomial (allocatedLiveSource (unavoidedResidual s ha cover u L J x)
      hb cover G B) ha D F η m A t V X θ z := by
  unfold windowedPolynomial selectedCoefficient
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_allocated_coefficient s ha hb cover u L J x seed G hu hseed B D I]

/-- The frozen avoidance factor is still present after the exact live
equality. Its norm is paid only after the positive allocation estimate. -/
theorem actual_frozen_cost (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u G : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G) :
    let r:=unavoidedResidual s ha cover u L J x
    ‖frozenWeight (punctureProduct r.S r.H) B.val*
      frozenCoefficient B.val G r.R (residualSource s ha cover u L J x).ν r.Wslot r.P‖^2≤
    ‖frozenWeight (punctureProduct r.S r.H) B.val*
      frozenCoefficient B.val G r.R r.ν r.Wslot r.P‖^2 := by
  exact frozen_weight_le (unavoidedResidual s ha cover u L J x) u G B

/-- No extra marked slot or profile control is created by genuine
extraction. The ordinary prefixPair is retained in the full source cap. -/
theorem allocated_size_caps (r : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure r) (G : Id) (B : actualAllocations (tuplePools r) G) :
    let live:=allocatedLiveSource r hb cover G B
    Fintype.card (liveIndices B.val)≤Fintype.card ι ∧
      (∏i,2*live.P i)≤∏i,2*r.P i ∧ (∏i,live.M i)≤∏i,r.M i ∧
      sourceNormCap live.P b live.T live.d≤sourceNormCap r.P b r.T r.d := by
  refine ⟨?_,?_,?_,live_norm_cap (allocationSource r hb cover G B)⟩
  · rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  · exact injected_prod_le (fun i : liveIndices B.val=>i.val) Subtype.val_injective
      (fun i=>2*r.P i) (fun i=>by linarith [r.hP i])
  · exact injected_prod_le (fun i : liveIndices B.val=>i.val) Subtype.val_injective r.M r.hM

theorem residual_norm_cap (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    sourceNormCap (unavoidedResidual s ha cover u L J x).P b
      (unavoidedResidual s ha cover u L J x).T (unavoidedResidual s ha cover u L J x).d≤
      sourceNormCap s.P b s.T s.d := by
  exact mul_le_mul_of_nonneg_left (residual_scale_product s ha cover u L J x)
    (mul_nonneg (sq_nonneg _) (div_nonneg s.total_pos.le (pairNorm_pos s.hd.1 s.hd.2).le))

/-- Actual common labels supply full ideal-norm caps. These are not
radical bounds, and do not use a guessed polynomial radius. -/
theorem actual_common_norm_caps (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed : Id)
    (p : Labels (residualSource s ha cover u L J x) ha seed) :
    (p.val.1.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d ∧
      (p.val.2.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d := by
  apply commonLabel_norm_bounds (sourceColumns (residualSource s ha cover u L J x))
    (sourceCoefficient (residualSource s ha cover u L J x) ha seed) _ _
    p.val.1 p.val.2 p.property
  intro I hI hn
  exact (original_coefficient_cap (residualSource s ha cover u L J x) ha seed I hn).2.trans
    (residual_norm_cap s ha cover u L J x)

/-- The same bound on the actual D-independent fixedPool used by the
outer consumer. Its commonColumn scalar gate is retained; nonzero
commonColumn implies a nonzero literal residual source coefficient. -/
theorem actual_fixed_common_norm_caps (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J)) (seed : Id)
    (p : OuterFreshConsumer.FixedLabel
      (OuterFreshConsumer.fixedPool (supplierData s ha u L J) x
        (residualSource s ha cover u L J x) seed)) :
    (p.val.1.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d ∧
      (p.val.2.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d := by
  apply commonLabel_norm_bounds (sourceColumns (residualSource s ha cover u L J x))
    (commonColumn (supplierData s ha u L J) x seed) _ _ p.val.1 p.val.2 p.property
  intro I hI hn
  have hc := common_coefficient (supplierData s ha u L J) x
    (residualSource s ha cover u L J x) ha (residual_matches s ha cover u L J x) seed I
  rw [hc] at hn
  exact (original_coefficient_cap (residualSource s ha cover u L J x) ha seed I
    (mul_ne_zero_iff.mp hn).2).2.trans (residual_norm_cap s ha cover u L J x)

/-- Exact full-puncture cost of the genuine live source. All dependence
on the fixed supplier and genuine common ideal remains visible. -/
theorem allocated_puncture_norm (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (hx : MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (G : Id) (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G) :
    ((allocatedLiveSource (unavoidedResidual s ha cover u L J x) hb cover G B).R.absNorm:ℝ)≤
      (s.R.absNorm:ℝ)*(∏i,2*s.P i)*(G.absNorm:ℝ) := by
  change (((s.R*frozenProduct (supplierData s ha u L J) x)*G).absNorm:ℝ)≤_
  simp only [map_mul,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (frozen_norm_le s ha u L J x hx) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- Direct inherited caps against the original source, after BOTH the
supplier restriction and the genuine common allocation. -/
theorem allocated_original_caps (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (G : Id)
    (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G) :
    let r:=allocatedLiveSource (unavoidedResidual s ha cover u L J x) hb cover G B
    Fintype.card (liveIndices B.val)≤Fintype.card ι ∧
      (∏i,2*r.P i)≤∏i,2*s.P i ∧ (∏i,r.M i)≤∏i,s.M i ∧
      sourceNormCap r.P b r.T r.d≤sourceNormCap s.P b s.T s.d ∧
      r.B=(fun _=>1) ∧ r.G=1 ∧ r.T=s.T ∧
      r.d=(s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) ∧
      r.X₁=s.X₁ ∧ r.X₂=s.X₂ ∧ r.Y₁=s.Y₁ ∧ r.Y₂=s.Y₂ ∧
      r.W₁=s.W₁ ∧ r.W₂=s.W₂ ∧ r.t₁=s.t₁ ∧ r.t₂=s.t₂ := by
  have hh:=allocated_size_caps (unavoidedResidual s ha cover u L J x) hb cover G B
  exact ⟨hh.1.trans (rest_card_le (supplierData s ha u L J)),
    hh.2.1.trans (residual_scale_product s ha cover u L J x),
    hh.2.2.1.trans (residual_slot_mass s ha cover u L J x),
    hh.2.2.2.trans (residual_norm_cap s ha cover u L J x),
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Canonical data pass to the unavoided residual by restriction of
the original finite slot index, with the SAME R0 and ambient character. -/
theorem residual_canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (ha : 0<a) (cover : OriginalEnclosure s) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J)) :
    Canonical M Hray hHray W Cap Lcap Z η₀
      (fun j : RestIndex (supplierData s ha u L J)=>θ j.val.val)
      (fun j=>w j.val.val) (fun j=>σ j.val.val) (fun j=>freq j.val.val) t
      (fun j=>R₀ j.val.val) (unavoidedResidual s ha cover u L J x) := by
  obtain ⟨hS,hpool,hν,hW,hP⟩ := hs
  refine ⟨hS,?_,?_,?_,?_⟩
  · change (fun j : RestIndex (supplierData s ha u L J)=>s.pool j.val.val)=_
    simpa only [hpool]
  · change (fun j : RestIndex (supplierData s ha u L J)=>s.ν j.val.val)=_
    rw [hν]
    rfl
  · change (fun j : RestIndex (supplierData s ha u L J)=>s.Wslot j.val.val)=_
    simpa only [hW]
  · change (fun j : RestIndex (supplierData s ha u L J)=>s.P j.val.val)=_
    simpa only [hP]

/-- Genuine allocation preserves Canonical on its unavoided live
source. Whole puncture R*G and both enlarged ordinary prefixes are data
of Source, not new character conductor or new bounded slot-hole sets. -/
theorem allocated_canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    Canonical M Hray hHray W Cap Lcap Z η₀
      (fun i : liveIndices B.val=>θ i.val) (fun i=>w i.val)
      (fun i=>σ i.val) (fun i=>freq i.val) t (fun i=>R₀ i.val)
      (allocatedLiveSource s hb cover G B) := by
  obtain ⟨hS,hpool,hν,hW,hP⟩ := hs
  refine ⟨hS,?_,?_,?_,?_⟩
  · change (fun i : liveIndices B.val=>s.pool i.val)=_
    simpa only [hpool]
  · change (fun i : liveIndices B.val=>s.ν i.val)=_
    rw [hν]
    rfl
  · change (fun i : liveIndices B.val=>s.Wslot i.val)=_
    simpa only [hW]
  · change (fun i : liveIndices B.val=>s.P i.val)=_
    simpa only [hP]

/- APPENDIX ONLY for the existing OuterFreshSelectedWindow namespace.
Requires its existing MixedFirstLiveSource/MixedLiveNormalization imports
and additionally opens MixedInnerExceptionalBlock for sourceVolume.
No new analytic estimate. Parent alone runs the Lean checker.
-/

open MixedInnerExceptionalBlock

/-- A genuine live source has fewer marked normalizers but the SAME
ordinary product. This is the exact conversion needed before using its
volume-normalized selected window estimate. -/
theorem allocated_normalization_ratio (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    ‖normalization (s.X₁*s.X₂) s.P‖^2*
      sourceVolume (allocatedLiveSource s hb cover G B)=
      (∏i : liveIndices B.val,s.P i.val)/(∏i,s.P i) := by
  have hT : 0<s.X₁*s.X₂ := by rw [s.hpX];exact s.total_pos
  have hP : 0<∏i,s.P i := Finset.prod_pos (fun i _=>zero_lt_one.trans_le (s.hP i))
  rw [normalization_sq (s.X₁*s.X₂) hT s.P (fun i=>zero_lt_one.trans_le (s.hP i))]
  change (1/((s.X₁*s.X₂)*(∏i,s.P i)))*
    ((s.X₁*s.X₂)*(∏i : liveIndices B.val,s.P i.val))=_
  field_simp [(s.hL.trans_le s.hX₁).ne',(s.hL.trans_le s.hX₂).ne',hP.ne'] <;> ring

/-- Exact paid scalar after applying the seeded-window bound to one
genuine allocation. Both original ordinary prefixes and the artificial
seed norm remain in the denominator; no reciprocal live volume is added.
This equality is valid even for E=0 and uses no analytic premise. -/
theorem allocated_paid_normalization (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (c : ℂ) (D : Id) (E : ℝ) :
    ‖normalization (s.X₁*s.X₂) s.P‖^2*‖c‖^2*
      (sourceVolume (allocatedLiveSource s hb cover G B)*
        (E/(pairNorm (allocatedLiveSource s hb cover G B).d*(D.absNorm:ℝ))))=
      (‖c‖^2*((∏i : liveIndices B.val,s.P i.val)/(∏i,s.P i))*E)/
        (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))*(D.absNorm:ℝ)) := by
  have hd : (allocatedLiveSource s hb cover G B).d=
      (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) := rfl
  rw [hd]
  calc
    _=(‖normalization (s.X₁*s.X₂) s.P‖^2*
        sourceVolume (allocatedLiveSource s hb cover G B))*‖c‖^2*
        (E/(pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))*(D.absNorm:ℝ))) := by ring
    _=_ := by rw [allocated_normalization_ratio];ring

end
end Candidate.FourthPower.OuterFreshSelectedWindow
