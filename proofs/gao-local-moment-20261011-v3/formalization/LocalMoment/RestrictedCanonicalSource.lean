import OAI.NumberTheory.DirichletL.Energy.AllocatedChildren
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Energy.ChildState

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.LocalMomentRestrictedCanonical
open HeckeFamily CenteredMomentRadialEligibleEnergy CenteredMomentEnergyState
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalRadial
open CenteredMomentAllocatedNaturalSource
open CenteredMomentDivisorAllocation CenteredMomentRetainedProfile
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

/-- Restriction changes no smooth profile, scale, natural character, fixed ideal,
or puncture.  The unsmoothed predicate stays solely in the row sum. -/
def restrictRadial (r : Radial) (low : O → Prop) : Radial :=
  { r with keep := fun z => r.keep z ∧ low z }

def restrictState {Z Bmask bPhi : ℝ} (s : NaturalState Z Bmask bPhi)
    (low : O → Prop) : NaturalState Z Bmask bPhi :=
  { s with
    radial := restrictRadial s.radial low
    row_ne_zero := fun z hz => s.row_ne_zero z hz.1
    nonexceptional := fun z hz => s.nonexceptional z hz.1 }

@[simp] theorem restrictState_width {Z Bmask bPhi : ℝ}
    (s : NaturalState Z Bmask bPhi) (low : O → Prop) :
    (restrictState s low).width = s.width := rfl

/-- The source's allocated natural coefficient factorization holds exactly
with the low predicate on the actual canonical radial state. -/
theorem actual_common_child_restricted {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (tau : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (V1 V2 : Plain) (Q : Ideal O) (n : Fin 4 → ℤ) (low : O → Prop)
    (left : Bool) (D1 D2 : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD1 : ∀ I ∈ D1, I ≠ 0) (hD2 : ∀ I ∈ D2, I ≠ 0) :
    radialEnergy (fun z => commonChild s tau v C R B D alloc V1 V2 left z D1 D2 J)
      (fun z => (canonicalRadial tau Q n).keep z ∧ low z)
      (canonicalRadial tau Q n).profile (canonicalRadial tau Q n).scale =
    commonAllocatedEnergy s tau v C R B D alloc V1 V2
      (restrictRadial (canonicalRadial tau Q n) low) left D1 D2 J := by
  exact commonChild_energy s tau v C R B D alloc V1 V2
    (restrictRadial (canonicalRadial tau Q n) low)
    (fun z hz => hz.1.1) left D1 D2 J hD1 hD2

/-- The padded enlarged main ball contains every amplified retained row. -/
theorem enlarged_main_covers (K K0 c d a omega delta1 : ℝ)
    (hK : K ≤ K0+delta1) (hw : delta1 ≤ omega) :
    K+6*a ≤ K0+max (d-c) 0+6*a+omega := by
  have hmax := le_max_right (d-c) 0
  linarith

/-- The proposed padded radius is already the source's common main radius. -/
theorem enlarged_main_is_existing_radius (Z d K0 c a delta reserve : ℝ) :
    CenteredMomentAmplifiedRetainedRadius.mainCommonRadius Z d K0 c
      (3*a) delta reserve = Z^(K0+max (d-c) 0+6*a+(delta+reserve)) := by
  unfold CenteredMomentAmplifiedRetainedRadius.mainCommonRadius
  congr 1
  ring

/-- B3.63 at the enlarged ball, with zero old moving width and main extraction.
The new main radius is used directly; no old mainRadius hypothesis occurs. -/
theorem enlarged_main_width (M A c d R E g2 t2 V a omega : ℝ) :
    let K0 := 2*A-c-d+R+E-M
    let H := K0+max (d-c) 0+6*a+omega
    let mChild := 2*(A-c)-H-g2-V
    let qChild := R+E+t2+V
    mChild+qChild = M-max (c-d) 0-6*a-omega-g2+t2 := by
  dsimp only
  by_cases h : c ≤ d
  · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
    ring
  · have hdc : d ≤ c := (lt_of_not_ge h).le
    rw [max_eq_right (sub_nonpos.mpr hdc),max_eq_left (sub_nonneg.mpr hdc)]
    ring

/-- Including a fixed parent modulus q gives the same ledger at M=m+q. -/
theorem enlarged_main_width_fixed_modulus (m q A c d R E g2 t2 V a omega : ℝ) :
    let K0 := 2*A-c-d+R+E-m
    let H := K0+max (d-c) 0+6*a+omega
    let mChild := 2*(A-c)-H-g2-V
    let qChild := q+R+E+t2+V
    mChild+qChild = (m+q)-max (c-d) 0-6*a-omega-g2+t2 := by
  dsimp only
  have h := enlarged_main_width m A c d R E g2 t2 V a omega
  dsimp only at h
  linarith

/-- This is the exact pre-allocation fine defect increment on the C side. -/
theorem enlarged_main_defect_increment (M A c d c2 g2 t2 a omega : ℝ) :
    (A-c-c2-(M-max (c-d) 0-6*a-omega-g2+t2))-(A-M) =
      6*a+omega-min c d-(c2-g2)-t2 := by
  by_cases h : c ≤ d
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h]
    ring
  · have hdc : d ≤ c := (lt_of_not_ge h).le
    rw [max_eq_left (sub_nonneg.mpr hdc),min_eq_right hdc]
    ring

#print axioms actual_common_child_restricted
#print axioms enlarged_main_covers
#print axioms enlarged_main_is_existing_radius
#print axioms enlarged_main_width
#print axioms enlarged_main_width_fixed_modulus
#print axioms enlarged_main_defect_increment
end SevenEighths.LocalMomentRestrictedCanonical
end
end OAI
