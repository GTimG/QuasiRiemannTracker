/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal annular/ray metadata for the P.3 short source. The compact profile
bound is Sil's authentic uniform slot_profile_bound (Apache-2.0). -/
import Candidate.C092.transport.ReferenceShortP3Reference
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFrozenSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.NativeStrip
open QRH.Cycle092.WholeSlot QRH.Cycle092.CofactorOrdinary
open QRH.SilDensitySplit.CubeFree.FP.MixedCanonicalSource (slotProfile)
local notation "O" => HeckeFamily.O

theorem actual_slot_profile_metadata (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (lo hi : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ σ v : ℝ, lo ≤ σ → σ ≤ hi →
      Function.support (slotProfile W σ v) ⊆ Set.Icc (1:ℝ) 2 ∧
      ∀ x : ℝ, ‖slotProfile W σ v x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := QRH.SilDensitySplit.CubeFree.FP.MixedFrozenSource.slot_profile_bound
    W hW hWs lo hi
  refine ⟨M,hM,?_⟩
  intro σ v hlo hhi
  refine ⟨?_,hbound σ v hlo hhi⟩
  intro x hx
  apply hWs
  intro hz
  exact hx (by simp only [slotProfile,hz,zero_mul])

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem original_pool_prime (U : ℝ) (w : ι→ℝ) (i : ι) (I : Ideal O)
    (hI : I∈originalPools rayM Hr 2 U w i) : Prime I :=
  (Finset.mem_filter.mp hI).2.1

theorem actual_ray_coefficient_bound (η₀ : Character)
    (θ : ι → RayQuotient.Characters rayM Hr) (i : ι) (I : Ideal O) :
    ‖idealCoeff (relativeCharacter rayM Hr hHr η₀ (θ i)) I‖ ≤ 1 :=
  idealCoeff_norm_le_one _ _

theorem original_coefficient_split (η₀ : Character)
    (θ : ι → RayQuotient.Characters rayM Hr) (W : ℝ→ℂ)
    (U : ℝ) (w σ v : ι→ℝ) (i : ι) (I : Ideal O) :
    originalCoefficients rayM Hr hHr η₀ θ W U w σ v i I =
      idealCoeff (relativeCharacter rayM Hr hHr η₀ (θ i)) I *
        slotProfile W (σ i) (v i) ((Ideal.absNorm I:ℝ)/(U^(w i))) := rfl

#print axioms actual_slot_profile_metadata
#print axioms original_pool_prime
#print axioms actual_ray_coefficient_bound
#print axioms original_coefficient_split
end
end QRH.Cycle092.ReferenceShortP3
