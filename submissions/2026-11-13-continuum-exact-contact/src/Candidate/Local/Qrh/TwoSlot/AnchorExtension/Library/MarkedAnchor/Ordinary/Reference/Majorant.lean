/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
A fixed radial majorant at support scale `b` and the passage from the lane's finite
`initialWeight` sums (weight `Φ`, bounded by `radialControl Φ`) to the parent's radial energy
with the fixed majorant profile (whose `diagonalControl` is a constant). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Statement
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison CenteredMomentDetectorPlainFiberSource
open QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource
open QRH.SilDensitySplit.CubeFree.FP.MixedFirstReferenceEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The fixed radial majorant `x ↦ radialMajorant (x / b)`. -/
def majorant (b : ℝ) (hb : 0 < b) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 b⁻¹ (inv_ne_zero hb.ne')))
    radialMajorant

theorem majorant_apply (b : ℝ) (hb : 0 < b) (x : ℝ) :
    majorant b hb x = radialMajorant (x*b⁻¹) := by
  simp [majorant, ContinuousLinearEquiv.unitsEquivAut_apply]

theorem majorant_nonneg (b : ℝ) (hb : 0 < b) (x : ℝ) : 0 ≤ (majorant b hb x).re := by
  rw [majorant_apply]; exact radialMajorant_nonneg _

theorem majorant_one (b : ℝ) (hb : 0 < b) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ b) :
    majorant b hb x = 1 := by
  rw [majorant_apply]
  apply radialMajorant_one
  refine ⟨mul_nonneg hx0 (inv_nonneg.mpr hb.le), ?_⟩
  rw [← div_eq_mul_inv]; exact (div_le_one hb).mpr hx

/-- The support scale of the majorant. -/
def majorantScale : ℝ := Classical.choose radialMajorant_support_bound

theorem majorantScale_pos : 0 < majorantScale :=
  (Classical.choose_spec radialMajorant_support_bound).1

theorem majorant_support (b : ℝ) (hb : 0 < b) :
    Function.support (majorant b hb : ℝ → ℂ) ⊆ Iic (majorantScale*b) := by
  intro x hx
  have hx' : radialMajorant (x*b⁻¹) ≠ 0 := by
    rw [← majorant_apply b hb x]; exact hx
  have h := (Classical.choose_spec radialMajorant_support_bound).2 hx'
  change x*b⁻¹ ≤ majorantScale at h
  rw [← div_eq_mul_inv, div_le_iff₀ hb] at h
  simpa [Set.mem_Iic, mul_comm] using h

/-- The finite initial-weight sum of the lane is below `radialControl Φ` times the radial energy
with the fixed majorant at the same scale, kept on `initialKeep η Q₀`. -/
theorem finite_le_majorant (F : O → ℂ) (η η₀ : Character) (Q Q₀ : Id)
    (hQ : internalQ Q η₀ = Q₀) (Φ : 𝓢(ℝ,ℂ)) (bΦ : ℝ) (hb : 0 < bΦ)
    (hs : Function.support (Φ:ℝ → ℂ) ⊆ Iic bΦ)
    (Z : ℝ) (hZ : 0 < Z) (rows : Finset O) :
    (∑ z ∈ rows, initialWeight η η₀ Q Φ Z z*‖F z‖^2) ≤
      radialControl Φ*radialEnergy F (initialKeep η Q₀) (majorant bΦ hb) Z := by
  let g := fun z : O => if initialKeep η Q₀ z then
    ‖F z‖^2*((majorant bΦ hb) (‖ConcreteTraceCRT.eisEmbedding z‖^2/Z)).re else 0
  have hg : ∀ z, 0 ≤ g z := by
    intro z; dsimp only [g]; split_ifs
    · exact mul_nonneg (sq_nonneg _) (majorant_nonneg _ _ _)
    · exact le_rfl
  have hsum : Summable g :=
    CenteredMomentEnergyCapacityRemoval.compact_radial_summable F (initialKeep η Q₀)
      (majorant bΦ hb) Z (majorantScale*bΦ) hZ (majorant_support bΦ hb)
  have hterm : ∀ z ∈ rows, initialWeight η η₀ Q Φ Z z*‖F z‖^2 ≤ radialControl Φ*g z := by
    intro z _
    unfold initialWeight
    rw [hQ]
    dsimp only [g]
    by_cases hk : initialKeep η Q₀ z
    · simp only [hk, ite_true]
      set x := ‖ConcreteTraceCRT.eisEmbedding z‖^2/Z
      have hx0 : 0 ≤ x := div_nonneg (sq_nonneg _) hZ.le
      by_cases hz : Φ x = 0
      · rw [hz, Complex.zero_re, zero_mul]
        exact mul_nonneg (radial_control_nonneg Φ) (mul_nonneg (sq_nonneg _) (majorant_nonneg _ _ _))
      · have hxb : x ≤ bΦ := hs hz
        rw [majorant_one bΦ hb x hx0 hxb, Complex.one_re, mul_one]
        have := real_profile_le Φ x
        nlinarith [sq_nonneg ‖F z‖]
    · simp only [hk, ite_false, zero_mul, mul_zero, le_refl]
  calc (∑ z ∈ rows, initialWeight η η₀ Q Φ Z z*‖F z‖^2)
      ≤ ∑ z ∈ rows, radialControl Φ*g z := Finset.sum_le_sum hterm
    _ = radialControl Φ*∑ z ∈ rows, g z := by rw [Finset.mul_sum]
    _ ≤ radialControl Φ*∑' z, g z :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum rows (fun z _ => hg z))
          (radial_control_nonneg Φ)
    _ = radialControl Φ*radialEnergy F (initialKeep η Q₀) (majorant bΦ hb) Z := rfl

end
end Qrh.MarkedAnchor.Ordinary.Reference
