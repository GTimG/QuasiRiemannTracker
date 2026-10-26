import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.GeometryMarkedPacket
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.RetainedSlotCaps
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.LabeledRawMax
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.WholeFixedBad
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryZeroPartition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle63Moment Cycle63InitialMass
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A common polynomial height for all selected buffered rows. -/
def geometryRawHeight (Z τ : ℝ) (I : ℕ) : ℝ :=
  (2*Real.pi+6*(I+1:ℕ))*Z^τ

lemma geometry_raw_height_nonneg {Z τ : ℝ} (hZ : 0 ≤ Z) (I : ℕ) :
    0 ≤ geometryRawHeight Z τ I := by
  unfold geometryRawHeight
  positivity

lemma geometry_raw_height_zero {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ)
    (i I : ℕ) (hi : i ≤ I) :
    2*Real.pi*Z^(τ/2)+(3*i:ℕ)*Z^τ ≤ geometryRawHeight Z τ I := by
  have hr := Real.rpow_le_rpow_of_exponent_le hZ (show τ/2 ≤ τ by linarith)
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.pi by positivity)
  unfold geometryRawHeight
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz]

lemma geometry_raw_height_time {Z τ t : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |t| ≤ geometryRawHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  unfold geometryRawHeight
  push_cast at ht ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

lemma geometry_raw_height_frequency {Z τ t v : ℝ} (hZ : 0 ≤ Z)
    (i I : ℕ) (hi : i ≤ I)
    (ht : |t|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ)
    (hv : |t+v|+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ) : |v| ≤ geometryRawHeight Z τ I := by
  have hz := Real.rpow_nonneg hZ τ
  have hic : (i:ℝ) ≤ I := by exact_mod_cast hi
  have habs : |v| ≤ |t+v|+|t| := by
    calc
      |v| = |t+v+-t| := congrArg abs (by ring)
      _ ≤ |t+v|+|t| := by simpa only [abs_neg] using abs_add_le (t+v) (-t)
  unfold geometryRawHeight
  push_cast at ht hv ⊢
  nlinarith [mul_nonneg (show 0 ≤ (I:ℝ)-i by linarith) hz,
    mul_nonneg Real.pi_pos.le hz]

/-- The fixed buffered index contributes exactly Jτ to the scale exponent. -/
lemma geometry_raw_height_power {Z τ : ℝ} (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (I J : ℕ) :
    (1+geometryRawHeight Z τ I)^J ≤
      (1+2*Real.pi+6*(I+1:ℕ))^J*Z^(τ*(J:ℝ)) := by
  have hz := Real.one_le_rpow hZ hτ
  have hp : 0 < Z := zero_lt_one.trans_le hZ
  have h : 1+geometryRawHeight Z τ I ≤ (1+2*Real.pi+6*(I+1:ℕ))*Z^τ := by
    unfold geometryRawHeight
    nlinarith
  calc
    _ ≤ ((1+2*Real.pi+6*(I+1:ℕ))*Z^τ)^J :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (geometry_raw_height_nonneg (τ:=τ) hp.le I)) h J
    _ = _ := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
