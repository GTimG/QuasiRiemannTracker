import Candidate.Cycle62.Marked.GeometryMarkedPacket
import Candidate.Cycle62.Marked.RetainedSlotCaps
import Candidate.Cycle62.Marked.LabeledRawMax
import Candidate.Cycle62.Marked.WholeFixedBad
import Candidate.Cycle62.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment Cycle62Moment Cycle62InitialMass
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

/-- Literal buffered admission supplies both maximum gates used by marked
counting, together with its uniform finite index bound. -/
lemma geometry_zero_bin_raw_gates {Z Bmask bΦ e : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p) :
    p.1.val ≤ bufferCount e ∧
      51/100 ≤ bufferValue e p ∧ bufferValue e p ≤ 7/8 ∧
      bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)<bufferValue e p+2*e :=
  ⟨hbin.2.1,hbin.2.2.1,hbin.2.2.2.1,hbin.2.2.2.2.1,hbin.2.2.2.2.2.2.2.1⟩

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.geometry_raw_height_power
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.geometry_zero_bin_raw_gates
