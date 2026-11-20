/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform actual height event, deterministic remaining-width admission and
canonical original packet on the genuine common rows. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassFinite
import Candidate.C092.transport.MixedUpperFinalRouting
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MixedUpperFinal QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Uniform in every permitted later physical height exponent and dyad. -/
theorem class_native_height_event (n : ℕ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀d tau : ℝ,∀i : ℕ,
      (1/100:ℝ) ≤ d → d ≤ 7/8 → 0 ≤ tau → tau ≤ 1/400 → i ≤ n →
      1+PacketJoin.nativeHeight Z d tau i ≤ Z^d := by
  let C : ℝ := (2*Real.pi+2)*(3+(3*n+1:ℕ))
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/400)).eventually (eventually_ge_atTop C),
    eventually_gt_atTop (1:ℝ)] with Z hC hZ
  refine ⟨hZ,?_⟩
  intro d tau i hd hdhi ht htmax hi
  have hbase : 1 ≤ Z^(1/400:ℝ) := Real.one_le_rpow hZ.le (by norm_num)
  have hp : Z^tau ≤ Z^(1/400:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le htmax
  have hi' : (3*i+1:ℝ) ≤ (3*n+1:ℝ) := by exact_mod_cast (show 3*i+1 ≤ 3*n+1 by omega)
  calc
    _ ≤ (2*Real.pi+2)*(3+(3*i+1:ℕ)*Z^tau) := PacketJoin.nativeHeight_le Z d tau i hZ.le hdhi ht
    _ ≤ C*Z^(1/400:ℝ) := by
      have hm:=mul_le_mul hi' hp (Real.rpow_nonneg (by linarith) _) (by positivity : 0 ≤ (3*n+1:ℝ))
      have hinner : 3+(3*i+1:ℕ)*Z^tau ≤ (3+(3*n+1:ℕ))*Z^(1/400:ℝ) := by
        push_cast
        nlinarith only [hm,hbase]
      have he:=mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2*Real.pi+2)
      convert he using 1 <;> dsimp [C] <;> ring
    _ ≤ Z^(3/400:ℝ)*Z^(1/400:ℝ) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = Z^(1/100:ℝ) := by rw [←Real.rpow_add (by linarith : 0<Z)];congr 1;norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hd

/-- Canonical genuine reflected packet. Principal rows are outside every
actual selected common class and are zero-extended only for finite notation. -/
def classCanonicalSmall (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ)
    (Y U : ℝ) (r : TopData.Row) (u : FreeRow) : ℂ :=
  if hn : (rowCharacter F.S F.exclusions.prime u).residue≠1 then
    paidOriginalSmall D F J η Z x z Y U r u
      (Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u hn)) else 0

def classSmallNorm (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ)
    (Y U : ℝ) (r : TopData.Row) (common : Finset FreeRow) : ℝ :=
  mainFront D J Z*∑u∈common,‖classCanonicalSmall D F J η Z x z Y U r u*mainProduct D F J u Z z‖

/-- The selected adapter's canonical data gives the SAME original packet
on the SAME true common rows. There is no varying-profile estimate. -/
theorem class_common_exact (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (η : Character) (Z : ℝ) (h decrement epsilon xi ann loss massEps cap : ℝ)
    (common nativeRows : Finset FreeRow) (d a height : ℝ) (x z : ℂ) (r : TopData.Row) (outerFee : ℝ)
    (R : PaidActualResult D F J η Z h decrement epsilon xi ann loss massEps cap common nativeRows d a height x z r outerFee) :
    classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) r common=
      mainFront D J Z*(∑u∈commonIndices R.input.bank.currentSlice.fiber.rows R.input.bank.common,
        ‖paidOriginalSmall D F J η Z R.input.x R.input.z (Z^Geometry.y) R.input.bank.baseScale R.input.r u.val
          (R.input.data u)*mainProduct D F J u.val Z R.input.z‖) := by
  unfold classSmallNorm
  conv_lhs => rw [←R.common_eq,←common_sum R.input.bank.currentSlice.fiber.rows R.input.bank.common R.input.bank.common_current]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  simp only [classCanonicalSmall,dif_pos (R.input.nonprincipal u.val u.property),R.data_eq,
    R.x_eq,R.z_eq,R.r_eq,MiddleBank.baseScale,R.d_eq]

#print axioms class_native_height_event
#print axioms class_common_exact
end
end QRH.Cycle092.MixedMiddleReturn
