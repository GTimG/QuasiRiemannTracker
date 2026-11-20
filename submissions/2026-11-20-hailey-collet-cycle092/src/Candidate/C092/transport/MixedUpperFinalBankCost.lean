/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pay the complete 65,537-response dyad multiplicity from an explicit reserve. -/
import Candidate.C092.transport.MixedUpperFinalPartition
import Candidate.C092.transport.PacketJoinPrefactor
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeDetectorWitnessRows
open QRH.Record1252270103Return QRH.Cycle092.MixedOffsetBank
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The exponent reserve is fixed before the live source scale and dyad.
The number of responses affects the constant, not the original row count. -/
theorem response_dyads_absorbed (copies : ℕ) (hc : 0<copies) (loss : ℝ) (hl : 0<loss) :
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠZ : ℝ in atTop,1 ≤ Z ∧
      ∀d : ℝ,(1/2:ℝ) ≤ d →
        (dyadicLength (Z^d):ℝ)^(2*copies) ≤ C*(Z^d)^loss := by
  have hn : 0<(copies:ℝ):=by exact_mod_cast hc
  obtain ⟨L,hL,h⟩:=QRH.Cycle092.PacketJoin.dyadic_cost_uniform
    (loss/(copies:ℝ)) (div_pos hl hn)
  refine ⟨L^copies,pow_nonneg hL _,?_⟩
  filter_upwards [h] with Z h
  refine ⟨h.1,?_⟩
  intro d hd
  have hp:=pow_le_pow_left₀ (by positivity : 0 ≤ (dyadicLength (Z^d):ℝ)^2) (h.2 d hd) copies
  have hUp : 0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans_le h.1) _
  have he : ((Z^d)^(loss/(copies:ℝ)))^copies=(Z^d)^loss := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le,div_mul_cancel₀ _ hn.ne']
  simpa only [pow_mul,mul_pow,he] using hp

/-- ALL dyads of ALL Q.2 offsets are paid once. The label alphabet is fixed
by the actual source modulus and remains an ordinary constant. -/
theorem descriptor_cost_absorbed (Label : Type*) [Fintype Label]
    (loss : ℝ) (hl : 0<loss) :
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠZ : ℝ in atTop,1 ≤ Z ∧
      ∀d : ℝ,(1/2:ℝ) ≤ d →
        (Fintype.card (Descriptor Label (dyadicLength (Z^d))):ℝ) ≤ C*(Z^d)^loss := by
  obtain ⟨L,hL,h⟩:=response_dyads_absorbed 65537 (by omega) loss hl
  refine ⟨(Fintype.card Label:ℝ)*L,mul_nonneg (Nat.cast_nonneg _) hL,?_⟩
  filter_upwards [h] with Z h
  refine ⟨h.1,?_⟩
  intro d hd
  rw [descriptor_count]
  push_cast
  calc
    _ = (Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^(2*65537) := by
      rw [mul_assoc,←pow_add]
    _ ≤ (Fintype.card Label:ℝ)*(L*(Z^d)^loss) :=
      mul_le_mul_of_nonneg_left (h.2 d hd) (Nat.cast_nonneg _)
    _ = _ := by ring

#print axioms response_dyads_absorbed
#print axioms descriptor_cost_absorbed
end
end QRH.Cycle092.MixedUpperFinal
