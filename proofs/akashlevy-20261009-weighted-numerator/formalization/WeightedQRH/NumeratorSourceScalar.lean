import WeightedQRH.NumeratorFreeScalarBound
import WeightedQRH.NumeratorPhysicalFront

/-! The actual calibrated scalar and physical frequency at an enlarged moment
base. The .68t factor is retained explicitly when replacing the dyad's lower edge. -/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

theorem source_frequency_scalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ∀Z d t U : ℝ,0 < Z → U=Z^d →
      Z^(d-2*t) ≤ rowNorm u → rowNorm u ≤ U →
      ‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*U^(2*eps)*
          U^(-(17/50:ℝ))*Z^((17/25)*t) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_arithmetic_bound e eps he he' heps S hS hmax
  refine ⟨C,hC,?_⟩
  intro η u ι _ ψ B a H i hB ha hatop hH hnext x z hx hz hxim Z d t U hZ hU hlo hhi
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hxim
  have hU0 : 0 < U := by rw [hU];exact Real.rpow_pos_of_pos hZ _
  have hNu0 : 0 < rowNorm u := (Real.rpow_pos_of_pos hZ _).trans_le hlo
  have hs := hbound η u ψ B a H i hB ha hatop hH hnext x z hx hz hxim
  have hs' : ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*U^(2*eps)*(3+H)^(2*eps) := by
    apply hs.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNu0.le hhi (by positivity)) (by positivity)) (by positivity)
  have hf : ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤
      U^(-(17/50:ℝ))*Z^((17/25)*t) := by
    apply (frequencyWeight_dyad_bound u z (Z^(d-2*t)) (17/50)
      (Real.rpow_pos_of_pos hZ _) (by norm_num) hz hlo).trans_eq
    rw [hU,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  rw [norm_mul]
  apply (mul_le_mul hf hs' (norm_nonneg _) (by positivity)).trans_eq
  ring

end WeightedQRH.Numerator
end
