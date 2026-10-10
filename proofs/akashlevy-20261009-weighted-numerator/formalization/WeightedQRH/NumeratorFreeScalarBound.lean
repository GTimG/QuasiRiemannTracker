import WeightedQRH.NumeratorTupleRestoration
import OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic

/-! The calibrated scalar left after the quotient-free numerator expansion.
It contains no correction packet and consequently incurs no correction norm cost. -/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

/-- The detector's actual next-bin bound controls the reciprocal uniformly in
all source exclusions; the remaining principal L-factor lies on Re s = 2.04. -/
theorem numeratorFreeRowScalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps) :
    ∃C : ℝ,0 < C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S)
      (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤ C*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0 ≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr,by positivity,?_⟩
  intro S hS hmax η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖ ≤ L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ) < 2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖ ≤ 1 := by
    rw [norm_star]
    exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold numeratorFreeRowScalar
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (1*(L+1))*(Cr*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps) :=
      mul_le_mul (mul_le_mul hcal hl (norm_nonneg _) (by norm_num)) hrec
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact arithmetic and height costs for the numerator-free scalar. In
particular the row norm exponent is 2 eps rather than the old 3 eps. -/
theorem numeratorFreeRowScalar_arithmetic_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_bound e eps he he' heps
  have hF : 0 < (fixedConductorConstant S:ℝ) := by
    exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hh : 0 ≤ H := (abs_nonneg _).trans hxi
  apply (hbound S hS hmax η u ψ B a H i hB ha ha1 hH hbin x z hx hz hxi).trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  apply (mul_le_mul_of_nonneg_left hc hC.le).trans_eq
  ring

end WeightedQRH.Numerator
end
