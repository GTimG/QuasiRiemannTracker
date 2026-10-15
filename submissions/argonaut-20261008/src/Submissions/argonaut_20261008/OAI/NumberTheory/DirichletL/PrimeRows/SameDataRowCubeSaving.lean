import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeErrorSaving
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.SameDataCanonicalFiniteCosts

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeMellinBoundary CompletedGauss
open HeckeInverseAmplification hiding PrimeIdeal
open SevenEighths.Parameters SevenEighths.PerturbedCentral
open SevenEighths.PerturbedCanonicalLocalPrep
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem original_row_cube_arbitrary_saving_same_D {Delta : ℝ} (D : HighDataPerturbed Delta) (τ saving b : ℝ)
    (hτ : 0<τ) (hb : 0<b)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin D.N→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(physicalHeight+D.t) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(D.ell j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^sourceLx) (Z^sourceLy) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^sourceLx) (Z^sourceLy) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN'⟩ := exists_canonical_decay_order τ saving hτ
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) D.N e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^D.N)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^sourceLx) (Z^sourceLy) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := same_D_canonical_contour_cost D η u P Z b hZ hb.le huZ hp
  have hscale := shifted_canonical_crude_source_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2+3*rho0)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by
      have hm : (17/2:ℝ)+3*rho0<9 := by norm_num [rho0]
      linarith only [hm, hN'])
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^D.N)^3*Z^(13/2+3*rho0))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^D.N)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2+3*rho0)/height H^N) := by
      have hh : Z^(13/2+3*rho0)*Z^(2:ℝ)=Z^(17/2+3*rho0) := by rw [←Real.rpow_add hZ0]; congr 1; ring
      rw [←hh]
      ring
    _ ≤ (C*(b^D.N)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2+3*rho0)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end SevenEighths.ProbeHighRowFamily
end
end OAI
