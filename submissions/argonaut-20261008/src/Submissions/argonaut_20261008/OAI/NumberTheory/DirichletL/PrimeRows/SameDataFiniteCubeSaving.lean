import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.PrimeRows.SameDataRowCubeSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError

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

theorem finite_cube_arbitrary_saving_same_D {Delta : ℝ} (D : HighDataPerturbed Delta) (τ saving b A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(physicalHeight+D.t)) →
      ∀(T : Fin D.N→Finset PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(D.ell j)) →
      ∀W : Fin D.N→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(D.ell j)) W0 W1 (Z^sourceLx) (Z^sourceLy) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(D.ell j)) W0 W1
          (Z^sourceLx) (Z^sourceLy) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving_same_D (ι:=ι) D τ (saving+2) b hτ hb e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^D.N*A^D.N*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(physicalHeight+D.t)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show physicalHeight+D.t≤1 by have hc := same_D_height_cap D; have ht := D.t_pos; linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^D.N*Z :=
    (same_D_canonical_prime_tuple_count D T Z b hZ0 hb.le hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (totalE_le_one)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^sourceLx) (Z^sourceLy) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^sourceLx) (Z^sourceLy) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(D.ell j))‖≤A^D.N := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin D.N,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(D.ell j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^sourceLx) (Z^sourceLy) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(D.ell j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^sourceLx) (Z^sourceLy) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^D.N*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^D.N*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^D.N*Z)*(A^D.N*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^D.N*A^D.N*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end SevenEighths.ProbeHighRowFamily
end
end OAI
