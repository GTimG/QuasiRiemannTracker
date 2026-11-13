/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B024
import Candidate.Bundles.B031
import Candidate.Bundles.B041
import Candidate.Bundles.B044
import Candidate.Bundles.B045
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

/- BEGIN ORIGINAL Cycle61.Numerator.FiniteError.FullW; sha256 6355415570007d25355ffafbc469a55ba0d6dfb440a692147265bf6931d4b379 -/
section
/- Adapted from weighted upstream PR6; original notices and transparent FullWContour definitions retained. -/
                                               
                                                  
                                                            

/-! Summable physical row/tuple errors for the full-w transport at the new
lengths, with arbitrary power savings chosen after the height exponent. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle61.Transport.FullWError
open Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma fullW_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^Cycle61.Arithmetic.x)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^Cycle61.Arithmetic.y)^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [Cycle61.Transport.length_sum,Cycle61.Transport.ly_coarse,Cycle61.Transport.ell_interval])

lemma fullW_prime_product_bound {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=Cycle61.Arithmetic.ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^Cycle61.Arithmetic.ell := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma fullW_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/10000000000)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(Cycle61.Arithmetic.h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=Cycle61.Arithmetic.ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Cycle61.Arithmetic.ell) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Cycle61.Arithmetic.h+ζ≤1 by linarith [Cycle61.Transport.h_interval]))
  have hp := fullW_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^Cycle61.Arithmetic.ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(Cycle61.Arithmetic.ell*(3:ℕ))=Z^(6+3*Cycle61.Arithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


lemma fullW_prime_tuple_count {K : ℕ} (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=Cycle61.Arithmetic.ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^Cycle61.Arithmetic.ell := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


theorem original_row_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/10000000000)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(Cycle61.Arithmetic.h+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=Cycle61.Arithmetic.ell →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z a e H (1/2)‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*Cycle61.Arithmetic.ell)+saving)/τ)
  have hN' : (8+3*Cycle61.Arithmetic.ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := fullW_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := fullW_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*Cycle61.Arithmetic.ell)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Cycle61.Arithmetic.ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Cycle61.Arithmetic.ell)/height H^N) := by
      have hh : Z^(6+3*Cycle61.Arithmetic.ell)*Z^(2:ℝ)=Z^(8+3*Cycle61.Arithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Cycle61.Arithmetic.ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


theorem finite_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/10000000000) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^(Cycle61.Arithmetic.h+ζ)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=Cycle61.Arithmetic.ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z-
        finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_fullW_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(Cycle61.Arithmetic.h+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Cycle61.Arithmetic.h+ζ≤1 by linarith [Cycle61.Transport.h_interval])
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (fullW_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Cycle61.Arithmetic.ell≤1 by linarith [Cycle61.Transport.ell_interval])) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z u-
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z (a u) e (H u) (1/2)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralFullWRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z (a u) e (H u) (1/2)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]


end Cycle61.Transport.FullWError
end

#print axioms Cycle61.Transport.FullWError.original_row_fullW_arbitrary_saving
#print axioms Cycle61.Transport.FullWError.finite_fullW_arbitrary_saving

end
/- END ORIGINAL Cycle61.Numerator.FiniteError.FullW -/

/- BEGIN ORIGINAL Cycle61.Numerator.FiniteError.CubeTransfer; sha256 4d112ecb891cbfd68db5493a970395c0e7689836ddc2900ec08671f346dad1f1 -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/
                                                 
                                          
namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]


private lemma transfer_triangle (A P B : ℂ) : ‖A-B‖ ≤ ‖P-A‖+‖P-B‖ := by
  calc
    _ = ‖-(P-A)+(P-B)‖ := by congr 1; ring
    _ ≤ ‖-(P-A)‖+‖P-B‖ := norm_add_le _ _
    _ = _ := by rw [norm_neg]

theorem finite_cube_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0 < b) (hζ : ζ≤1/10000000000) (hA : 0≤A)
    (e : ℝ) (he : 0 < e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((Cycle61.Arithmetic.h:ℝ)+ζ)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(Cycle61.Arithmetic.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2 < B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u) < a u+2*e) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e a H-
        Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨Cc,hCc,hcube⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ A hτ hb hζ hA
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cw,hCw,hfull⟩ := Cycle61.Transport.FullWError.finite_fullW_arbitrary_saving (ι:=ι)
    K τ saving b ζ A hτ hb hζ hA e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cc+Cw,add_nonneg hCc hCw,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hc := hcube η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hw := hfull η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have ht := transfer_triangle (finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
      (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e a H)
    (finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z)
    (Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
      (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e a H)
  exact ht.trans ((add_le_add hc hw).trans_eq (by ring))

end SevenEighths.Cycle61HighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.Cycle61HighRowFamily.finite_cube_fullW_arbitrary_saving

end
/- END ORIGINAL Cycle61.Numerator.FiniteError.CubeTransfer -/

/- BEGIN ORIGINAL Cycle61.Numerator.FiniteError.Normalized; sha256 60baa26cc9e42b7b9c4bd2121d2571a7fb0f8a07df7e9c8a981f5faf919598de -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/
                                                 
                                                  
                                      
                                                           

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transferPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_cube_fullW_arbitrary_saving
    (K : ℕ) (τ saving a b B ζ nu : ℝ)
    (hτ : 0 < τ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hζ : ζ ≤ 1/10000000000) (hnu : 0 < nu)
    (e : ℝ) (he : 0 < e) (he' : e < 1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,0 < ell j) (hellinj : Function.Injective ell)
    (hellsum : ∑j,ell j=Cycle61.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b)
    (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0 ≤ (W0 y).re) (hp1 : ∀y,0 ≤ (W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^((Cycle61.Arithmetic.h:ℝ)+ζ)) →
      ∀(alpha base height : FreeRow→ℝ) (idx : FreeRow→ℕ),
      (∀u∈R,(51/100:ℝ) ≤ alpha u ∧ alpha u ≤ 1 ∧ 2 < base u ∧
        Z^τ ≤ height u ∧ height u ≤ (3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(idx u+1:ℕ)*base u) < alpha u+2*e) →
      let Y : Fin K→ℝ := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Y j)
      let hT := transferPoolOutside M H S K a b Y
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Cycle61.Arithmetic.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧
      ‖finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e alpha height/normer-
        Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z e alpha height/normer‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ct,hCt,htransfer⟩ := finite_cube_fullW_arbitrary_saving
    (ι:=RayQuotient.Characters M H) K τ (saving+nu) b ζ B hτ (ha.trans_le hab) hζ hB
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Cycle61LowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    hell hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Ct*Cn,mul_nonneg hCt hCn.le,?_⟩
  filter_upwards [hnormalizer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_ge_atTop (1:ℝ)] with Z hnorm hdis hZ
  intro η R hR alpha base height idx hbin
  dsimp only at hnorm ⊢
  refine ⟨hnorm.1,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Y : Fin K→ℝ := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Y j)
  let hT := transferPoolOutside M H S K a b Y
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) :
      (P.val.absNorm:ℝ) ≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ0 (ell j)) P hP).2
    simpa only [mul_comm] using hh
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hb := htransfer η Z hZ R hR T hT hdis ell hellsum hpool WC hWCB
    alpha base height idx (rayCubeFamily M H hH) hbin
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hb hnorm.2 (norm_nonneg _) (by positivity)).trans_eq
  have hp : Z^(-(saving+nu))*Z^nu=Z^(-saving) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  calc
    _ = (Ct*Cn*(η.modulus.absNorm:ℝ)^2)*(Z^(-(saving+nu))*Z^nu) := by ring
    _ = _ := by rw [hp]

end SevenEighths.Cycle61HighRowFamily
end
end OAI

#print axioms OAI.SevenEighths.Cycle61HighRowFamily.actual_normalized_cube_fullW_arbitrary_saving

end
/- END ORIGINAL Cycle61.Numerator.FiniteError.Normalized -/

/- BEGIN ORIGINAL Cycle61.Numerator.Finite.Transfer; sha256 6cb4b5b62bdfba22cea70021dc9a58595bf76b3d85db029040277be7949a2126 -/
section
                                         
                                               

set_option autoImplicit false
namespace Cycle61.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle61DetectorCount FinalAssembly Cycle61HighTransport

/-- The proved original-row error applies to the literal new-geometry numerator. -/
theorem actual_selected_error (A : ChosenData) (τ : ℝ) (hτ : 0<τ) :
    ∃C : ℝ,0≤C ∧ ∀ᶠZ : ℝ in atTop,∀n : ℕ,∀η : Character,∀idx grid : FreeRow→ℕ,
      ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
        η rowPadding A.D.e τ n Z idx grid →
      normalizer A.D A.F Z≠0 ∧
      ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
        1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid/normalizer A.D A.F Z-
        fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
          (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normalizer A.D A.F Z‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ)) := by
  obtain ⟨C,hC,herror⟩:=Cycle61HighRowFamily.actual_normalized_cube_fullW_arbitrary_saving
    A.F.modulus ⊤ le_top A.D.N τ 1 1 2 1 rowPadding (A.D.t/8)
    hτ (by norm_num) (by norm_num) (by norm_num) (by norm_num [rowPadding])
    (by have ht:=A.D.t_pos;positivity) A.D.e A.D.e_pos A.D.e_small
    A.F.S A.F.exclusions A.F.maximal A.F.first A.D.length A.D.slots_pos A.D.slots_injective A.D.slots_sum
    (fun _=>A.F.w) (fun _=>A.F.smooth) (fun _=>A.F.compact) (fun _=>A.F.support)
    (fun _=>A.F.bounded) (fun _=>A.F.nonzero) A.F.W A.F.W 1 2 1 2 (by norm_num) (by norm_num)
    A.F.complex_support A.F.complex_support A.F.real A.F.real A.F.nonnegative A.F.nonnegative
    A.F.complex_nonzero A.F.complex_nonzero
  refine ⟨C,hC,?_⟩
  filter_upwards [herror,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_ge_atTop (1:ℝ)] with Z he hT hZ
  intro n η idx grid hsel
  have hrows:=selected_rows_facts A.D A.F Z grid
  have hbin : ∀u∈selectedRows A.D A.F Z grid,
      (51/100:ℝ)≤51/100+A.D.e*grid u ∧ 51/100+A.D.e*grid u≤1 ∧ 2<Z^τ ∧
      Z^τ≤(3*idx u+1:ℕ)*Z^τ ∧ (3*idx u+1:ℕ)*Z^τ≤(3*idx u+2:ℕ)*Z^τ ∧
      detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
        (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+A.D.e*grid u+2*A.D.e := by
    intro u hu
    refine ⟨(hsel.2.1 u).1,(hsel.2.1 u).2.1.trans (by norm_num),hT,?_,?_,(hsel.2.1 u).2.2.2.2.1⟩
    · have hm : (1:ℝ)≤(3*idx u+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx u+1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
    · have hm : ((3*idx u+1:ℕ):ℝ)≤(3*idx u+2:ℕ) := by
        exact_mod_cast (by omega : 3*idx u+1≤3*idx u+2)
      exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by linarith) τ)
  have hb:=he η (selectedRows A.D A.F Z grid)
    (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩)
    (fun u=>51/100+A.D.e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx hbin
  convert hb using 1 <;> rfl
end
end Cycle61.FiniteNumerator

end
/- END ORIGINAL Cycle61.Numerator.Finite.Transfer -/
