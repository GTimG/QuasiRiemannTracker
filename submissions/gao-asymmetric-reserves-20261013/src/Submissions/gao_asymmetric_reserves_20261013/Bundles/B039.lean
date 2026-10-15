/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B014
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B030
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.SmallTail

/- BEGIN ORIGINAL MODULE Global.Transport.FullWFiniteError ; sha256 2cd5bb7359d764b00244c472f94d42c82c19d72f0d2444e18b31cdf3b65303f8 -/
section
/- Adapted from weighted upstream PR6; original notices and transparent FullWContour definitions retained. -/





/-! Summable physical row/tuple errors for the full-w transport at the new
lengths, with arbitrary power savings chosen after the height exponent. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Submission20261012.Global.Transport.FullWError
open Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma fullW_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^Submission20261012.Global.lx)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^Submission20261012.Global.ly)^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [Submission20261012.Global.length_sum,Submission20261012.Global.ly_coarse,Submission20261012.Global.ell_interval])

lemma fullW_prime_product_bound {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=Submission20261012.Global.ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^Submission20261012.Global.ell := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma fullW_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(Submission20261012.Global.h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=Submission20261012.Global.ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Submission20261012.Global.ell) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Submission20261012.Global.h+ζ≤1 by linarith [Submission20261012.Global.h_interval]))
  have hp := fullW_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^Submission20261012.Global.ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(Submission20261012.Global.ell*(3:ℕ))=Z^(6+3*Submission20261012.Global.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


lemma fullW_prime_tuple_count {K : ℕ} (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=Submission20261012.Global.ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^Submission20261012.Global.ell := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=> Nat.cast_nonneg _) (fun j _=> hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


theorem original_row_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(Submission20261012.Global.h+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=Submission20261012.Global.ell →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z u-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z a e H (1/2)‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*Submission20261012.Global.ell)+saving)/τ)
  have hN' : (8+3*Submission20261012.Global.ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := fullW_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := fullW_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*Submission20261012.Global.ell)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Submission20261012.Global.ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Submission20261012.Global.ell)/height H^N) := by
      have hh : Z^(6+3*Submission20261012.Global.ell)*Z^(2:ℝ)=Z^(8+3*Submission20261012.Global.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*Submission20261012.Global.ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


theorem finite_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(Submission20261012.Global.h+ζ)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=Submission20261012.Global.ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z-
        finiteCentralFullWRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_fullW_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(Submission20261012.Global.h+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Submission20261012.Global.h+ζ≤1 by linarith [Submission20261012.Global.h_interval])
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (fullW_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show Submission20261012.Global.ell≤1 by linarith [Submission20261012.Global.ell_interval])) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z u-
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z (a u) e (H u) (1/2)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=> hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=> hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) (fun j _=> hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralFullWRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=> CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z (a u) e (H u) (1/2)‖ := norm_sum_le _ _
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


end Submission20261012.Global.Transport.FullWError
end
end
/- END ORIGINAL MODULE Global.Transport.FullWFiniteError -/

/- BEGIN ORIGINAL MODULE Global.Transport.LargeDyad ; sha256 165877c4c39ee47cfbf43620e1782b18b1e2f8b98aee61d4cc93cb56189ef9e5 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z U : ℝ),1≤ Z → 1≤ U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z 2 2 r
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+(Submission20261012.Global.h:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=> Z^(length i)) hYp W hWS hWB
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(Submission20261012.Global.lx:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(Submission20261012.Global.ly:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [large_source_scale Z hZ0 length hl r];ring

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.LargeDyad -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderRayThresholds ; sha256 5a443e51ab9e718e91eb1ccf885f4297b5120b4f8421589701cacc7188c27b5d -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/



noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Submission20261012.Global.Transport.PrincipalRaySlots
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
open OAI.SevenEighths.ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0< c) (hd : c ≤ d) (hmin : 0< ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin ≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1 ≤ Z ∧ 480 ≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(theta :ℝ)) ≤ 1 ∧
      (∀j,480 ≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)< c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin ≤ (P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(theta :ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]) : (0:ℝ)< theta )).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0< Z := by linarith [Submission20261012.Global.Transport.theta_bounds]
  have hmono (j : ι) : c*Z^ellMin ≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0< c) (hd : c ≤ d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0 ≤ W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0< ell j) (eps : ℝ) (heps : 0< eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0< slotMass T (residueWeights W (fun j=> Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=> Z^(ell j)))))⁻¹| ≤ Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0< slotMass
      (fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=> Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=> c) (fun _=> d) ell (fun _ _=> hc) (fun _ _=> hd) (fun j _=> hsupp j)
    (fun j _=> hW j) (fun j _=> hcompact j) (fun j _=> hp j) (fun j _=> hW0 j) (fun j _=> hne j)
    (fun j _=> hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end Submission20261012.Global.Transport.PrincipalRaySlots
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderRayThresholds -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderRegion ; sha256 58592f8f3711f9ff6739400fad556ea369578c7b8f311de7f6577c346eab4c50 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




/-!
Extension of the original OpenAI local Euler estimates to the narrower
w,z region and the improved x boundary. Proof structure follows
Detector/GlobalRegion.lean, GlobalHolomorphic.lean and GlobalCorrection.lean.
The local factors and the global infinite product are the original objects.
-/

noncomputable section
namespace Submission20261012.Global.Transport
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler OAI.SevenEighths.ProbePhysical

theorem remainder_unramified_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : theta ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(219/100:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-theta) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(77/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds])))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

lemma remainder_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : theta≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem remainder_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|theta< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := remainder_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem remainder_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : theta≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := remainder_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem remainder_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : theta≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := remainder_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


local notation "Id" => Ideal ActualEisensteinCubic.O

lemma remainder_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply remainder_unramified_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem remainder_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> remainder_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma remainder_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : theta≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    remainder_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem remainder_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|theta< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply remainder_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact remainder_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem remainder_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : theta≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply remainder_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact remainder_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem remainder_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : theta≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply remainder_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact remainder_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end Submission20261012.Global.Transport
end
end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderRegion -/

/- BEGIN ORIGINAL MODULE Global.Transport.SignalShift ; sha256 2055d047803cb745f0afb6282ef19afbfe8d414776268af506fc2e082ca76016 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




/-! Original Hecke signal contour shift with the improved analyticity boundary. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI OAI.SevenEighths
namespace Submission20261012.Global.Transport.SignalShift
open HeckeFamily HeckeSignal Continuation

theorem quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | theta < s.re}) {a : ℝ}
    (ha : theta< a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((Complex.isOpen_re_gt theta).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, theta< s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (n : ℕ) (ha : theta< a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3/2)*C)*(1+|s.im|^n) := by
  have hnorm : ‖H s‖ ≤ 3/2 := by
    have ht := norm_add_le (H s-1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith [hb s (ha.trans_le hs.1)]
  unfold quotient
  rw [norm_mul]
  calc
    _ ≤ (3/2)*(C*(1+|s.im|^n)) :=
      mul_le_mul hnorm (hR s hs.1 hs.2) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | theta< s.re})
    (hb : ∀ s : ℂ, theta< s.re → ‖H s-1‖ ≤ 1/2)
    (c a C : ℝ) (n : ℕ) (ha : theta< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^n))
    {x : ℝ} (hx : 1 ≤ x) :
    HeckeSignal.signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ n ha2
    (gaussianContourIntegrand_differentiableOn (quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)*((3/2)*C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x^(b+c) ≤ x^(2+c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b-5/6)^2) ≤ Real.exp ((2-5/6 : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hb'.1,hb'.2]
  have hq := quotient_polynomial_bound χ H hb n ha hC hR
    (s := (b : ℂ)+y*I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x^(2+c)*Real.exp ((2-5/6 : ℝ)^2)) *
        (((3/2)*C)*(1+|y|^n))*Real.exp (-(y^2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring


 theorem contour_shift_left_bound (χ : HeckeFamily.Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | theta < s.re})
    (hb : ∀ s : ℂ, theta < s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : theta < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) {x : ℝ} (hx : 1 ≤ x) :
    HeckeSignal.signal χ H c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

end Submission20261012.Global.Transport.SignalShift
end
end
/- END ORIGINAL MODULE Global.Transport.SignalShift -/

/- BEGIN ORIGINAL MODULE Global.Transport.SmallTail ; sha256 41b0212ce643c1b3769a77ab8fd0bde1b99b9a71de158749bf5597f251807d98 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤ Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50))
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    ((7/8:ℝ)+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) (by linarith) le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e)
  have hA : 0≤ A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50)
      ≤ A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=> Z^(length i)) hYp
      W hWS hWB (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := small_source_scale Z hZ0 length hl (7/8) e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e)*Z^((1/100:ℝ)*2)=
          Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6))+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.SmallTail -/
