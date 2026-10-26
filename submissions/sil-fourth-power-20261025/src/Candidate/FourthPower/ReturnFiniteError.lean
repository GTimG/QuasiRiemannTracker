/- Copyright (c) 2026 Sil, Hailey Collet, Gao and OpenAI. Apache-2.0.
Exact actual cube-to-FullW finite error at our new geometry. The underlying
row error theorems are geometry-independent and reused. Only their coarse
polynomial cost and finite-sum specialization is adapted here, because the
old global Bounds package contains the false-for-us guard ell<.1677.
No new analytic estimate or desired numerator premise is introduced.

-/
import Candidate.FourthPower.ReturnFullNumerator
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.Imported.FullWFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.Transport.LowNormalizer

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnFiniteError
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
open ProbeRaySlots Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
local notation "O" => HeckeFamily.O
local instance : Geometry.Parameters := ReturnSourceInputs.parameters
variable {ι : Type*} [Fintype ι]

private theorem actual_row_cap {ζ : ℝ} (hζ : ζ≤1/10000000000) :
    QRH.Record1252270103Return.GenericArithmetic.h+ζ≤1 := by
  change 1+ell-x+ζ≤1
  norm_num [ell,x,h,theta] at *
  linarith

private theorem actual_ell_cap : QRH.Record1252270103Return.GenericArithmetic.ell≤1 := by
  change ell≤1
  norm_num [ell,theta]

lemma fullW_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^QRH.Record1252270103Return.GenericArithmetic.x)^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^QRH.Record1252270103Return.GenericArithmetic.y)^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  have hx : QRH.Record1252270103Return.GenericArithmetic.x≤1 := by
    change x≤1
    norm_num [x,ell,h,theta]
  have hy : 0≤QRH.Record1252270103Return.GenericArithmetic.y := by
    change 0≤y
    norm_num [y,ell,h,theta]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by
    nlinarith [mul_nonneg ha hy,mul_nonneg he hy])

lemma fullW_prime_product_bound {K : ℕ} (P : Fin K→HeckeInverseAmplification.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=QRH.Record1252270103Return.GenericArithmetic.ell) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^QRH.Record1252270103Return.GenericArithmetic.ell := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma fullW_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→HeckeInverseAmplification.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/10000000000)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(QRH.Record1252270103Return.GenericArithmetic.h+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=QRH.Record1252270103Return.GenericArithmetic.ell)
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*QRH.Record1252270103Return.GenericArithmetic.ell) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (actual_row_cap hζ))
  have hp := fullW_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^QRH.Record1252270103Return.GenericArithmetic.ell)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^(QRH.Record1252270103Return.GenericArithmetic.ell*(3:ℕ))=Z^(6+3*QRH.Record1252270103Return.GenericArithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


lemma fullW_prime_tuple_count {K : ℕ} (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=QRH.Record1252270103Return.GenericArithmetic.ell)
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^QRH.Record1252270103Return.GenericArithmetic.ell := by
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


theorem uniform_cube_fullW_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→HeckeInverseAmplification.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H (1/2)‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cc,hCc,hcube⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨Cw,hCw,hfull⟩ := uniform_original_row_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨Cc+Cw,add_nonneg hCc hCw,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hc := hcube η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hw := hfull η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u) _).trans
  rw [norm_sub_rev] at hc
  exact (add_le_add hc hw).trans_eq (by ring)

theorem row_cube_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0< τ) (hb : 0< b) (hζ : ζ≤1/10000000000)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→HeckeInverseAmplification.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(QRH.Record1252270103Return.GenericArithmetic.h+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=QRH.Record1252270103Return.GenericArithmetic.ell →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖centralCubeIntegral S hS hmax P hPS η u W0 W1
          (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z a e H-
        centralFullWIntegral S hS hmax P hPS η u W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z a e H (1/2)‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*QRH.Record1252270103Return.GenericArithmetic.ell)+saving)/τ)
  have hN' : (8+3*QRH.Record1252270103Return.GenericArithmetic.ell)+saving< τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_cube_fullW_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := fullW_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := fullW_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(8+3*QRH.Record1252270103Return.GenericArithmetic.ell)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*QRH.Record1252270103Return.GenericArithmetic.ell))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*QRH.Record1252270103Return.GenericArithmetic.ell)/height H^N) := by
      have hh : Z^(6+3*QRH.Record1252270103Return.GenericArithmetic.ell)*Z^(2:ℝ)=Z^(8+3*QRH.Record1252270103Return.GenericArithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(8+3*QRH.Record1252270103Return.GenericArithmetic.ell)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


theorem finite_cube_fullW_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0< τ) (hb : 0< b) (hζ : ζ≤1/10000000000) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^(QRH.Record1252270103Return.GenericArithmetic.h+ζ)) →
      ∀(T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=QRH.Record1252270103Return.GenericArithmetic.ell →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z e a H-
        finiteCentralFullWRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := row_cube_fullW_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^(QRH.Record1252270103Return.GenericArithmetic.h+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (actual_row_cap hζ)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (fullW_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ actual_ell_cap) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z (a u) e (H u)-
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z (a u) e (H u) (1/2)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finiteCentralCubeRows finiteCentralFullWRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z (a u) e (H u))-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralFullWIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^QRH.Record1252270103Return.GenericArithmetic.x) (Z^QRH.Record1252270103Return.GenericArithmetic.y) Z (a u) e (H u) (1/2)‖ := norm_sum_le _ _
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
    (hellsum : ∑j,ell j=QRH.Record1252270103Return.GenericArithmetic.ell)
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
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^((QRH.Record1252270103Return.GenericArithmetic.h:ℝ)+ζ)) →
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
        (Probe.principalScalar Finset.univ Z (QRH.Record1252270103Return.GenericArithmetic.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧
      ‖finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
          (Z^(QRH.Record1252270103Return.GenericArithmetic.x:ℝ)) (Z^(QRH.Record1252270103Return.GenericArithmetic.y:ℝ)) Z e alpha height/normer-
        Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT WC Y W0 W1
          (Z^(QRH.Record1252270103Return.GenericArithmetic.x:ℝ)) (Z^(QRH.Record1252270103Return.GenericArithmetic.y:ℝ)) Z e alpha height/normer‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ct,hCt,htransfer⟩ := finite_cube_fullW_arbitrary_saving
    (ι:=RayQuotient.Characters M H) K τ (saving+nu) b ζ B hτ (ha.trans_le hab) hζ hB
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Record1252270103LowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
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

end
end Candidate.FourthPower.ReturnFiniteError
