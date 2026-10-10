import ZetaZeroFree.Analytic.Principal.Residues
import OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import OAI.NumberTheory.DirichletL.PrimeRows.CentralWTail
import OAI.NumberTheory.DirichletL.PrimeRows.CentralZTail
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalLargeTail

namespace ZetaZeroFree.Analytic.Probe
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(13/33:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(15/33:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma central_prime_product_bound {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(5/33:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(5/33:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((25/33:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(5/33:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (25/33:ℝ)+ζ≤1 by linarith))
  have hpnew := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp : (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(1/6:ℝ) := hpnew.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)) (pow_nonneg hb _))
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(1/6:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((1/6:ℝ)*(3:ℕ))=Z^(13/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((25/33:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(5/33:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving)/τ)
  have hN' : (17/2:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)


lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(5/33:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(5/33:ℝ) := by
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


theorem finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((25/33:ℝ)+ζ)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(5/33:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((25/33:ℝ)+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (25/33:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (5/33:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
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

theorem small_source_physical_dyad_bound (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U → U≤Z^(1/200:ℝ) →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-67/99-1/20+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU hUsmall R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  have hscale : U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(13/33:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
        (Z^(15/33:ℝ))^((1/2:ℝ)-1))≤Z^(HeckeZeroSupremum.beta-67/99-1/20+8*e) := by
    have hUp : U^(8/5+δ-(17/50:ℝ))≤Z^((1/200)*(8/5+δ-(17/50:ℝ))) := by
      rw [Real.rpow_mul hZ0.le]
      exact Real.rpow_le_rpow (by linarith) hUsmall (by linarith)
    have hp : (∏i,(Z^(length i))^(17/50:ℝ))=Z^((5/33)*(17/50:ℝ)) := by
      simp_rw [←Real.rpow_mul hZ0.le]
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul,hl]
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUp (by positivity)) (by positivity))
    rw [hp]
    simp_rw [←Real.rpow_mul hZ0.le]
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(13/33:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(15/33:ℝ))^((1/2:ℝ)-1)) := hh
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*(U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(13/33:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(15/33:ℝ))^((1/2:ℝ)-1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

lemma source_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(5/33:ℝ)) (r : ℝ) :
    (∏i,(Z^(length i))^r)*
      ((Z^(13/33:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(15/33:ℝ))^((2:ℝ)-1))=
      Z^((109/66:ℝ)+(25/33:ℝ)*r) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

theorem source_large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((109/66:ℝ)+(25/33:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(13/33:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(15/33:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [source_large_source_scale Z hZ0 length hl r];ring

lemma source_large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0<Z) (n : ℕ) :
    Z^((109/66:ℝ)+(25/33:ℝ)*r)*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma source_source_large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    Summable (fun n : ℕ=>Z^((109/66:ℝ)+(25/33:ℝ)*r)*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [source_large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma source_large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    (∑'n : ℕ,Z^((109/66:ℝ)+(25/33:ℝ)*r)*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [source_large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_source_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤r ∧ 8/5+δ<r ∧
      (109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

theorem source_large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r) (hr' : 8/5+δ<r) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((25/33:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨C,hC,hmain⟩ := source_large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=>Z^((109/66:ℝ)+(25/33:ℝ)*r)*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^((25/33:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((25/33:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := source_source_large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((109/66:ℝ)+((25/33:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from source_large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

theorem source_large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤r ∧ 0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((25/33:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_source_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := source_large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

theorem source_large_original_physical_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((25/33:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((25/33:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5/33:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,C,hr,hC,hmain⟩ := source_large_physical_tail_arbitrary_saving K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=>norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring


end
end ZetaZeroFree.Analytic.Probe
