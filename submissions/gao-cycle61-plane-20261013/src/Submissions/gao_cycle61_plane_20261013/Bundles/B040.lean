/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B024
import Submissions.gao_cycle61_plane_20261013.Bundles.B039
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeErrorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CanonicalReduction; sha256 86f71e7b15d8c8f86dc994bc3bbb17c2f4cfb7f01154936d3798f2ac9389eb6e -/
section
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
                                               
                                                               
                                                
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O


theorem canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(Cycle61.Arithmetic.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Cycle61.Arithmetic.h:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^((7/8:ℝ)-(4+Cycle61.Transport.b)/6-(Cycle61.Arithmetic.y/2-Cycle61.Arithmetic.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail K δ a b B ζ saving hδ (by linarith [Cycle61.Transport.h_interval]) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((Cycle61.Arithmetic.h:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Cycle61.Transport.h_interval]))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Cycle61.Transport.b)/6-(Cycle61.Arithmetic.y/2-Cycle61.Arithmetic.h*(17/50-1/6)-1/50)+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CanonicalReduction -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CentralErrorSaving; sha256 8c987a22a172478141bdfcd1789a5144c6a37640238d7c4eaa8efee2433d21d6 -/
section
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
                                               
                                                               
                                                             
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(Cycle61.Arithmetic.x:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(Cycle61.Arithmetic.y:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith [Cycle61.Arithmetic.x_add_y, Cycle61.Transport.ly_coarse, Cycle61.Arithmetic.ell_pos, mul_nonneg (by linarith [Cycle61.Transport.ly_coarse] : 0 ≤ Cycle61.Arithmetic.y) ha, mul_nonneg (by linarith [Cycle61.Transport.ly_coarse] : 0 ≤ Cycle61.Arithmetic.y) he])

lemma central_prime_product_bound {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(Cycle61.Arithmetic.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(Cycle61.Arithmetic.ell:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/10000000000)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((Cycle61.Arithmetic.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(Cycle61.Arithmetic.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(6+3*Cycle61.Arithmetic.ell) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (Cycle61.Arithmetic.h:ℝ)+ζ≤1 by linarith [Cycle61.Transport.h_interval]))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(Cycle61.Arithmetic.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((Cycle61.Arithmetic.ell:ℝ)*(3:ℕ))=Z^(6+3*Cycle61.Arithmetic.ell) := by rw [←Real.rpow_add hZ0];congr 1;ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CentralErrorSaving -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CentralFiniteError; sha256 74bb2151c5c8eba0c9dc241c7839051a988e8e48e308ee801bcf810f540c932a -/
section
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
                                               
                                                               
                                                    
                                                         
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0 < Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(Cycle61.Arithmetic.ell:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(Cycle61.Arithmetic.ell:ℝ) := by
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

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CentralFiniteError -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CubeErrorSaving; sha256 672b567a8e49d0620fb8715a3ab1970505ca1307fdc08bf05667c562e8bc331a -/
section
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/
                                               
                                                            
                                                    
                                                        
namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0 < b) (hζ : ζ≤1/10000000000)
    (e : ℝ) (he : 0 < e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((Cycle61.Arithmetic.h:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(Cycle61.Arithmetic.ell:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2 < B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((8+3*Cycle61.Arithmetic.ell)+saving)/τ)
  have hN' : (8+3*Cycle61.Arithmetic.ell)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(Cycle61.Arithmetic.x:ℝ)) (Z^(Cycle61.Arithmetic.y:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤a) he.le
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

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CubeErrorSaving -/
