/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed polynomial exponent for the complete padded canonical pool.
Original slot cardinality enters only the constant and eventual threshold. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalPoolTransport
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularResidualInitialGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentPrimeSlot CenteredMomentSourceRectangle CenteredMomentEnergyBands
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
local notation "O"=>ActualEisensteinCubic.O

section Initial
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z : ℝ) (hZ : 0<Z) (η η₀ : Character) (R₀ : Ideal O)
variable (θ : ι→RayQuotient.Characters rayM H) (w v : ι→ℝ) (t : ℝ)
variable (p : Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hprod : Y₁*Y₂=X₁*X₂)
local notation "s" => initialInput rayM H hH W hW hsW Z hZ η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

/-- Product geometry retains the sum of marked widths. Multiplying one
coarse exponent per slot would incorrectly introduce N into the exponent. -/
theorem initial_full_column_cap (N : ℕ) (hN : Fintype.card ι≤N) (hZ1 : 1≤Z)
    (hx₁ : X₁≤Z) (hx₂ : X₂≤Z) (hy₁ : Y₁≤Z) (hy₂ : Y₂≤Z)
    (hw : (∑i,w i)≤1) :
    ∀I∈finiteColumns (Fintype.piFinset (s).pools),
      (I.absNorm:ℝ)≤(2:ℝ)^N*(9/4)^2*Z^(3:ℝ) := by
  intro I hI
  obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hI
  have hm (i:ι) : ((q (Sum.inl i)).absNorm:ℝ)≤2*Z^(w i) := by
    have hi:=Fintype.mem_piFinset.mp hq (Sum.inl i)
    change q (Sum.inl i)∈primePool rayM H 2 (Z^(w i)) at hi
    have hn := (Nat.cast_le.mpr (mem_idealsUpTo.mp (Finset.mem_filter.mp hi).1).2).trans
      (Nat.floor_le (by positivity : 0≤max 1 (2:ℝ)*Z^(w i)))
    simpa only [max_eq_right (by norm_num : (1:ℝ)≤2)] using hn
  have hp (j:Fin 2) : ((q (Sum.inr j)).absNorm:ℝ)≤(9/4)*Z := by
    have hj:=Fintype.mem_piFinset.mp hq (Sum.inr j)
    fin_cases j
    · change q (Sum.inr 0)∈plainSupportPool (9/4) X₁ Y₁ at hj
      rcases Finset.mem_union.mp hj with hj|hj
      · exact ((mem_idealBall _ _).mp hj).2.trans (mul_le_mul_of_nonneg_left hx₁ (by norm_num))
      · exact ((mem_idealBall _ _).mp hj).2.trans (mul_le_mul_of_nonneg_left hy₁ (by norm_num))
    · change q (Sum.inr 1)∈plainSupportPool (9/4) X₂ Y₂ at hj
      rcases Finset.mem_union.mp hj with hj|hj
      · exact ((mem_idealBall _ _).mp hj).2.trans (mul_le_mul_of_nonneg_left hx₂ (by norm_num))
      · exact ((mem_idealBall _ _).mp hj).2.trans (mul_le_mul_of_nonneg_left hy₂ (by norm_num))
  have hmarks : (∏i,((q (Sum.inl i)).absNorm:ℝ))≤(2:ℝ)^N*Z := by
    calc
      _≤∏i,2*Z^(w i) := Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _) (fun i _=>hm i)
      _=(2:ℝ)^Fintype.card ι*Z^(∑i,w i) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←Real.rpow_sum_of_pos hZ]
      _≤_ := mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN)
        (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1 hw)
        (Real.rpow_nonneg hZ.le _) (by positivity)
  rw [finiteTupleProduct,map_prod,Nat.cast_prod,Fintype.prod_sum_type,Fin.prod_univ_two]
  calc
    _≤((2:ℝ)^N*Z)*(((9/4)*Z)*((9/4)*Z)) :=
      mul_le_mul hmarks (mul_le_mul (hp 0) (hp 1) (Nat.cast_nonneg _) (by positivity))
        (by positivity) (by positivity)
    _=_ := by norm_num [pow_succ];ring
end Initial

/-- The polynomial exponent four is independent of every slot cardinality. -/
theorem eventual_full_pool_absorption (N : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ (2:ℝ)^N*(9/4)^2*Z^(3:ℝ)≤Z^(4:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((2:ℝ)^N*(9/4)^2)] with Z hZ hc
  refine ⟨hZ,?_⟩
  calc
    _≤Z*Z^(3:ℝ) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(4:ℝ) := by norm_num [pow_succ];ring

end
end QRH.Record1252270103Source.InitialPhysical
#print axioms QRH.Record1252270103Source.InitialPhysical.initial_full_column_cap
#print axioms QRH.Record1252270103Source.InitialPhysical.eventual_full_pool_absorption
