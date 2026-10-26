/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.SecondZero.Caps
import Submissions.hailey_collet_1252270103.Cycle61.Physical.TerminalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61SecondZero
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentFiniteProfileExceptional
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationErrorEnergy EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

/-- Actual normalized second-zero source at a physical radius. -/
def radiusTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ‖((K : ℂ)*paperRadialFourier W 0)*
    sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) s.η s.t‖/volume s.toData

lemma radiusTerm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    0 ≤ radiusTerm s R seed W K := div_nonneg (norm_nonneg _) (volume_pos _).le

lemma radiusTerm_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hKL : K ≤ L) : radiusTerm s R seed W K ≤ radiusTerm s R seed W L := by
  have hL : 0 ≤ L := hK.trans hKL
  unfold radiusTerm
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK,abs_of_nonneg hL]
  gcongr
  exact (volume_pos s.toData).le

/-- The side-reference and amplifier normalization is explicit. The nominal
radius gate is geometric, not an assumed estimate for the zero source. -/
theorem actual_main_second_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (lo hi : ℝ), 0 < lo → 0 ≤ hi →
    ∀ (s : Input ι) (p : Profiles lo hi), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s.toData ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) →
    Z^(-a-(A-c+Rw+E+Bc))*
      radiusTerm s R seed W (mainCommonRadius Z d K0 c (3*a) δ reserve) ≤
    C*zeroControl s p ε*‖paperRadialFourier W 0‖*
      Z^(-M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_second_zero_power N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E
    K0 nominalLoss δ reserve B s₀ hZ hb hM hA ha hc hd hBc hK0 hvol hseedN
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hh := hbound hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z
    (K0+max (d-c) 0+2*(3*a)+δ+reserve) B s₀ hZ.le hvol hseedN
  have hmin : max (d-c) 0-d = -min c d := by
    by_cases h : c ≤ d
    · rw [max_eq_left (sub_nonneg.mpr h),min_eq_left h]; ring
    · rw [max_eq_right (by linarith),min_eq_right (by linarith)]; ring
  have he : -a-(A-c+Rw+E+Bc)+(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀) ≤
      -M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀ := by
    have hs := Cycle61.Physical.second_zero_excess_bound hb hM hA ha hc hd hBc
    linarith
  have hf : 0 ≤ C*zeroControl s p ε*‖paperRadialFourier W 0‖ :=
    mul_nonneg (mul_nonneg hC.le (zeroControl_nonneg _ _ _)) (norm_nonneg _)
  calc
    _ ≤ Z^(-a-(A-c+Rw+E+Bc))*(C*zeroControl s p ε*‖paperRadialFourier W 0‖*
        Z^(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀)) := by
      exact mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = (C*zeroControl s p ε*‖paperRadialFourier W 0‖)*
        Z^(-a-(A-c+Rw+E+Bc)+(K0+max (d-c) 0+2*(3*a)+δ+reserve+ε*B-s₀)) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) hf

/-- Enlarged extracted radii remain below the main radius for every actual
extracted prime power 1, 6, or 7. No source monotonicity is presumed. -/
lemma actual_error_radius_le_main (Z d K0 c a δ reserve : ℝ) (hZ : 1 < Z)
    (ha : 0 ≤ a) (q : O) (hq : q ≠ 0) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    errorCommonRadius Z d K0 c (3*a) δ reserve q k ≤
      mainCommonRadius Z d K0 c (3*a) δ reserve := by
  have hl := Real.logb_nonneg hZ (normValue_ge_one q hq)
  have hm : errorMoving q Z k ≤ 2*errorRemoval q Z k := by
    rcases hk with rfl|rfl|rfl <;> simp [errorMoving,errorRemoval] <;> linarith
  unfold errorCommonRadius mainCommonRadius
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hx := max_le_max_right (0:ℝ) (show d-c-2*errorRemoval q Z k+errorMoving q Z k ≤ d-c by linarith)
  linarith

lemma actual_error_cost_le_one (q : O) (hq : q ≠ 0) (n : ℕ) : localErrorCost q n ≤ 1 := by
  have hq1 := normValue_ge_one q hq
  have hq0 := normValue_pos q hq
  have hi : (normValue q)⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hq1
  have hn : 0 ≤ (normValue q)⁻¹ := inv_nonneg.mpr hq0.le
  unfold localErrorCost
  change (if n=5 then (1-(normValue q)⁻¹)^2 else (normValue q)⁻¹) ≤ 1
  split_ifs <;> nlinarith

/-- The literal squared extraction scalar is paid together with its physical
radius, retaining every twice-child coefficient, mask, and height phase. -/
lemma actual_extracted_second_zero_le_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (Z d K0 c a δ reserve : ℝ) (hZ : 1 < Z) (ha : 0 ≤ a)
    (q : O) (hq : q ≠ 0) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    localErrorCost q (k-1)*radiusTerm s R seed W
      (errorCommonRadius Z d K0 c (3*a) δ reserve q k) ≤
      radiusTerm s R seed W (mainCommonRadius Z d K0 c (3*a) δ reserve) := by
  have hrad := actual_error_radius_le_main Z d K0 c a δ reserve hZ ha q hq k hk
  have hp : 0 ≤ errorCommonRadius Z d K0 c (3*a) δ reserve q k :=
    Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  exact (mul_le_of_le_one_left (radiusTerm_nonneg _ _ _ _ _)
    (actual_error_cost_le_one q hq (k-1))).trans (radiusTerm_mono s R seed W hp hrad)

/-- Uniform extracted second-zero certificate from the genuine source
diagonal, with the original extraction weight and the nominal loss explicit. -/
theorem actual_extracted_second_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι ≤ N → ∀ (lo hi : ℝ), 0 < lo → 0 ≤ hi →
    ∀ (s : Input ι) (p : Profiles lo hi), s.W₁ = p.profile 0 → s.W₂ = p.profile 1 →
    ∀ (R seed : Ideal O), seed ≠ 0 → ∀ (W : 𝓢(ℝ,ℂ))
    (Z beta M A a c d Bc Rw E K0 nominalLoss δ reserve B s₀ : ℝ), 1 < Z →
    3401/100000 ≤ beta ∧ beta ≤ 1/25 → 0 ≤ M →
    A ≤ M*Cycle61.Arithmetic.totalA beta → a ≤ M*Cycle61.Arithmetic.amp beta →
    0 ≤ c → 0 ≤ d → 0 ≤ Bc → K0 ≤ 2*A-c-d+Rw+E-M+nominalLoss →
    volume s.toData ≤ Z^B → Z^s₀ ≤ (seed.absNorm : ℝ) → 0 ≤ a →
    ∀ (q : O), q ≠ 0 → ∀ k : ℕ, k=1 ∨ k=6 ∨ k=7 →
    Z^(-a-(A-c+Rw+E+Bc))*(localErrorCost q (k-1)*
      radiusTerm s R seed W (errorCommonRadius Z d K0 c (3*a) δ reserve q k)) ≤
    C*zeroControl s p ε*‖paperRadialFourier W 0‖*
      Z^(-M*(8754683599/120632400000)+nominalLoss+δ+reserve+ε*B-s₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_main_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc Rw E
    K0 nominalLoss δ reserve B s₀ hZ hb hM hA ha hc hd hBc hK0 hvol hseedN ha0 q hq k hk
  have hm := hbound hcard lo hi hlo hhi s p h₁ h₂ R seed hseed W Z beta M A a c d Bc
    Rw E K0 nominalLoss δ reserve B s₀ hZ hb hM hA ha hc hd hBc hK0 hvol hseedN
  have he := actual_extracted_second_zero_le_main s R seed W Z d K0 c a δ reserve hZ ha0 q hq k hk
  exact (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans hm

end
end OAI.SevenEighths.Cycle61SecondZero
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_main_second_zero
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_extracted_second_zero_le_main
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_extracted_second_zero
#print axioms OAI.SevenEighths.Cycle61SecondZero.radiusTerm_nonneg
#print axioms OAI.SevenEighths.Cycle61SecondZero.radiusTerm_mono
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_error_radius_le_main
#print axioms OAI.SevenEighths.Cycle61SecondZero.actual_error_cost_le_one
