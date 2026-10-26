/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A single forced-divisor constant covers every surviving marked subtype below
a fixed original slot cap. This uses the actual allocation divisor bound. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedForcedExceptional
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
open IdealMobiusDivisorSum
open CenteredMomentSourceMass CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationChildInput CenteredMomentSecondHeightFamily
open Record1252270103Second
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
local instance correctedForcedUniformDecidable (ι : Type*) : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem marked_forced_allocation_mass_uniform (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N → ∀(s : Input ι) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → forcedAllocationMass s (Collision.markedSourceModifier A₁ A₂ D K F) R L≤
        K₀*(L.absNorm:ℝ)^ε := by
  obtain ⟨K₀,hK₀,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/8) (by positivity)
  obtain ⟨D₀,hD₀,halloc⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/8) (by positivity)
  refine ⟨(K₀*D₀)^2,by positivity,?_⟩
  intro ι inst hcardι s A₁ A₂ D K R L F hL
  let mod := Collision.markedSourceModifier (ι:=ι) A₁ A₂ D K F
  let T := forcedLabels L (forcedSource s mod R L)
  have hsub : T⊆idealDivisors (L^2) := by
    intro C hC
    exact (mem_idealDivisors (pow_ne_zero 2 hL.ne_zero)).mpr
      (marked_forced_label_dvd_square s A₁ A₂ D K R L F hL ⟨C,hC⟩)
  have hone : (0:ℝ)≤L.absNorm := Nat.cast_nonneg _
  have hr : (((L.absNorm:ℝ)^2):ℝ)^(ε/8)=(L.absNorm:ℝ)^(ε/4) := by
    rw [←Real.rpow_natCast_mul hone]
    congr 1
    norm_num
    ring
  have hcard : (T.card:ℝ)≤K₀*(L.absNorm:ℝ)^(ε/4) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    apply (hdiv (L^2) (pow_ne_zero 2 hL.ne_zero)).trans_eq
    rw [map_pow,Nat.cast_pow,hr]
  have heach (C : T) : ((actualAllocations s.pools (C:Ideal O)).card:ℝ)≤D₀*(L.absNorm:ℝ)^(ε/4) := by
    have hCd := marked_forced_label_dvd_square s A₁ A₂ D K R L F hL C
    have hnorm : ((C:Ideal O).absNorm:ℝ)≤(L.absNorm:ℝ)^2 := by
      have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (pow_ne_zero 2 hL.ne_zero))) (map_dvd Ideal.absNorm hCd)
      simpa only [map_pow,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr hh
    apply (halloc (by simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hcardι 2) s.pools C (forcedLabel_ne_zero L _ C)).trans
    apply mul_le_mul_of_nonneg_left _ hD₀.le
    exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm (by positivity)).trans_eq hr
  have hh : forcedAllocationMass s mod R L≤(T.card:ℝ)^2*(D₀*(L.absNorm:ℝ)^(ε/4))^2 := by
    unfold forcedAllocationMass
    apply le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun C _=>pow_le_pow_left₀ (Nat.cast_nonneg _) (heach C) 2)) (Nat.cast_nonneg _))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    dsimp only [T]
    exact le_of_eq (by ring)
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg _))
  apply le_of_eq
  have hpow : ((L.absNorm:ℝ)^(ε/4))^4=(L.absNorm:ℝ)^ε := by
    rw [←Real.rpow_mul_natCast hone]
    congr 1
    ring
  calc
    _=(K₀*D₀)^2*((L.absNorm:ℝ)^(ε/4))^4 := by ring
    _=_ := by rw [hpow]

/-- Literal marked-source artificial-divisor payment. The input is the
actual seed-one child source after complete common allocation. -/
theorem marked_corrected_forced_source_uniform (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N → ∀(s : Input ι) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → ∀(τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ),
      0<H → 0≤E → (∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) →
      (∀C : forcedLabels L (forcedSource s (Collision.markedSourceModifier A₁ A₂ D K F) R L),
        ∀B : actualAllocations s.pools (C:Ideal O),
        childDivisorEnergy s (Collision.markedSourceModifier A₁ A₂ D K F) C R 1 B τ t keep Φ H/
          volume (child s C R B τ t)≤E) →
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s (Collision.markedSourceModifier A₁ A₂ D K F) R L) (heightCoeff τ t) Φ H/volume s≤
        K₀*(L.absNorm:ℝ)^ε*(forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hbound⟩ := marked_forced_allocation_mass_uniform N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro ι inst hcardι s A₁ A₂ D K R L F hL τ t keep Φ H E hH hE hΦ hchild
  apply (actual_forced_norm_saving s (Collision.markedSourceModifier A₁ A₂ D K F) R L hL.ne_zero
    τ t keep Φ H E hH hE hΦ hchild).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hbound hcardι s A₁ A₂ D K R L F hL)
    (mul_nonneg (forcedProfileCost_nonneg s) hE)

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.marked_forced_allocation_mass_uniform
#print axioms OAI.SevenEighths.Record1252270103Source.marked_corrected_forced_source_uniform
