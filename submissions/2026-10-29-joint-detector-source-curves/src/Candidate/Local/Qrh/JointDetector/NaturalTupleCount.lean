/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Candidate.Local.Qrh.JointDetector.NaturalSelectedNorm

/-! Counting the actual higher-colour fibres by their product ideal.
The divisor multiplicity belongs to the original product, and all tuples in
the given finite family are retained. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

def higherIdeal (v : HigherTuple) : Ideal O := ∏ j, v j

theorem higherIdeal_ne_zero (v : HigherTuple) (h : ∀ j, v j ≠ 0) : higherIdeal v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => h j)

theorem higher_fibre_count (F : Finset HigherTuple) (I : Ideal O) (hI : I ≠ 0) :
    (F.filter fun v => higherIdeal v=I).card ≤ (idealDivisors I).card^4 := by
  let S := F.filter fun v => higherIdeal v=I
  let f : S → (Fin 4 → idealDivisors I) := fun v j =>
    ⟨v.val j,(mem_idealDivisors hI).mpr (by
      rw [← (Finset.mem_filter.mp v.property).2]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j))⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun he j)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h

/-- A uniform count at the residual higher-product radius. In the shared-table
application this radius is V/(H J F) or V/(H J E), not the original V. -/
theorem higher_tuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset HigherTuple) (V : ℝ),
      1 ≤ V → (∀ v ∈ F, ∀ j, v j ≠ 0) →
      (∀ v ∈ F, (Ideal.absNorm (higherIdeal v):ℝ) ≤ V) →
      (F.card:ℝ) ≤ C*V*V^ε := by
  have he : 0 < ε/4 := by positivity
  let K := idealDivisorConstant (ε/4) he
  have hK : 0 < K := idealDivisorConstant_pos _ _
  refine ⟨128*K^4,by positivity,?_⟩
  intro F V hV1 hn hnorm
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one hV1
  let S := F.image higherIdeal
  have hS0 : ∀ I ∈ S, I ≠ 0 := by
    intro I hI
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact higherIdeal_ne_zero v (hn v hv)
  have hSN : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ V := by
    intro I hI
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact hnorm v hv
  have hcard := DescentFiberCost.finite_ideal_count_real S V hV1 hS0 hSN
  have hfibre (I : Ideal O) (hI : I ∈ S) :
      ((F.filter fun v => higherIdeal v=I).card:ℝ) ≤ K^4*V^ε := by
    have hNI : 0 < (Ideal.absNorm I:ℝ) := norm_pos (hS0 I hI)
    have hc : ((idealDivisors I).card:ℝ) ≤ K*(Ideal.absNorm I:ℝ)^(ε/4) :=
      idealDivisorConstant_bound _ _ I (hS0 I hI)
    calc
      _ ≤ ((idealDivisors I).card:ℝ)^4 := by exact_mod_cast higher_fibre_count F I (hS0 I hI)
      _ ≤ (K*(Ideal.absNorm I:ℝ)^(ε/4))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
      _ = K^4*(Ideal.absNorm I:ℝ)^ε := by
        rw [mul_pow,← Real.rpow_mul_natCast hNI.le]
        congr 1
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNI.le (hSN I hI) hε.le) (by positivity)
  have hsplit : (F.card:ℝ)=∑ I ∈ S, ((F.filter fun v => higherIdeal v=I).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image higherIdeal F
  rw [hsplit]
  calc
    _ ≤ ∑ _I ∈ S, K^4*V^ε := Finset.sum_le_sum hfibre
    _ = (S.card:ℝ)*(K^4*V^ε) := by simp
    _ ≤ (128*V)*(K^4*V^ε) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- A crude polynomial row count, sufficient for the complete Schwartz tail. -/
theorem ideal_tuple_count_crude {n : ℕ} (F : Finset (Fin n → Ideal O)) (Y : ℝ)
    (hY : 1 ≤ Y) (hn : ∀ c ∈ F, ∀ j, c j ≠ 0)
    (hN : ∀ c ∈ F, ∀ j, (Ideal.absNorm (c j):ℝ) ≤ Y) :
    (F.card:ℝ) ≤ (128*Y)^n := by
  let S := F.biUnion fun c => Finset.univ.image c
  have hS0 : ∀ I ∈ S, I ≠ 0 := by
    intro I hI
    obtain ⟨c,hc,hI⟩ := Finset.mem_biUnion.mp hI
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hI
    exact hn c hc j
  have hSN : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ Y := by
    intro I hI
    obtain ⟨c,hc,hI⟩ := Finset.mem_biUnion.mp hI
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hI
    exact hN c hc j
  let f : F → (Fin n → S) := fun c j =>
    ⟨c.val j,Finset.mem_biUnion.mpr ⟨c.val,c.property,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun he j)
  have hc : F.card ≤ S.card^n := by
    simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  have hcount := DescentFiberCost.finite_ideal_count_real S Y hY hS0 hSN
  exact (show (F.card:ℝ) ≤ (S.card:ℝ)^n by exact_mod_cast hc).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount n)

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.higher_tuple_count
