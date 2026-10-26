import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.RepeatedSlots
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option maxHeartbeats 0
namespace RepeatedPrimeSlots
noncomputable section
open scoped Classical BigOperators

theorem sum_comp_le_total {I J : Type*} [Fintype I] [Fintype J]
    (f : J → I) (hf : Function.Injective f) (w : I → ℝ) (hw : ∀i,0≤w i) :
    (∑j,w (f j)) ≤ ∑i,w i := by
  classical
  calc
    _ = ∑i∈Finset.univ.image f,w i := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑i,w i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => hw i)

theorem sum_family_energy {Row Color : Type*} [Fintype Color]
    (rows : Finset Row) (F : Color → Row → ℂ) (E : ℝ)
    (h : ∀ c, ∑ u ∈ rows, ‖F c u‖^2 ≤ E) :
    (∑ u ∈ rows, ‖∑ c, F c u‖^2) ≤ (Fintype.card Color : ℝ)^2*E := by
  have hp (u : Row) : ‖∑ c, F c u‖^2 ≤
      (Fintype.card Color : ℝ) * ∑ c, ‖F c u‖^2 := by
    apply ((sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr (norm_sum_le _ _)).trans
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun (_ : Color) => (1 : ℝ)) (fun c => ‖F c u‖)
  calc
    _ ≤ ∑ u ∈ rows, (Fintype.card Color : ℝ)*∑ c, ‖F c u‖^2 :=
      Finset.sum_le_sum (fun u _ => hp u)
    _ = (Fintype.card Color : ℝ)*∑ c, ∑ u ∈ rows, ‖F c u‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card Color : ℝ)*∑ c : Color, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => h c)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two,mul_assoc]

/-- Coloring separates the injective part with a cost depending only on the
number of slots. The number of available primes cancels exactly. -/
theorem injective_coloring_energy {Row A I : Type*} [Fintype A] [Fintype I]
    [Nonempty I] (rows : Finset Row) (a : Row → I → A → ℂ) (D : Row → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (h : ∀ c : A → I,
      (∑ u ∈ rows, ‖D u*(∏ i, ∑ p : A, if c p=i then a u i p else 0)‖^2) ≤ E) :
    (∑ u ∈ rows, ‖D u*(∑ x : I → A,
      if Function.Injective x then ∏ i, a u i (x i) else 0)‖^2) ≤
      (Fintype.card I : ℝ)^(2*Fintype.card I)*E := by
  classical
  by_cases hx : ∃ x : I → A, Function.Injective x
  · obtain ⟨x,hx⟩ := hx
    have hcard : Fintype.card I ≤ Fintype.card A := Fintype.card_le_of_injective x hx
    let c : ℕ := Fintype.card I^(Fintype.card A-Fintype.card I)
    have hc : 0 < (c : ℝ) := by
      exact_mod_cast Nat.pow_pos (Fintype.card_pos : 0 < Fintype.card I)
    let F (col : A → I) (u : Row) : ℂ :=
      D u*(∏ i, ∑ p : A, if col p=i then a u i p else 0)
    have he := sum_family_energy rows F E h
    have hid (u : Row) : (∑ col, F col u) = (c : ℂ)*
        (D u*(∑ x : I → A, if Function.Injective x then ∏ i, a u i (x i) else 0)) := by
      dsimp only [F]
      rw [←Finset.mul_sum,sum_colored_products]
      ring
    simp_rw [hid,norm_mul,Complex.norm_natCast,mul_pow] at he
    rw [←Finset.mul_sum,Fintype.card_fun] at he
    have hp : ((Fintype.card I^Fintype.card A : ℕ) : ℝ)^2 =
        (c : ℝ)^2*(Fintype.card I : ℝ)^(2*Fintype.card I) := by
      have heq : Fintype.card I^Fintype.card A = c*Fintype.card I^Fintype.card I := by
        dsimp [c]
        rw [←pow_add,Nat.sub_add_cancel hcard]
      rw [heq]
      simp only [Nat.cast_mul,Nat.cast_pow,mul_pow,←pow_mul,Nat.mul_comm]
      ring
    rw [hp,mul_assoc] at he
    simpa only [norm_mul,mul_pow] using
      (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp he
  · have hzero (u : Row) : (∑ x : I → A,
        if Function.Injective x then ∏ i, a u i (x i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [ite_eq_right (fun hi => hx ⟨x,hi⟩)]
    simp only [hzero,mul_zero,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    positivity

end
end RepeatedPrimeSlots

end Record1252270103Bootstrap.PR67
