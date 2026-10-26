import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Cauchy

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentCauchy CenteredMomentSmooth

def jointPaddedCoefficient {Label κ : Type*} [DecidableEq Label]
    {α : Label → Type*} (tag : κ → Label) (c : (k : κ) → α (tag k) → ℂ)
    (k : κ) (i : Sigma α) : ℂ :=
  if h : i.1 = tag k then c k (h ▸ i.2) else 0

theorem joint_padded_sum {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (f : (l : Label) → α l → ℂ) (k : κ) :
    (∑ i : Sigma α, jointPaddedCoefficient tag c k i * f i.1 i.2) =
      ∑ i : α (tag k), c k i * f (tag k) i := by
  rw [Fintype.sum_sigma]
  have hinner (l : Label) :
      (∑ i : α l, jointPaddedCoefficient tag c k ⟨l,i⟩ * f l i) =
        if h : l = tag k then ∑ i : α (tag k), c k i * f (tag k) i else 0 := by
    by_cases h : l = tag k
    · subst l
      simp only [jointPaddedCoefficient, dite_true]
    · simp only [jointPaddedCoefficient, h, dite_false, zero_mul, Finset.sum_const_zero]
  simp_rw [hinner]
  simp

theorem joint_padded_left_column {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (u : (l : Label) → α l → ℝ)
    (V : ℝ → ℂ) (k : κ) (t : ℝ) :
    leftColumn Finset.univ (jointPaddedCoefficient tag c k) V (fun i => u i.1 i.2) t =
      leftColumn Finset.univ (c k) V (u (tag k)) t := by
  exact joint_padded_sum tag c (fun l i => columnPhase V (u l i) t) k

theorem joint_padded_right_column {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (u : (l : Label) → α l → ℝ)
    (V : ℝ → ℂ) (k : κ) (t : ℝ) :
    rightColumn Finset.univ (jointPaddedCoefficient tag c k) V (fun i => u i.1 i.2) t =
      rightColumn Finset.univ (c k) V (u (tag k)) t := by
  have he (i : Sigma α) : star (jointPaddedCoefficient tag c k i) =
      jointPaddedCoefficient tag (fun k i => star (c k i)) k i := by
    unfold jointPaddedCoefficient
    split_ifs <;> simp
  simp only [rightColumn, he]
  exact joint_padded_sum tag (fun k i => star (c k i))
    (fun l i => columnPhase V (u l i) t) k

theorem joint_padded_kernel {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α β : Label → Type*} [∀ l, Fintype (α l)] [∀ l, Fintype (β l)]
    (tag : κ → Label) (c : (k : κ) → α (tag k) → ℂ)
    (d : (k : κ) → β (tag k) → ℂ)
    (u : (l : Label) → α l → ℝ) (v : (l : Label) → β l → ℝ)
    (K : ℝ → ℝ → ℂ) (k : κ) :
    (∑ i : Sigma α, ∑ j : Sigma β,
      (jointPaddedCoefficient tag c k i * star (jointPaddedCoefficient tag d k j)) *
        K (u i.1 i.2) (v j.1 j.2)) =
      ∑ i : α (tag k), ∑ j : β (tag k),
        (c k i * star (d k j)) * K (u (tag k) i) (v (tag k) j) := by
  have he (j : Sigma β) : star (jointPaddedCoefficient tag d k j) =
      jointPaddedCoefficient tag (fun k j => star (d k j)) k j := by
    unfold jointPaddedCoefficient
    split_ifs <;> simp
  simp_rw [he, mul_assoc]
  have hi (i : Sigma α) :
      (∑ j : Sigma β, jointPaddedCoefficient tag (fun k j => star (d k j)) k j *
        K (u i.1 i.2) (v j.1 j.2)) =
      ∑ j : β (tag k), star (d k j) * K (u i.1 i.2) (v (tag k) j) :=
    joint_padded_sum tag (fun k j => star (d k j))
      (fun l j => K (u i.1 i.2) (v l j)) k
  have hout : (∑ i : Sigma α, ∑ j : Sigma β,
      jointPaddedCoefficient tag c k i *
        (jointPaddedCoefficient tag (fun k j => star (d k j)) k j *
          K (u i.1 i.2) (v j.1 j.2))) =
      ∑ i : Sigma α, jointPaddedCoefficient tag c k i *
        (∑ j : β (tag k), star (d k j) * K (u i.1 i.2) (v (tag k) j)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, hi i]
  rw [hout]
  have hh := joint_padded_sum tag c
    (fun l i => ∑ j : β (tag k), star (d k j) * K (u l i) (v (tag k) j)) k
  simpa only [Finset.mul_sum, mul_assoc] using hh

theorem whole_kernel_dependent_row_estimate (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {Label κ : Type*} [Fintype Label] [DecidableEq Label]
        {α β : Label → Type*} [∀ l, Fintype (α l)] [∀ l, Fintype (β l)],
      ∀ (rows : Finset κ) (tag : κ → Label)
        (c : (k : κ) → α (tag k) → ℂ) (d : (k : κ) → β (tag k) → ℂ)
        (u : (l : Label) → α l → ℝ) (v : (l : Label) → β l → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ,
        Real.sqrt (∑ k ∈ rows, ‖leftColumn Finset.univ (c k) (V 2) (u (tag k)) t‖^2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn Finset.univ (d k) (V 3) (v (tag k)) t‖^2) ≤
          E*(1+‖t‖)^J) →
      (1+R)^A * ‖∑ k ∈ rows, η k *
        (∑ i : α (tag k), ∑ j : β (tag k), (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u (tag k) i) (v (tag k) j))‖ ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR Label κ _ _ α β _ _ rows tag c d u v ρ x η hη hV₀ hV₁ E hE henergy
  have hh := hbound R hR rows (Finset.univ : Finset (Sigma α))
    (Finset.univ : Finset (Sigma β)) (jointPaddedCoefficient tag c)
    (jointPaddedCoefficient tag d) (fun i => u i.1 i.2) (fun j => v j.1 j.2)
    ρ x η hη hV₀ hV₁ E hE (by
      intro t
      simpa only [joint_padded_left_column, joint_padded_right_column] using henergy t)
  simpa only [joint_padded_kernel] using hh

#print axioms whole_kernel_dependent_row_estimate
#print axioms joint_padded_sum
#print axioms joint_padded_left_column
#print axioms joint_padded_right_column
end
end OAI.SevenEighths.Cycle61Moment
