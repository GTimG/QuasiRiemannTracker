/- Copyright (c) 2026 Sil. Apache-2.0.
Generic degree-(2,3) polynomial certificates. The only upstream import is
Hailey Collet's small tensor-Bernstein basis, not an endpoint certificate. -/
import Submissions.hailey_collet_1252270103.Cycle61.Arithmetic.Bernstein.Basis

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnBernstein
noncomputable section

open Cycle61.Arithmetic.Bernstein

abbrev Coeff := Fin 3 → Fin 4 → ℝ

def eval (c : Coeff) (δ p : ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * δ^(i.val) * p^(j.val)

def deltaAffine (c : Coeff) (a r : ℝ) : Coeff :=
  ![fun j => c 0 j+a*c 1 j+a^2*c 2 j,
    fun j => r*c 1 j+2*a*r*c 2 j,
    fun j => r^2*c 2 j]

def pAffine (c : Coeff) (a r : ℝ) : Coeff := fun i =>
  ![c i 0+a*c i 1+a^2*c i 2+a^3*c i 3,
    r*(c i 1+2*a*c i 2+3*a^2*c i 3),
    r^2*(c i 2+3*a*c i 3), r^3*c i 3]

def deltaBernstein (c : Coeff) : Coeff :=
  ![fun j => c 0 j, fun j => c 0 j+c 1 j/2,
    fun j => c 0 j+c 1 j+c 2 j]

def pBernstein (c : Coeff) : Coeff := fun i =>
  ![c i 0, c i 0+c i 1/3,
    c i 0+2*c i 1/3+c i 2/3, c i 0+c i 1+c i 2+c i 3]

def coefficients (c : Coeff) (a b e f : ℝ) : Coeff :=
  pBernstein (deltaBernstein (pAffine (deltaAffine c a (b-a)) e (f-e)))

theorem affine_eval (c : Coeff) (a r e s u v : ℝ) :
    eval c (a+r*u) (e+s*v) = eval (pAffine (deltaAffine c a r) e s) u v := by
  simp [eval, pAffine, deltaAffine, Fin.sum_univ_succ]
  ring

theorem bernstein_eval (c : Coeff) (u v : ℝ) :
    eval c u v = tensor (pBernstein (deltaBernstein c)) u v := by
  simp [eval, tensor, basis2, basis3, pBernstein, deltaBernstein, Fin.sum_univ_succ]
  ring

theorem box_eval (c : Coeff) (a b e f u v : ℝ) :
    eval c (a+(b-a)*u) (e+(f-e)*v) = tensor (coefficients c a b e f) u v := by
  exact (affine_eval c a (b-a) e (f-e) u v).trans
    (bernstein_eval (pAffine (deltaAffine c a (b-a)) e (f-e)) u v)

theorem positive_on_box {c : Coeff} {a b e f m : ℝ}
    (hab : a < b) (hef : e < f) (hm : 0 < m)
    (hc : ∀ i j, m ≤ coefficients c a b e f i j)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc e f) :
    0 < eval c δ p := by
  have hu := normalize_mem hab hδ
  have hv := normalize_mem hef hp
  have heδ : a+(b-a)*((δ-a)/(b-a)) = δ := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    <;> ring
  have hep : e+(f-e)*((p-e)/(f-e)) = p := by
    field_simp [ne_of_gt (sub_pos.mpr hef)]
    <;> ring
  have hpos := tensor_pos hm hu hv hc
  rw [← box_eval, heδ, hep] at hpos
  exact hpos

/-- An explicitly supplied Bernstein table is sound only after its complete
polynomial identity has been proved. This avoids recalculating the same affine
change of variables separately for each of the twelve inequalities. -/
theorem positive_on_box_from_tensor {c β : Coeff} {a b e f m : ℝ}
    (heq : ∀ u v : ℝ, eval c (a+(b-a)*u) (e+(f-e)*v) = tensor β u v)
    (hab : a < b) (hef : e < f) (hm : 0 < m)
    (hβ : ∀ i j, m ≤ β i j)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc e f) :
    0 < eval c δ p := by
  have hu := normalize_mem hab hδ
  have hv := normalize_mem hef hp
  have heδ : a+(b-a)*((δ-a)/(b-a)) = δ := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    <;> ring
  have hep : e+(f-e)*((p-e)/(f-e)) = p := by
    field_simp [ne_of_gt (sub_pos.mpr hef)]
    <;> ring
  have hpos := tensor_pos hm hu hv hβ
  have hident := heq ((δ-a)/(b-a)) ((p-e)/(f-e))
  rw [heδ, hep] at hident
  rw [hident]
  exact hpos

theorem certificate_sound {g : ℝ → ℝ → ℝ} {c : Coeff} {a b e f m : ℝ}
    (heq : ∀ δ p, g δ p = eval c δ p)
    (hab : a < b) (hef : e < f) (hm : 0 < m)
    (hc : ∀ i j, m ≤ coefficients c a b e f i j)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc e f) :
    0 < g δ p := by
  rw [heq]
  exact positive_on_box hab hef hm hc hδ hp

/-- A closed split keeps the dividing line in both children. -/
theorem split_delta {P : ℝ → ℝ → Prop} {a b e f m : ℝ}
    (hl : ∀ {δ p : ℝ}, δ ∈ Set.Icc a m → p ∈ Set.Icc e f → P δ p)
    (hr : ∀ {δ p : ℝ}, δ ∈ Set.Icc m b → p ∈ Set.Icc e f → P δ p)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc e f) : P δ p := by
  rcases le_total δ m with h | h
  · exact hl ⟨hδ.1, h⟩ hp
  · exact hr ⟨h, hδ.2⟩ hp

theorem split_p {P : ℝ → ℝ → Prop} {a b e f m : ℝ}
    (hl : ∀ {δ p : ℝ}, δ ∈ Set.Icc a b → p ∈ Set.Icc e m → P δ p)
    (hr : ∀ {δ p : ℝ}, δ ∈ Set.Icc a b → p ∈ Set.Icc m f → P δ p)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc a b) (hp : p ∈ Set.Icc e f) : P δ p := by
  rcases le_total p m with h | h
  · exact hl hδ ⟨hp.1, h⟩
  · exact hr hδ ⟨h, hp.2⟩

end
end Candidate.SilPrior.FourthPower.ReturnBernstein
