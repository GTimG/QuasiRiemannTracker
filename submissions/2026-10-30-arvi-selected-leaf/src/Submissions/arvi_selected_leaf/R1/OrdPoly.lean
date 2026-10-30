/-
Ordinary polynomials (source set and coefficient vector) and their products.

An ordinary polynomial is `z ↦ ∑_{I ∈ S} c I · idealRowHom z I` (PR 93's `ordinaryPolynomial`). Products are
again ordinary polynomials on the product sources with the ideal convolution of the coefficients
(`ordinaryPolynomial_mul`); the coefficient mass of a product is at most the product of the masses times the
divisor factor `D_ε X^ε` per multiplication (`idealConvolution_mass_small_power`). The selected energy of an
ordinary polynomial is at most the selected norm times its mass (`ordinaryPolynomial_energy`).
-/
import Submissions.arvi_selected_leaf.JointDetector.FineDetectorWords

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion
open Qrh.JointDetector Qrh.JointDetector.FineDetectorWords
local notation "O" => ActualEisensteinCubic.O

/-- An ordinary polynomial: a finite source set with a coefficient vector. -/
structure OrdPoly where
  S : Finset (Ideal O)
  c : S → ℂ

namespace OrdPoly

/-- The value at a row. -/
def eval (p : OrdPoly) (z : O) : ℂ := ordinaryPolynomial p.S p.c z

/-- The coefficient mass. -/
def mass (p : OrdPoly) : ℝ := ∑ I, ‖p.c I‖^2

theorem mass_nonneg (p : OrdPoly) : 0 ≤ p.mass := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The product polynomial. -/
def mul (p q : OrdPoly) : OrdPoly :=
  ⟨idealProductSources p.S q.S, idealConvolution p.S q.S p.c q.c⟩

theorem eval_mul (p q : OrdPoly) (z : O) : (p.mul q).eval z = p.eval z * q.eval z :=
  (ordinaryPolynomial_mul p.S q.S p.c q.c z).symm

/-- The unit polynomial. -/
def one : OrdPoly := ⟨{1}, fun _ => 1⟩

theorem eval_one (z : O) : one.eval z = 1 := by
  show ∑ I : ({1} : Finset (Ideal O)), (1:ℂ) * idealRowHom z I.val = 1
  rw [Finset.sum_coe_sort ({1} : Finset (Ideal O)) (fun I => (1:ℂ) * idealRowHom z I),
    Finset.sum_singleton, one_mul, map_one]

theorem mass_one : one.mass = 1 := by
  show ∑ _I : ({1} : Finset (Ideal O)), ‖(1:ℂ)‖^2 = 1
  rw [Finset.sum_coe_sort ({1} : Finset (Ideal O)) (fun _ => ‖(1:ℂ)‖^2)]
  simp

/-- Every source is nonzero and of norm at most `X`. -/
def NormLe (p : OrdPoly) (X : ℝ) : Prop := ∀ I ∈ p.S, I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X

theorem normLe_one : one.NormLe 1 := by
  intro I hI
  have : I = 1 := Finset.mem_singleton.mp hI
  subst this
  exact ⟨by simp, by simp⟩

theorem normLe_mono {p : OrdPoly} {X Y : ℝ} (h : p.NormLe X) (hXY : X ≤ Y) : p.NormLe Y :=
  fun I hI => ⟨(h I hI).1, (h I hI).2.trans hXY⟩

theorem normLe_mul {p q : OrdPoly} {X Y : ℝ} (hp : p.NormLe X) (hq : q.NormLe Y) :
    (p.mul q).NormLe (X*Y) := by
  intro I hI
  obtain ⟨A, hA, B, hB, rfl⟩ := (mem_idealProductSources p.S q.S I).mp hI
  refine ⟨mul_ne_zero (hp A hA).1 (hq B hB).1, ?_⟩
  rw [map_mul, Nat.cast_mul]
  exact mul_le_mul (hp A hA).2 (hq B hB).2 (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans (hp A hA).2)

theorem mass_mul {p q : OrdPoly} {X : ℝ} (ε : ℝ) (hε : 0 < ε) (h : (p.mul q).NormLe X) :
    (p.mul q).mass ≤ idealDivisorConstant ε hε * X^ε * p.mass * q.mass :=
  idealConvolution_mass_small_power p.S q.S p.c q.c ε X hε (fun I hI => (h I hI).1)
    (fun I hI => (h I hI).2)

/-- **Selected energy of an ordinary polynomial.** -/
theorem energy_le (rows : Finset O) (p : OrdPoly) :
    ∑ z ∈ rows, ‖p.eval z‖^2 ≤ selectedNorm rows p.S * p.mass := by
  rw [← Finset.sum_coe_sort rows (fun z => ‖p.eval z‖^2)]
  exact ordinaryPolynomial_energy rows p.S p.c

/-- The product of a list. -/
def prod (l : List OrdPoly) : OrdPoly := l.foldr mul one

theorem eval_prod (l : List OrdPoly) (z : O) : (prod l).eval z = (l.map (fun p => p.eval z)).prod := by
  induction l with
  | nil => exact eval_one z
  | cons p l ih => simp only [prod, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢; rw [eval_mul, ih]

/-- Norms of a product list of bounded factors (factor, norm bound). -/
theorem normLe_prod (l : List (OrdPoly × ℝ)) (hX : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2) :
    (prod (l.map Prod.fst)).NormLe (l.map Prod.snd).prod := by
  induction l with
  | nil => exact normLe_one
  | cons q l ih =>
    simp only [prod, List.map_cons, List.foldr_cons, List.prod_cons]
    exact normLe_mul (hX q List.mem_cons_self).1 (ih (fun r hr => hX r (List.mem_cons_of_mem _ hr)))

theorem prod_bounds_ge_one (l : List (OrdPoly × ℝ)) (hX : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2) :
    1 ≤ (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 := (hX q List.mem_cons_self).2
    have h2 := ih (fun r hr => hX r (List.mem_cons_of_mem _ hr))
    nlinarith

/-- **Mass of a product list**: one divisor factor `D_ε Xtot^ε` per multiplication. -/
theorem mass_prod (ε : ℝ) (hε : 0 < ε) (l : List (OrdPoly × ℝ))
    (hX : ∀ q ∈ l, q.1.NormLe q.2 ∧ 1 ≤ q.2) (Xtot : ℝ) (htot : (l.map Prod.snd).prod ≤ Xtot) :
    (prod (l.map Prod.fst)).mass ≤
      (idealDivisorConstant ε hε * Xtot^ε)^l.length * (l.map (fun q => q.1.mass)).prod := by
  induction l with
  | nil => simp [prod, mass_one]
  | cons q l ih =>
    simp only [prod, List.map_cons, List.foldr_cons, List.prod_cons, List.length_cons] at htot ⊢
    have hq1 := (hX q List.mem_cons_self).2
    have hrest1 := prod_bounds_ge_one l (fun r hr => hX r (List.mem_cons_of_mem _ hr))
    have hrest : (l.map Prod.snd).prod ≤ Xtot := by nlinarith
    have hih := ih (fun r hr => hX r (List.mem_cons_of_mem _ hr)) hrest
    have hN : (q.1.mul (prod (l.map Prod.fst))).NormLe Xtot := normLe_mono
      (normLe_mul (hX q List.mem_cons_self).1
        (normLe_prod l (fun r hr => hX r (List.mem_cons_of_mem _ hr)))) htot
    have hm := mass_mul ε hε hN
    have hXt : 0 ≤ Xtot := le_trans (by linarith) hrest
    have hD : 0 ≤ idealDivisorConstant ε hε * Xtot^ε :=
      mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hXt _)
    have hpm := q.1.mass_nonneg
    calc (q.1.mul (prod (l.map Prod.fst))).mass
        ≤ idealDivisorConstant ε hε * Xtot^ε * q.1.mass * (prod (l.map Prod.fst)).mass := hm
      _ ≤ idealDivisorConstant ε hε * Xtot^ε * q.1.mass *
            ((idealDivisorConstant ε hε * Xtot^ε)^l.length * (l.map (fun q => q.1.mass)).prod) := by
          apply mul_le_mul_of_nonneg_left hih; positivity
      _ = (idealDivisorConstant ε hε * Xtot^ε)^(l.length+1) *
            (q.1.mass * (l.map (fun q => q.1.mass)).prod) := by ring

end OrdPoly

end
end QRH.ArviSelectedLeaf.R1
