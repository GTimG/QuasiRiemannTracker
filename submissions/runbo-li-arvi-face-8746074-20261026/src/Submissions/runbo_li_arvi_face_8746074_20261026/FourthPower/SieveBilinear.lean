/- Copyright (c) 2026 Sil. Apache-2.0.
Keep the repeated-prime parameter in a block of columns and the opposite
parameter in the frequency rows. This permits one common coefficient vector
when applying the baseline's arbitrary-matrix coprime bilinear theorem. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveUncoupling
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveRanges

set_option autoImplicit false
namespace Candidate.FourthPower.SieveBilinear
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths FiniteSieveOperator
open SexticSieve SieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O

section Blocks
variable {U V K R T : Type*} [Fintype U] [Fintype V] [Fintype K] [Fintype R] [Fintype T]

def leftBlock (A : Matrix (V × K) R ℂ) : Matrix (U × V × K) (U × R) ℂ :=
  fun x y => if y.1 = x.1 then A x.2 y.2 else 0

def rightBlock (B : Matrix (U × K) T ℂ) : Matrix (U × V × K) (V × T) ℂ :=
  fun x y => if y.1 = x.2.1 then B (x.1,x.2.2) y.2 else 0

omit [Fintype V] [Fintype K] in
theorem leftBlock_apply (A : Matrix (V × K) R ℂ) (a : U × R → ℂ) (u : U) (v : V) (k : K) :
    (∑ y, leftBlock A (u,v,k) y * a y) = ∑ r, A (v,k) r * a (u,r) := by
  simp only [leftBlock, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype U] [Fintype K] in
theorem rightBlock_apply (B : Matrix (U × K) T ℂ) (b : V × T → ℂ) (u : U) (v : V) (k : K) :
    (∑ y, rightBlock B (u,v,k) y * b y) = ∑ t, B (u,k) t * b (v,t) := by
  simp only [rightBlock, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem leftBlock_norm (A : Matrix (V × K) R ℂ) :
    ‖operator (leftBlock (U := U) A)‖^2 ≤ ‖operator A‖^2 := by
  apply squared_norm_le_of_energy _ _ (sq_nonneg _)
  intro a
  have he (x : U × V × K) : (∑ y, leftBlock A x y * a y) = ∑ r, A x.2 r * a (x.1,r) :=
    leftBlock_apply A a x.1 x.2.1 x.2.2
  simp_rw [he]
  have h (u : U) := CubicSieve.energy_le_squaredNorm A (fun r => a (u,r))
  simpa only [CubicSieve.squaredNorm, CubicSieve.operator, FiniteSieveOperator.operator,
    Fintype.sum_prod_type, Finset.mul_sum] using
    Finset.sum_le_sum (fun u _ => h u)

theorem rightBlock_norm (B : Matrix (U × K) T ℂ) :
    ‖operator (rightBlock (V := V) B)‖^2 ≤ ‖operator B‖^2 := by
  apply squared_norm_le_of_energy _ _ (sq_nonneg _)
  intro b
  have he (x : U × V × K) : (∑ y, rightBlock B x y * b y) = ∑ t, B (x.1,x.2.2) t * b (x.2.1,t) :=
    rightBlock_apply B b x.1 x.2.1 x.2.2
  simp_rw [he]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h (v : V) := CubicSieve.energy_le_squaredNorm B (fun t => b (v,t))
  simpa only [CubicSieve.squaredNorm, CubicSieve.operator, FiniteSieveOperator.operator,
    Fintype.sum_prod_type, Finset.mul_sum] using
    Finset.sum_le_sum (fun v _ => h v)

/-- No loss equal to the number of U or V parameters: they are retained
inside the operator, not estimated separately before summing. -/
theorem coherent_coprime (ε : ℝ) (hε : 0 < ε)
    (rs : R → Id) (ts : T → Id) (hr0 : ∀ r, rs r ≠ 0) (ht0 : ∀ t, ts t ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hrN : ∀ r, (Ideal.absNorm (rs r) : ℝ) ≤ N₁)
    (htN : ∀ t, (Ideal.absNorm (ts t) : ℝ) ≤ N₂)
    (A : Matrix (V × K) R ℂ) (B : Matrix (U × K) T ℂ)
    (a : U × R → ℂ) (b : V × T → ℂ) :
    (∑ u, ∑ v, ∑ k, ‖∑ r, ∑ t, if IsCoprime (rs r) (ts t) then
      star (A (v,k) r * a (u,r)) * (B (u,k) t * b (v,t)) else 0‖)^2 ≤
      (‖operator A‖^2 * (IdealCoprimeSieveOperator.supportConstant ε hε * N₁^ε) * ∑ y, ‖a y‖^2) *
      (‖operator B‖^2 * (IdealCoprimeSieveOperator.supportConstant ε hε * N₂^ε) * ∑ y, ‖b y‖^2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε
    (fun y : U × R => rs y.2) (fun y : V × T => ts y.2)
    (fun y => hr0 y.2) (fun y => ht0 y.2) N₁ N₂ hN₁ hN₂
    (fun y => hrN y.2) (fun y => htN y.2) (leftBlock A) (rightBlock B) a b
  have hid (x : U × V × K) :
      (∑ y : U × R, ∑ z : V × T, if IsCoprime (rs y.2) (ts z.2) then
        star (leftBlock A x y * a y) * (rightBlock B x z * b z) else 0) =
      ∑ r, ∑ t, if IsCoprime (rs r) (ts t) then
        star (A x.2 r * a (x.1,r)) * (B (x.1,x.2.2) t * b (x.2.1,t)) else 0 := by
    obtain ⟨u,v,k⟩ := x
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
    · apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
      · simp only [leftBlock, rightBlock, ite_true]
      · intro v' _ hv
        simp [rightBlock, hv]
      · simp
    · intro u' _ hu
      simp [leftBlock, hu]
    · simp
  simp_rw [hid] at hb
  simp only [Fintype.sum_prod_type] at hb ⊢
  apply hb.trans
  have hl : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N₁^ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN₁ _)
  have hr : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N₂^ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN₂ _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (leftBlock_norm A) hl)
      (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (rightBlock_norm B) hr)
      (by positivity)
  · positivity
  · positivity

end Blocks

def frequencyMatrix (Ds Ks columns : Finset Id) : Matrix (↥Ds × ↥Ks) ↥columns ℂ :=
  fun x I => rowValue (x.1.val*x.2.val) I.val

theorem frequency_operator_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ds Ks Qs columns : Finset Id) (L : ℝ), 0 ≤ L →
      (∀ D ∈ Ds, ∀ K ∈ Ks, D*K ∈ Qs) →
      (∀ Q ∈ Qs, Q ≠ 0 ∧ (Ideal.absNorm Q : ℝ) ≤ L) →
      ‖operator (frequencyMatrix Ds Ks columns)‖^2 ≤ C*L^ε*squaredNorm Qs columns := by
  obtain ⟨C,hC,hbound⟩ := SieveUncoupling.product_energy_bound ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks Qs columns L hL hmap hQs
  apply squared_norm_le_of_energy _ _ (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hL _)) (sq_nonneg _))
  intro a
  let aext : Id → ℂ := fun I => if hI : I ∈ columns then a ⟨I,hI⟩ else 0
  have hb := hbound Ds Ks Qs columns L hL hmap hQs aext
  have hi (D K : Id) : (∑ I ∈ columns, aext I * rowValue (D*K) I) =
      ∑ I : columns, rowValue (D*K) I.val * a I := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro I _
    simp only [aext, dite_eq_left I.property, mul_comm]
  have hm : coefficientMass columns aext = ∑ I : columns, ‖a I‖^2 := by
    rw [coefficientMass, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro I _
    simp only [aext, dite_eq_left I.property]
  simp_rw [hi] at hb
  rw [hm, ← Finset.sum_coe_sort] at hb
  have hk : ∀ D : Ds,
      (∑ K ∈ Ks, ‖∑ I : columns, rowValue (D.val*K) I.val * a I‖^2) =
      ∑ K : Ks, ‖∑ I : columns, rowValue (D.val*K.val) I.val * a I‖^2 := by
    intro D
    exact (Finset.sum_coe_sort Ks _).symm
  simp_rw [hk] at hb
  simpa only [frequencyMatrix, Fintype.sum_prod_type, SieveOperator.squaredNorm] using hb

theorem frequency_lambda_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ds Ks columns : Finset Id) (L N : ℝ), 0 ≤ L →
      (∀ D ∈ Ds, ∀ K ∈ Ks, CanonicalQuadraticSieve.Supported (D*K) ∧ (Ideal.absNorm (D*K) : ℝ) ≤ L) →
      (∀ I ∈ columns, CanonicalQuadraticSieve.Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ‖operator (frequencyMatrix Ds Ks columns)‖^2 ≤ C*L^ε*SieveRanges.lambda L N := by
  obtain ⟨C,hC,hbound⟩ := frequency_operator_bound ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks columns L N hL hmap hc
  have h := hbound Ds Ks (SieveRanges.fullRange L) columns L hL
    (fun D hD K hK => SieveRanges.mem_fullRange.mpr (hmap D hD K hK))
    (fun Q hQ => ⟨(SieveRanges.mem_fullRange.mp hQ).1.1,(SieveRanges.mem_fullRange.mp hQ).2⟩)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg hL _))
  exact SieveRanges.norm_mono (Finset.Subset.refl _)
    (fun I hI => SieveRanges.mem_freeRange.mpr (hc I hI))

/-- The two repeated-prime ranges enter only through the enlarged frequency
lengths. All coefficients are retained in the column blocks. -/
theorem coherent_frequency_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Us Vs Ks Rs Ts : Finset Id) (L₁ L₂ N₁ N₂ : ℝ),
      0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ N₁ → 0 ≤ N₂ →
      (∀ V ∈ Vs, ∀ K ∈ Ks, CanonicalQuadraticSieve.Supported (V*K) ∧ (Ideal.absNorm (V*K) : ℝ) ≤ L₁) →
      (∀ U ∈ Us, ∀ K ∈ Ks, CanonicalQuadraticSieve.Supported (U*K) ∧ (Ideal.absNorm (U*K) : ℝ) ≤ L₂) →
      (∀ R ∈ Rs, CanonicalQuadraticSieve.Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ N₁) →
      (∀ T ∈ Ts, CanonicalQuadraticSieve.Supported T ∧ PowerFree 6 T ∧ (Ideal.absNorm T : ℝ) ≤ N₂) →
      ∀ (a : ↥Us × ↥Rs → ℂ) (b : ↥Vs × ↥Ts → ℂ),
      (∑ u : Us, ∑ v : Vs, ∑ k : Ks, ‖∑ r : Rs, ∑ t : Ts,
        if IsCoprime r.val t.val then
          star (rowValue (v.val*k.val) r.val * a (u,r)) *
            (rowValue (u.val*k.val) t.val * b (v,t)) else 0‖)^2 ≤
        (C*L₁^ε*SieveRanges.lambda L₁ N₁ *
          (IdealCoprimeSieveOperator.supportConstant ε hε*N₁^ε) * ∑ y, ‖a y‖^2) *
        (C*L₂^ε*SieveRanges.lambda L₂ N₂ *
          (IdealCoprimeSieveOperator.supportConstant ε hε*N₂^ε) * ∑ y, ‖b y‖^2) := by
  obtain ⟨C,hC,hf⟩ := frequency_lambda_bound ε hε
  refine ⟨C,hC,?_⟩
  intro Us Vs Ks Rs Ts L₁ L₂ N₁ N₂ hL₁ hL₂ hN₁ hN₂ hV hU hR hT a b
  have hl := hf Vs Ks Rs L₁ N₁ hL₁ hV hR
  have hr := hf Us Ks Ts L₂ N₂ hL₂ hU hT
  have hb := coherent_coprime ε hε (fun r : Rs => r.val) (fun t : Ts => t.val)
    (fun r => (hR r.val r.property).1.1) (fun t => (hT t.val t.property).1.1)
    N₁ N₂ hN₁ hN₂ (fun r => (hR r.val r.property).2.2)
    (fun t => (hT t.val t.property).2.2)
    (frequencyMatrix Vs Ks Rs) (frequencyMatrix Us Ks Ts) a b
  apply hb.trans
  have hc₁ : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε*N₁^ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN₁ _)
  have hc₂ : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε*N₂^ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN₂ _)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hc₁) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hc₂) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hL₁ _))
      (SieveRanges.lambda_nonneg _ _)) hc₁) (by positivity)

open SieveUncoupling CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion

/-- Exact reduction of the actual cross kernel on fixed residue classes,
including the coprimality restriction. -/
theorem cross_coprime_identity (U V K : Id) (Rs Ts : Finset Id)
    (r₀ t₀ : EisensteinEPrimaryPhase.Coord) (hU : Supported U) (hV : Supported V)
    (hR : ∀ R ∈ Rs, Supported R ∧ ray R = r₀)
    (hT : ∀ T ∈ Ts, Supported T ∧ ray T = t₀) (a : Rs → ℂ) (b : Ts → ℂ) :
    (∑ r : Rs, ∑ t : Ts, if IsCoprime r.val t.val then
      star (a r)*b t*crossKernel U V r.val t.val K else 0) =
      crossPhase U V r₀ t₀ * star (rowValue K U) * rowValue K V *
        (∑ r : Rs, ∑ t : Ts, if IsCoprime r.val t.val then
          star (rowValue (V*K) r.val * a r) * (rowValue (U*K) t.val * b t) else 0) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hc : IsCoprime r.val t.val
  · simp only [ite_eq_left hc]
    rw [cross_factor U V r.val t.val K hU hV (hR r.val r.property).1 (hT t.val t.property).1,
      (hR r.val r.property).2, (hT t.val t.property).2]
    simp only [star_mul, mul_comm K V, mul_comm K U]
    ring
  · simp only [ite_eq_right hc, mul_zero]

theorem cross_coprime_norm (U V K : Id) (Rs Ts : Finset Id)
    (r₀ t₀ : EisensteinEPrimaryPhase.Coord) (hU : Supported U) (hV : Supported V)
    (hR : ∀ R ∈ Rs, Supported R ∧ ray R = r₀)
    (hT : ∀ T ∈ Ts, Supported T ∧ ray T = t₀) (a : Rs → ℂ) (b : Ts → ℂ) :
    ‖∑ r : Rs, ∑ t : Ts, if IsCoprime r.val t.val then
      star (a r)*b t*crossKernel U V r.val t.val K else 0‖ ≤
        ‖∑ r : Rs, ∑ t : Ts, if IsCoprime r.val t.val then
          star (rowValue (V*K) r.val * a r) * (rowValue (U*K) t.val * b t) else 0‖ := by
  rw [cross_coprime_identity U V K Rs Ts r₀ t₀ hU hV hR hT a b, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simp only [norm_mul, norm_star]
  have hp := crossPhase_norm U V r₀ t₀
  have hu : ‖rowValue K U‖ ≤ 1 := idealRowHom_norm _ _
  have hv : ‖rowValue K V‖ ≤ 1 := idealRowHom_norm _ _
  exact (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) hp) (norm_nonneg _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hu).trans hv)

end
end Candidate.FourthPower.SieveBilinear
