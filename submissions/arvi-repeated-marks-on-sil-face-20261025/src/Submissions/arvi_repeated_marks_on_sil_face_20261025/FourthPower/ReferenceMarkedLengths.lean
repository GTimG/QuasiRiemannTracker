/- Copyright (c) 2026 Sil. Apache-2.0.
The live annular length retains the entire frozen norm in its denominator.
Uniformity over all frozen label subsets is obtained by a finite maximum,
before any arithmetic or physical parameter is selected.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceNaturalMarkedFactor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.ReferenceMarkedLengths
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceNaturalMarkedFactor KernelPhysicalScalars
open KernelMarkedRows KernelAssignmentReindex
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

theorem frozenNorm_one_le (S : Finset PrimeIdeal) (T : Finset α) (t : T → S) :
    1 ≤ frozenNorm S t := by
  have h : (∏ i : T, (1:ℝ)) ≤ ∏ i : T, (Ideal.absNorm (t i).val.val : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
      (fun i _ => ideal_norm_one_le (t i).val.property.ne_zero)
  simpa only [frozenNorm,Finset.prod_const_one] using h

theorem live_length_bound (S : Finset PrimeIdeal) (T : Finset α) (P : α → ℝ)
    (t : T → S) (hP : ∀ i, 0 < P i)
    (ht : ∀ i : T, (Ideal.absNorm (t i).val.val : ℝ) ≤ 2*P i.val) :
    (∏ i : {i // i ∉ T}, 2*P i.val) ≤ (∏ i, 2*P i)/frozenNorm S t := by
  apply (le_div_iff₀ (frozenNorm_pos S t)).mpr
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ T) (fun i => (2:ℝ)*P i)]
  calc
    _ = frozenNorm S t*(∏ i : {i // i ∉ T}, 2*P i.val) := by ring
    _ ≤ (∏ i : T, 2*P i.val)*(∏ i : {i // i ∉ T}, 2*P i.val) :=
      mul_le_mul_of_nonneg_right
        (Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => ht i))
        (Finset.prod_nonneg (fun i _ => by have := hP i.val; positivity))
    _ = _ := by
      congr 1 <;> (apply Finset.prod_congr (by ext; simp); intro i hi; rfl)

theorem live_length_le_full (S : Finset PrimeIdeal) (T : Finset α) (P : α → ℝ)
    (t : T → S) (hP : ∀ i, 0 < P i)
    (ht : ∀ i : T, (Ideal.absNorm (t i).val.val : ℝ) ≤ 2*P i.val) :
    (∏ i : {i // i ∉ T}, 2*P i.val) ≤ ∏ i, 2*P i := by
  exact (live_length_bound S T P t hP ht).trans
    (div_le_self (Finset.prod_nonneg (fun i _ => by have := hP i; positivity))
      (frozenNorm_one_le S T t))

/-- The same outer constant works for every frozen subset, every actual
frozen assignment and every physical character. -/
theorem uniform_remaining_factor (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (T : Finset α) (S : Finset PrimeIdeal)
      (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (B : ℝ),
      1 ≤ B → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ t : T → S, ∃ F : Factor,
        F.length = ∏ i : {i // i ∉ T}, 2*P i.val ∧
        ((∀ i : T, (t i).val.val ∈ pool i.val) →
          F.length ≤ (∏ i, 2*P i)/frozenNorm S t ∧
          F.amplitude ≤ M*(max 1 (∏ i, 2*P i))^δ*(Real.sqrt 2*B)^Fintype.card α) ∧
        ∀ χ : Character,
          remainingSum T (naturalCoefficients χ S pool β P) t (fun _ => 1) = F.value χ := by
  choose C hC hfactor using fun T : Finset α => remaining_factor T δ hδ
  let M := 1+∑ T : Finset α, C T
  have hM : 0 < M := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) => (hC T).le)
    dsimp [M]
    linarith
  have hCM (T : Finset α) : C T ≤ M := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=C)
      (fun U _ => (hC U).le) (Finset.mem_univ T)
    dsimp [M]
    linarith
  refine ⟨M,hM,?_⟩
  intro T S pool β P B hB hP hp hβ t
  obtain ⟨F,hlen,hamp,hvalue⟩ := hfactor T S pool β P B (zero_le_one.trans hB) hP hp hβ t
  refine ⟨F,hlen,?_,hvalue⟩
  intro ht
  have hfrozen (i : T) : (Ideal.absNorm (t i).val.val : ℝ) ≤ 2*P i.val :=
    (hp i.val _ (ht i)).2
  have hlive := live_length_le_full S T P t hP hfrozen
  have hsqrt : 1 ≤ Real.sqrt 2 := by simpa using Real.sqrt_le_sqrt (by norm_num : (1:ℝ) ≤ 2)
  have hbase : 1 ≤ Real.sqrt 2*B := one_le_mul_of_one_le_of_one_le hsqrt hB
  have hp0 : 0 ≤ max 1 (∏ i : {i // i ∉ T}, 2*P i.val) := zero_le_one.trans (le_max_left _ _)
  constructor
  · rw [hlen]
    exact live_length_bound S T P t hP hfrozen
  · rw [hamp]
    apply mul_le_mul
    · exact mul_le_mul (hCM T) (Real.rpow_le_rpow hp0 (max_le_max_left _ hlive) hδ.le)
        (Real.rpow_nonneg hp0 _) hM.le
    · exact pow_le_pow_right₀ hbase (Fintype.card_subtype_le _)
    · positivity
    · positivity

end
end Candidate.FourthPower.ReferenceMarkedLengths
