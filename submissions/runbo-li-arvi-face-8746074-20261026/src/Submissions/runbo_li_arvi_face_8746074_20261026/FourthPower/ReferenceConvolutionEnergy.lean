/- Copyright (c) 2026 Sil. Apache-2.0.
The actual common tuple convolution in the proved central sextic reference.
No divisor-count, optimal-sieve or row-family energy hypothesis remains.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceConvolution
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveReferenceScales

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceConvolutionEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss
open SieveReference SieveElementReference SieveCentralReference SieveReferenceScales
open ReferenceConvolution
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem central_convolution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N B : ℝ), 1 ≤ M → 1 ≤ N → 0 ≤ B →
      ∀ (rows : Finset O) (S : Finset (α → Id)) (β : (α → Id) → ℂ),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M) →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      (∑ x ∈ rows, ‖∑ v ∈ S, β v*idealRowHom x (product v)‖^2) ≤
        C*(M*N)^ε*referenceMajorant M N*B^2 := by
  obtain ⟨C₁,hC₁,hb₁⟩ := central_envelope (α:=α) (ε/2) (by positivity)
  obtain ⟨C₂,hC₂,hb₂⟩ := central_reference (ε/2) (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  intro M N B hM hN hB rows S β hr hs hβ
  have hgeom : ∀ I ∈ columns S, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N := by
    intro I hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    exact hs v hv
  have hh := hb₂ M N (C₁*N^(ε/2)*B^2) hM hN (by positivity)
    rows (columns S) hr hgeom (coefficient S β)
    (hb₁ S β N B hN hB (fun v hv => ⟨(hs v hv).1.1,(hs v hv).2⟩) hβ)
  have hp : (M*N)^(ε/2)*N^(ε/2) ≤ (M*N)^ε := by
    apply (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans hN)
        (le_mul_of_one_le_left (zero_le_one.trans hN) hM) (by positivity : 0 ≤ ε/2))
      (by positivity : 0 ≤ (M*N)^(ε/2))).trans_eq
    rw [← Real.rpow_add (mul_pos (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hN))]
    congr 1
    ring
  simp_rw [row_identity S β]
  calc
    _ ≤ C₂*(M*N)^(ε/2)*referenceMajorant M N*(C₁*N^(ε/2)*B^2) := hh
    _ = (C₂*C₁)*((M*N)^(ε/2)*N^(ε/2))*referenceMajorant M N*B^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (mul_pos hC₂ hC₁).le)
        (referenceMajorant_nonneg M N (zero_le_one.trans hM) (zero_le_one.trans hN))) (sq_nonneg B)

theorem two_scale_convolution (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T B : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T → 0 ≤ B →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (rows : Finset O) (S : Finset (α → Id)) (β : (α → Id) → ℂ),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ u ∈ S, Supported (product u) ∧ (Ideal.absNorm (product u) : ℝ) ≤ N) →
      (∀ u ∈ S, ‖β u‖ ≤ B/Real.sqrt (Ideal.absNorm (product u) : ℝ)) →
      (∑ x ∈ rows, ‖∑ u ∈ S, β u*idealRowHom x (product u)‖^2) ≤
        C*Z^(R+ε)*(3+T^(1/3 : ℝ))*B^2 := by
  obtain ⟨C,hC,hb⟩ := central_convolution (α:=α) (ε/L) (div_pos hε hL)
  refine ⟨C,hC,?_⟩
  intro Z R v y N T B hZ hR hN hT hB hcap hv hy hmax href rows S β hr hs hβ
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hM : 0 < Z^R := Real.rpow_pos_of_pos hZ0 R
  have hp : ((Z^R)*N)^(ε/L) ≤ Z^ε := by
    calc
      _ ≤ ((Z^R)*(Z^v))^(ε/L) := Real.rpow_le_rpow (mul_nonneg hM.le hN0.le)
        (mul_le_mul_of_nonneg_left hmax hM.le) (div_pos hε hL).le
      _ = Z^((R+v)*(ε/L)) := by rw [← Real.rpow_add hZ0,← Real.rpow_mul hZ0.le]
      _ ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ
        ((mul_le_mul_of_nonneg_right hcap (div_pos hε hL).le).trans_eq (mul_div_cancel₀ ε hL.ne'))
  have hm := two_scale_majorant Z R v y N T hZ hR hN0.le hT hv hy hmax href
  have he := hb (Z^R) N B (Real.one_le_rpow hZ hR) hN hB rows S β hr hs hβ
  calc
    _ ≤ C*((Z^R)*N)^(ε/L)*referenceMajorant (Z^R) N*B^2 := he
    _ ≤ C*Z^ε*(Z^R*(3+T^(1/3 : ℝ)))*B^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hm
        (referenceMajorant_nonneg (Z^R) N hM.le hN0.le) (by positivity)) (sq_nonneg B)
    _ = _ := by rw [Real.rpow_add hZ0]; ring

end
end Candidate.FourthPower.ReferenceConvolutionEnergy
