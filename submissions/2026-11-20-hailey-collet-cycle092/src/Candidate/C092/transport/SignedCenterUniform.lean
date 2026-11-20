/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterFinal

/-! Uniform polynomial height/conductor dependence for the genuine corrected
fixed-row coefficient convolution. The original source identity is kept as a
separate arithmetic obligation, not an analytic premise of this theorem.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

def OrdinaryProfile.atHeight (P : OrdinaryProfile) (t : ℝ) : OrdinaryProfile := {P with t:=t}

/-- The finite derivative degree controls both independent normalized heights. -/
theorem pairK_uniform_degree (P₁ P₂ : OrdinaryProfile) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ,∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ (R₁ R₂ : OrdinaryRow),R₁.Q=Q₁ → R₂.Q=Q₂ →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm R₁.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm R₂.χ.modulus : ℝ) ≤ U^B → ∀ t₁ t₂ : ℝ,
      pairK R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) ≤
        C*U^ε*(1+‖t₁‖+‖t₂‖)^J := by
  obtain ⟨n₁,hn₁⟩ := CenteredMomentNaturalFixedRaySource.volumeControl_uniform_degree
    P₁.a P₁.b ε B P₁.ha hε hB
  obtain ⟨n₂,hn₂⟩ := CenteredMomentNaturalFixedRaySource.volumeControl_uniform_degree
    P₂.a P₂.b ε B P₂.ha hε hB
  refine ⟨max n₁ n₂,?_⟩
  intro Q₁ Q₂
  obtain ⟨D₁,hD₁,h₁⟩ := hn₁ Q₁ P₁.W P₁.hs P₁.hW
  obtain ⟨D₂,hD₂,h₂⟩ := hn₂ Q₂ P₂.W P₂.hs P₂.hW
  let V := pairC P₁ P₂
  have hV : 0 ≤ V := pairC_nonneg P₁ P₂
  let C := 1+2*V^2+4*(D₁+D₂)*V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro R₁ R₂ hQ₁ hQ₂ U hU hnorm₁ hnorm₂ t₁ t₂
  let H := 1+‖t₁‖+‖t₂‖
  let S := U^ε*H^max n₁ n₂
  have hH : 1 ≤ H := by dsimp only [H]; linarith [norm_nonneg t₁,norm_nonneg t₂]
  have hz : 0 ≤ U^ε := Real.rpow_nonneg (zero_le_one.trans hU) _
  have hS : 1 ≤ S := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hU hε.le) (one_le_pow₀ hH)
  have hp₁ : (1+‖t₁‖)^n₁ ≤ H^max n₁ n₂ := by
    calc
      _ ≤ H^n₁ := by gcongr; dsimp only [H]; linarith [norm_nonneg t₂]
      _ ≤ _ := pow_le_pow_right₀ hH (le_max_left _ _)
  have hp₂ : (1+‖t₂‖)^n₂ ≤ H^max n₁ n₂ := by
    calc
      _ ≤ H^n₂ := by gcongr; dsimp only [H]; linarith [norm_nonneg t₁]
      _ ≤ _ := pow_le_pow_right₀ hH (le_max_right _ _)
  have he₁ := (h₁ U hU R₁.χ hnorm₁ t₁).trans
    (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hD₁.le hz))
  have he₂ := (h₂ U hU R₂.χ hnorm₂ t₂).trans
    (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hD₂.le hz))
  have hE : pairE R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) ≤ (D₁+D₂)*S := by
    change volumeControl R₁.Q R₁.χ (normPowerProfile P₁.W P₁.a P₁.b P₁.ha P₁.hs P₁.hW t₁)+
      volumeControl R₂.Q R₂.χ (normPowerProfile P₂.W P₂.a P₂.b P₂.ha P₂.hs P₂.hW t₂) ≤ _
    rw [hQ₁,hQ₂]
    dsimp only [S]
    nlinarith
  have hbase : 2*V^2 ≤ 2*V^2*S := by nlinarith [mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 2*V^2)]
  have hmul := mul_le_mul_of_nonneg_right hE (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hV)
  change 2*V^2+4*pairE R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂)*V ≤ C*U^ε*H^max n₁ n₂
  rw [mul_assoc C (U^ε) (H^max n₁ n₂)]
  change 2*V^2+4*pairE R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂)*V ≤ C*S
  dsimp only [C]
  nlinarith

/-- Polynomial radical caps turn the actual cleared mask mass into U^ε. -/
theorem correctedMass_capped (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ,0 < C ∧ ∀ (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
      (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) ≤ U^B →
      correctedMass χ₁ χ₂ ψ₁ ψ₂ bad allowed ≤ C*U^ε := by
  let δ := ε/(B+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨C,hC,hbound⟩ := correctedMass_subpower δ hδ
  refine ⟨C,hC,?_⟩
  intro χ₁ χ₂ ψ₁ ψ₂ bad allowed hallowed U hU hcap
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have he : B*δ ≤ ε := by
    have hd : δ*(B+1)=ε := by dsimp only [δ]; field_simp
    nlinarith
  exact (hbound χ₁ χ₂ ψ₁ ψ₂ bad allowed hallowed).trans
    ((mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow (Nat.cast_nonneg _) hcap hδ.le).trans
        (by rw [←Real.rpow_mul hUpos.le]; exact Real.rpow_le_rpow_of_exponent_le hU he)) hC.le))

/-- Full independent-height, polynomial-conductor H8 estimate for the explicit
corrected Euler convolution. Both original row identities and every actual
allowed exceptional mask are retained in its data. -/
theorem correctedConvolutionSource_uniform (P₁ P₂ : OrdinaryProfile) (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ,∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ (R₁ R₂ : OrdinaryRow),R₁.Q=Q₁ → R₂.Q=Q₂ →
      ∀ (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P ∈ bad,allowed P ⊆ residualPairs true true) →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm R₁.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm R₂.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) ≤ U^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*(correctedConvolutionSource R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) bad allowed X₁ X₂-
        correctedConvolutionSource R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) bad allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,hJ⟩ := pairK_uniform_degree P₁ P₂ (ε/2) B (by linarith) hB
  obtain ⟨D,hD,hmask⟩ := correctedMass_capped (ε/2) B (by linarith) hB
  refine ⟨J,?_⟩
  intro Q₁ Q₂
  obtain ⟨C,hC,hpair⟩ := hJ Q₁ Q₂
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro R₁ R₂ hQ₁ hQ₂ bad allowed hallowed U hU hnorm₁ hnorm₂ hrad
    t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hk := hpair R₁ R₂ hQ₁ hQ₂ U hU hnorm₁ hnorm₂ t₁ t₂
  have hm := hmask R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed hallowed U hU hrad
  have h := correctedConvolutionSource_signed_max R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂)
    bad allowed X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hmass : 0 ≤ correctedMass R₁.χ R₂.χ R₁.ψ R₂.ψ bad allowed :=
    tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hbound := mul_le_mul hk hm hmass (by positivity : 0 ≤ C*U^(ε/2)*(1+‖t₁‖+‖t₂‖)^J)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg T))
    (Real.rpow_nonneg (zero_le_one.trans (le_max_left 1 L)) (-(3/5 : ℝ)))
  apply h.trans (hscaled.trans_eq ?_)
  have he : U^(ε/2)*U^(ε/2)=U^ε := by
    rw [←Real.rpow_add (zero_lt_one.trans_le hU)]
    congr 1
    ring
  calc
    _ = C*D*(U^(ε/2)*U^(ε/2))*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by ring
    _ = _ := by rw [he]

end
end QRH.Cycle092.SignedCenter
