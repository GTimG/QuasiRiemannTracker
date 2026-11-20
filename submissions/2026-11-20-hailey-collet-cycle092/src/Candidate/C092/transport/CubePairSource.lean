/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairConvolution

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

lemma mem_ordinaryResidualPairs (R₁ R₂ : OrdinaryRow) (keep₁ keep₂ : PrimeIdeal → Bool)
    (P : PrimeIdeal) (q : ℕ×ℕ) :
    q ∈ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P ↔
      q.1+q.2 ≤ 2 ∧
      ((IsCoprime P.val R₁.χ.modulus ∧ keep₁ P=true) ∨ q.1=0) ∧
      ((IsCoprime P.val R₂.χ.modulus ∧ keep₂ P=true) ∨ q.2=0) := by
  simp only [ordinaryResidualPairs,residualPairs,Finset.mem_filter,Finset.mem_product,
    Finset.mem_range,ordinaryPrimeKeep,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega,by omega⟩,h⟩

/-- Literal coordinate deletions, including both presented modulus holes. The
same masks are kept in both scale arms. -/
def ordinaryPairHoles (R₁ R₂ : OrdinaryRow) (bad : Finset PrimeIdeal)
    (keep₁ keep₂ : PrimeIdeal → Bool) (I J : Ideal O) : Prop :=
  (∀ P ∈ bad,(IsCoprime P.val R₁.χ.modulus ∧ keep₁ P=true) ∨ ProbePhysical.primeValuations I P=0) ∧
  (∀ P ∈ bad,(IsCoprime P.val R₂.χ.modulus ∧ keep₂ P=true) ∨ ProbePhysical.primeValuations J P=0)

lemma pairAllowed_ordinaryResidualPairs (R₁ R₂ : OrdinaryRow) (bad : Finset PrimeIdeal)
    (keep₁ keep₂ : PrimeIdeal → Bool) (I J : Ideal O) :
    PairAllowed bad (ordinaryResidualPairs R₁ R₂ keep₁ keep₂) I J ↔
      PairCubeFree I J ∧ ordinaryPairHoles R₁ R₂ bad keep₁ keep₂ I J := by
  constructor
  · rintro ⟨hgood,hbad⟩
    refine ⟨fun P => ?_,⟨fun P hP => ?_,fun P hP => ?_⟩⟩
    · by_cases hP : P ∈ bad
      · exact ((mem_ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P _).mp (hbad P hP)).1
      · exact hgood P hP
    · exact ((mem_ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P _).mp (hbad P hP)).2.1
    · exact ((mem_ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P _).mp (hbad P hP)).2.2
  · rintro ⟨hc,h₁,h₂⟩
    refine ⟨fun P _ => hc P,fun P hP => ?_⟩
    exact (mem_ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P _).mpr ⟨hc P,h₁ P hP,h₂ P hP⟩

/-- The physical source written with cubefreeness and literal coordinate holes,
so the equality is visibly to a coupled source, not a factored replacement. -/
def ordinaryDeletedCubePairSource (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool) (x y : ℝ) : ℂ :=
  ∑' p : Ideal O×Ideal O,
    (if PairCubeFree p.1 p.2 ∧ ordinaryPairHoles R₁ R₂ bad keep₁ keep₂ p.1 p.2 then
      idealCoeff R₁.χ p.1*idealCoeff R₂.χ p.2 else 0)*
      P₁.normalized ((Ideal.absNorm p.1 : ℝ)/x)*P₂.normalized ((Ideal.absNorm p.2 : ℝ)/y)

lemma literalCubePairSource_eq_deleted (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool) (x y : ℝ) :
    literalCubePairSource R₁ R₂ P₁ P₂ bad (ordinaryResidualPairs R₁ R₂ keep₁ keep₂) x y=
      ordinaryDeletedCubePairSource R₁ R₂ P₁ P₂ bad keep₁ keep₂ x y := by
  apply tsum_congr
  intro p
  simp only [physicalPairTerm,literalCubePairCoefficient,pairAllowed_ordinaryResidualPairs]

theorem correctedConvolutionSource_eq_deleted (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
    (hgood₁ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus)
    (hgood₂ : ∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    correctedConvolutionSource R₁ R₂ P₁ P₂ bad (ordinaryResidualPairs R₁ R₂ keep₁ keep₂) x y=
      ordinaryDeletedCubePairSource R₁ R₂ P₁ P₂ bad keep₁ keep₂ x y := by
  rw [ordinaryRow_correctedConvolutionSource R₁ R₂ P₁ P₂ bad keep₁ keep₂ _ hgood₁ hgood₂
    (fun _ _ => Finset.Subset.refl _) x y hx hy,literalCubePairSource_eq_deleted]

/-- H8 for the actual coupled source with its full retained exceptional
valuation sets. The degree is chosen before the fixed rows and all independent
profile heights. The same coefficient/mask data occur in both signed arms. -/
theorem literalCubePairSource_uniform (P₁ P₂ : OrdinaryProfile) (ε B : ℝ)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ,∀ Q₁ Q₂ : Ideal O,∃ C : ℝ,0 < C ∧
      ∀ (R₁ R₂ : OrdinaryRow),R₁.Q=Q₁ → R₂.Q=Q₂ →
      ∀ (bad : Finset PrimeIdeal) (keep₁ keep₂ : PrimeIdeal → Bool)
        (allowed : PrimeIdeal → Finset (ℕ×ℕ)),
      (∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₁.χ.modulus) →
      (∀ P : PrimeIdeal,P ∉ bad → IsCoprime P.val R₂.χ.modulus) →
      (∀ P ∈ bad,allowed P ⊆ ordinaryResidualPairs R₁ R₂ keep₁ keep₂ P) →
      ∀ U : ℝ,1 ≤ U → (Ideal.absNorm R₁.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm R₂.χ.modulus : ℝ) ≤ U^B →
      (Ideal.absNorm (∏ P ∈ bad,P.val) : ℝ) ≤ U^B →
      ∀ t₁ t₂ X₁ X₂ Y₁ Y₂ T L : ℝ,0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T : ℂ)⁻¹*(literalCubePairSource R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) bad allowed X₁ X₂-
        literalCubePairSource R₁ R₂ (P₁.atHeight t₁) (P₂.atHeight t₂) bad allowed Y₁ Y₂)‖ ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*(max 1 L)^(-(3/5 : ℝ)) := by
  obtain ⟨J,hJ⟩ := correctedConvolutionSource_uniform P₁ P₂ ε B hε hB
  refine ⟨J,fun Q₁ Q₂ => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hJ Q₁ Q₂
  refine ⟨C,hC,?_⟩
  intro R₁ R₂ hQ₁ hQ₂ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    U hU hn₁ hn₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound R₁ R₂ hQ₁ hQ₂ bad allowed
    (fun P hP => (hallowed P hP).trans (ordinaryResidualPairs_subset R₁ R₂ keep₁ keep₂ P))
    U hU hn₁ hn₂ hrad t₁ t₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [ordinaryRow_correctedConvolutionSource R₁ R₂ _ _ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂),
    ordinaryRow_correctedConvolutionSource R₁ R₂ _ _ bad keep₁ keep₂ allowed hgood₁ hgood₂ hallowed
    Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂)] at h
  exact h

#print axioms correctedConvolutionSource_eq_deleted
#print axioms literalCubePairSource_uniform
end
end QRH.Cycle092.SignedCenter
