/- Copyright (c) 2026 Sil. Apache-2.0.
A concrete finite good-prime enclosure and exact ordinary row identities,
including unchanged frequency profiles under the restoration extraction.
-/
import Candidate.Feedback.FourthPower.ReferenceCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.ReferencePrimeEnclosure
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowExpansion KernelRowProfiles KernelRowPools ReferenceCoefficients
local notation "Id" => Ideal HeckeFamily.O

def primePool (X : ℝ) : Finset Id := (idealBall X).filter (fun I => Prime I ∧ Supported I)

def enclosure (X : ℝ) : Finset PrimeIdeal :=
  (primePool X).attach.image (fun I => ⟨I.val,(Finset.mem_filter.mp I.property).2.1⟩)

theorem enclosure_values (X : ℝ) : primeValues (enclosure X) = primePool X := by
  ext I
  simp [primeValues,enclosure]
  intro hI
  exact (Finset.mem_filter.mp hI).2.1

theorem enclosure_bound (X : ℝ) (P : PrimeIdeal) (hP : P ∈ enclosure X) :
    Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X := by
  have hp : P.val ∈ primePool X := by
    rw [← enclosure_values]
    exact Finset.mem_image.mpr ⟨P,hP,rfl⟩
  exact ⟨(Finset.mem_filter.mp hp).2.2,
    ((mem_idealBall _ _).mp (Finset.mem_filter.mp hp).1).2⟩

theorem supported_divisor {I J : Id} (hI : Supported I) (hJ : J ∣ I) : Supported J := by
  obtain ⟨K,rfl⟩ := hJ
  exact (supported_mul_iff J K).mp hI |>.1

theorem support_enclosed (X : ℝ) (I : Id) (hI : Supported I)
    (hcap : (Ideal.absNorm I : ℝ) ≤ X) : primeSupport I ⊆ primeValues (enclosure X) := by
  rw [enclosure_values]
  intro P hP
  have hp : Prime P := primeSupport_prime hP
  have hd : P ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  apply Finset.mem_filter.mpr
  exact ⟨(mem_idealBall _ _).mpr ⟨hp.ne_zero,(CenteredExceptionalCount.norm_le_of_dvd hI.1 hd).trans hcap⟩,
    hp,supported_divisor hI hd⟩

theorem enclosed_row (χ : Character) (S : Finset PrimeIdeal) (b X₁ X₂ : ℝ)
    (W₁ W₂ : ℝ → ℂ) (r : Id × Id → ℂ)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    normalizedRow χ (supportedRectangle S b X₁ X₂) r W₁ W₂ X₁ X₂ =
      normalizedRow χ (rectangle b X₁ X₂) r W₁ W₂ X₁ X₂ := by
  unfold normalizedRow supportedRectangle
  congr 1
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hn' : ¬pairSupport n.1 n.2 ⊆ primeValues S :=
    fun hs => hnot (Finset.mem_filter.mpr ⟨hn,hs⟩)
  have hbad : ¬Supported (n.1*n.2) := by
    intro hgood
    have hparts := (supported_mul_iff _ _).mp hgood
    have hmem := Finset.mem_product.mp hn
    apply hn'
    exact Finset.union_subset
      (henclose n.1 hparts.1 (Or.inl ((mem_idealBall _ _).mp hmem.1).2))
      (henclose n.2 hparts.2 (Or.inr ((mem_idealBall _ _).mp hmem.2).2))
  simp only [pairCharacter,hχ _ hbad,mul_zero,zero_mul]

theorem actual_enclosed_row (χ : Character) (Y b X₁ X₂ : ℝ)
    (W₁ W₂ : ℝ → ℂ) (r : Id × Id → ℂ)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (h₁ : b*X₁ ≤ Y) (h₂ : b*X₂ ≤ Y) :
    normalizedRow χ (supportedRectangle (enclosure Y) b X₁ X₂) r W₁ W₂ X₁ X₂ =
      normalizedRow χ (rectangle b X₁ X₂) r W₁ W₂ X₁ X₂ := by
  apply enclosed_row χ _ b X₁ X₂ W₁ W₂ r hχ
  intro I hI hlen
  exact support_enclosed Y I hI (hlen.elim (fun h => h.trans h₁) (fun h => h.trans h₂))

def phaseProfile (W : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ :=
  W x*FourierBridge.logPhase t (Real.log x)

theorem phaseProfile_support (W : ℝ → ℂ) (t : ℝ) :
    Function.support (phaseProfile W t) ⊆ Function.support W := by
  intro x hx hw
  apply hx
  simp [phaseProfile,hw]

/-- No smoothness statement about the phase-modified profile is needed for
this exact identity. Analytic constants always refer to the original W. -/
theorem phase_polynomial (χ : Character) (W : ℝ → ℂ) (b X t : ℝ)
    (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    HeckeDyadic.polynomial χ false (phaseProfile W t) X 0 0 =
      HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t) := by
  rw [natural_polynomial_finite χ (phaseProfile W t) b X hX ((phaseProfile_support W t).trans hs),
    phase_polynomial_finite χ W X t hX (idealBall (b*X))
      (fun I hI => ((mem_idealBall _ _).mp hI).1)
      (fun I hI hw => (mem_idealBall _ _).mpr ⟨hI,(div_le_iff₀ hX).mp (hs hw)⟩)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  unfold phaseProfile phaseCoefficient
  ring

theorem enclosed_phase_pair (χ : Character) (S : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ t₁ t₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1)
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂ =
      HeckeDyadic.polynomial χ false W₁ X₁ 0 (2*Real.pi*t₁)*
        HeckeDyadic.polynomial χ false W₂ X₂ 0 (2*Real.pi*t₂) := by
  rw [enclosed_row χ S b X₁ X₂ _ _ _ hχ henclose,
    natural_pair_row χ _ _ b X₁ X₂ hX₁ hX₂
      ((phaseProfile_support W₁ t₁).trans hW₁) ((phaseProfile_support W₂ t₂).trans hW₂),
    phase_polynomial χ W₁ b X₁ t₁ hX₁ hW₁,phase_polynomial χ W₂ b X₂ t₂ hX₂ hW₂]

end
end Candidate.Feedback.FourthPower.ReferencePrimeEnclosure
