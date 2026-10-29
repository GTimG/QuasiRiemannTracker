/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryProfiles

/-! Uniform inverse moments for the literal normalized original slots.
The fixed dictionary orientation and every moving sixth-root hole are
retained as bounded common coefficients, before the inverse theorem is used. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators ComplexConjugate
open Set OAI OAI.SevenEighths ConcreteTraceCRT
open HeckeFamily HeckeDyadic HeckeInverseAmplification CanonicalRowCompletion
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource CenteredMomentCommonMaskEnergy
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorDictionary Deletion26 DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

def maskedDirectCoefficient (η : Character) (m A root : O) (β : Ideal O → ℂ)
    (t : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff η I*idealRowHom (m^6*A*root^6) I*heightCoefficient β t I

/-- Exact conversion; arbitrary overlaps, all natural zeros and every root
prime stay in the common coefficient, rather than being removed by a bound. -/
theorem normalizedSlot_root_eq_direct (η : Character) (m A root u : O)
    (L : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) :
    normalizedSlot η m A (u*root^6) L β t P =
      directPrimeSlot u L (maskedDirectCoefficient η m A root β t) P := by
  unfold normalizedSlot rowSlot directPrimeSlot maskedDirectCoefficient heightCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have he : m^6*(A*(u*root^6)) = (m^6*A*root^6)*u := by ring
  rw [he,idealRowHom_argument_mul]
  ring

theorem maskedDirectCoefficient_norm (η : Character) (m A root : O)
    (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) (B : ℝ)
    (hβ : ‖heightCoefficient β t I‖ ≤ B) :
    ‖maskedDirectCoefficient η m A root β t I‖ ≤ B := by
  unfold maskedDirectCoefficient
  rw [norm_mul,norm_mul]
  have hb : ‖idealCoeff η I‖*‖idealRowHom (m^6*A*root^6) I‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η I) (idealRowHom_norm _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hβ

private theorem oriented_iterate (reverse : Bool) (W : ℝ → ℂ) (n : ℕ) :
    orientedProfile reverse ((logProfile^[n]) W) =
      (logProfile^[n]) (orientedProfile reverse W) := by
  rw [oriented_logTest,logTest_eq_iterate]

/-- The inverse raw moment is uniform in the ORIGINAL source slots and all
sixth-root masks. The mesh and root size do not enter the constant. Slot
modulus separation is kept explicit for the later tiny-slot exit. -/
theorem normalized_inverse_marked_energy (W : ℝ → ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : Continuous W)
    (hεm : 0 < εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ),
        (∀ i,0≤ell i) → (∀ i,∀ P∈L i,Prime P) →
        (∀ i,∀ P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Icc (1:ℝ) 2) →
        (∀ i,((deletedBase data).modulus.absNorm:ℝ)<U^(ell i)) →
      ∀ (η : Character) (m A root : O) (ν : ι → Character)
        (σslot vslot : ι → ℝ) (tslot : ℝ),
        (∀ i,lo≤σslot i) → (∀ i,σslot i≤hi) →
      ∀ r : ℝ,0≤r → r+2*(∑ i,ell i)<1 → 2*r+8*(∑ i,ell i)<3 →
      ∀ rows : Finset NonzeroElement, (∀ u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀ (χ : NonzeroElement → Character) (reverse : Bool),
        (∀ u∈rows,∀ I : Ideal O, idealCoeff (χ u) I =
          if reverse then conj (idealCoeff (data.character u) I) else idealCoeff (data.character u) I) →
      ∀ tstar : ℝ,∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,
      ∀ height freq : ℝ,0≤height → freq∈Icc (-height) height →
      (∑ u∈rows,‖polynomial (χ u) true
        ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ freq *
          (∏ i, normalizedSlot η m A (u.val*root^6) (L i)
            (fun I => idealCoeff (ν i) I*
              HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I)
            tslot (U^(ell i)))‖^2) ≤ (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨B,hB,hcoeff⟩ := annular_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW
  obtain ⟨degree,henergy⟩ := overlapping_inverse_marked_energy εm (max 1 B) hεm
    (le_max_left _ _) K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hp hratio hlarge η m A root ν σslot vslot tslot hσlo hσhi
    r hr hfirst hsecond rows hrows χ reverse hχ tstar n hn σ hσ height freq hh ht
  have hUp : 0<U := zero_lt_one.trans (hU₀.trans_le hU)
  let β := fun i I => idealCoeff (ν i) I*
    HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I
  let coeff := fun i => maskedDirectCoefficient η m A root (β i) tslot
  have hc (i : ι) (I : Ideal O) (hI : I∈L i) : ‖coeff i I‖≤max 1 B := by
    apply maskedDirectCoefficient_norm
    exact (hcoeff (ν i) (U^(ell i)) (σslot i) (vslot i) tslot
      (Real.rpow_pos_of_pos hUp _) (hσlo i) (hσhi i) I (hp i I hI).ne_zero).trans
      (le_max_right _ _)
  have hfreq : orientedFrequency reverse freq ∈ Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact abs_le.mpr ht
  have he := henergy U hU hK L ell coeff hell hp hratio hc hlarge
    r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height
    (orientedFrequency reverse freq) hh hfreq
  convert he using 1
  apply Finset.sum_congr rfl
  intro u hu
  simp only [norm_mul]
  rw [norm_of_oriented_coefficients (χ u) (data.character u) reverse (hχ u hu)
    true ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ freq
    (Real.rpow_pos_of_pos hUp _),oriented_iterate]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact normalizedSlot_root_eq_direct η m A root u.val (L j) (β j) tslot (U^(ell j))

end
end Qrh.JointDetector.RepeatedMarks
