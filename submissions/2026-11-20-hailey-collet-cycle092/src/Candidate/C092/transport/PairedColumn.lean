/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MergedColumn

namespace QRH.Cycle092.PairedColumn
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentAddedZero CenteredMomentSourceMass
open Qrh.JointDetector WholeWordAmplification SlotWordProducer
local notation "O" => ActualEisensteinCubic.O

theorem word_energy (rows : Finset O) {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (c : Fin r → Ideal O → ℂ) (C cap : Fin r → ℝ) (K X ε : ℝ)
    (hK : 0 ≤ K) (hX : 1 ≤ X) (hε : 0 < ε)
    (hnz : ∀ i, ∀ I ∈ pools i, I ≠ 0) (hn : ∀ i, ∀ I ∈ pools i, (I.absNorm:ℝ) ≤ cap i)
    (hcaps : ∏ i, cap i ≤ X) (hc : ∀ i, (∑ I ∈ pools i, ‖c i I‖^2) ≤ C i)
    (hsource : ∀ (S : Finset (Ideal O)) (a : S → ℂ), (∀ I ∈ S, (I.absNorm:ℝ) ≤ X) →
      ∑ z : rows, ‖FineDetectorWords.ordinaryPolynomial S a z.val‖^2 ≤ K * ∑ I, ‖a I‖^2) :
    (∑ z : rows, ‖∏ i, ∑ I ∈ pools i, c i I * idealRowHom z.val I‖^2) ≤
      K * ((wordDivisorConstant r ε hε * X^ε) * ∏ i, C i) := by
  have hp := MergedColumn.masked_word_energy rows pools c (fun _ => 1) C cap K X ε hK hX hε hnz hn hcaps hc (by simp) hsource
  simp only [one_mul] at hp
  have heq (z : O) : (∏ i, ∑ I ∈ pools i, c i I * idealRowHom z I) =
      ∑ v ∈ wordTuples pools, wordCoefficient c v * idealRowHom z (tupleProduct v) := by
    rw [Finset.prod_univ_sum]; apply Finset.sum_congr rfl; intro v hv
    simp only [wordCoefficient,tupleProduct,map_prod,Finset.prod_mul_distrib]
  simp_rw [heq]; exact hp

private def two {N : ℕ} {α : Type*} (a b : α) (f : Fin N → α) : Fin (N+2) → α :=
  Fin.cons a (Fin.cons b f)

private theorem prod_two {N : ℕ} {α : Type*} [CommMonoid α] (a b : α) (f : Fin N → α) :
    (∏ i, two a b f i) = a*(b*∏ i, f i) := by
  simp [two,Fin.prod_univ_succ]

/-- Two ordinary ideal variables and each marked slot are paid for together. -/
theorem paired_energy (rows : Finset O) {N : ℕ} (d : SelectedSlotData N) {Z mesh B : ℝ}
    (hd : d.Bounded Z mesh B) (S T : Finset (Ideal O)) (a b : Ideal O → ℂ)
    (A D P Q K X ε : ℝ) (hK : 0 ≤ K) (hX : 1 ≤ X) (hε : 0 < ε)
    (hs : ∀ I ∈ S, I ≠ 0) (ht : ∀ I ∈ T, I ≠ 0)
    (hp : ∀ I ∈ S, (I.absNorm:ℝ) ≤ P) (hq : ∀ I ∈ T, (I.absNorm:ℝ) ≤ Q)
    (hA : ∑ I ∈ S, ‖a I‖^2 ≤ A) (hD : ∑ I ∈ T, ‖b I‖^2 ≤ D)
    (hcap : P*(Q*∏ i, (2*Z^(d.width i))) ≤ X)
    (hsource : ∀ (S : Finset (Ideal O)) (a : S → ℂ), (∀ I ∈ S, (I.absNorm:ℝ) ≤ X) →
      ∑ z : rows, ‖FineDetectorWords.ordinaryPolynomial S a z.val‖^2 ≤ K * ∑ I, ‖a I‖^2) :
    (∑ z : rows, ‖(∑ I ∈ S, a I * idealRowHom z.val I)*
      ((∑ I ∈ T, b I * idealRowHom z.val I) * ∏ i, d.polynomial i z.val)‖^2) ≤
      K * ((wordDivisorConstant (N+2) ε hε * X^ε) * (A*(D*B^N))) := by
  let s := two S T d.sources; let c := two a b d.coefficient
  let cap := two P Q (fun i => 2*Z^(d.width i)); let mass := two A D (fun _ : Fin N => B)
  have hnz : ∀ i, ∀ I ∈ s i, I ≠ 0 := Fin.cases hs (Fin.cases ht hd.source_nonzero)
  have hn : ∀ i, ∀ I ∈ s i, (I.absNorm:ℝ) ≤ cap i := Fin.cases hp (Fin.cases hq hd.source_norm)
  have hm : ∀ i, (∑ I ∈ s i, ‖c i I‖^2) ≤ mass i := Fin.cases hA (Fin.cases hD hd.coefficient_mass)
  have h := word_energy rows s c mass cap K X ε hK hX hε hnz hn (by simpa only [cap,prod_two] using hcap) hm hsource
  have hprod (z : O) : (∏ i, ∑ I ∈ s i, c i I * idealRowHom z I) =
      (∑ I ∈ S, a I * idealRowHom z I)*((∑ I ∈ T, b I * idealRowHom z I) * ∏ i, d.polynomial i z) := by
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]; rfl
  simp_rw [hprod] at h; simpa only [mass,prod_two,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

#print axioms paired_energy
end
end QRH.Cycle092.PairedColumn
