/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete genuine short fourth on the original finite rows, including every
positive bounded scale. All constants precede the actual slot metadata,
ordinary profile, pitch, height and row set. -/
import Candidate.C092.transport.ReferenceShortP3Product

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceInputTailUniform CenteredMomentCommonRadialData
open QRH.Cycle092.OrdinaryColumn
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_ReferenceShortP3Fourth_a328bc2389a6d31a_001 {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

theorem short_fourth_source (ι : Type) [Fintype ι] [DecidableEq ι]
    (a b B ε ξ saving : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sd St : Finset (ℕ×ℕ), ∃ Cd Ct : ℝ, 0 < Cd ∧ 0 < Ct ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (η : Character) (t : ℝ) (pool : ι → Finset (Ideal O)) (ν : ι → Ideal O → ℂ)
      (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ),
    (∀ i, ∀ I∈pool i, Prime I) → (∀ i, 0 < P i) → (∀ i, 1 ≤ M i) →
    (∀ i I, ‖ν i I‖ ≤ 1) → (∀ i, Function.support (Wslot i) ⊆ Set.Icc (1:ℝ) 2) →
    (∀ i x, ‖Wslot i x‖ ≤ M i) →
    ∀ (W : 𝓢(ℝ,ℂ)) (X K : ℝ), Function.support (W : ℝ→ℂ) ⊆ Set.Icc a b →
    0 < X → 0 < K → X^2*(∏ i,P i)^2 ≤ U^B → K⁻¹ ≤ U^B →
    4*((X^2*(∏ i,P i)^2)^2/K)*U^(ξ/2) < 1 →
    ∀ (Φ : 𝓢(ℝ,ℂ)) (rows : Finset O),
    (∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) →
    (∀ z∈rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) →
    (∑ z∈rows, (‖original η (fixedBadMask*idealGenerator 1) 1 z W t X‖^2 *
      ∏ i, ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z (pool i)
        (fun I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t (P i)‖^2)^2) ≤
      Cd*(∏ i,M i)^4*(SchwartzMap.seminorm ℝ 0 0 W)^4*
        Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*U^ε +
      Ct*(∏ i,M i)^4*(SchwartzMap.seminorm ℝ 0 0 W)^4*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*U^(-saving) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hsource⟩ := short_input_energy (fun _ : Fin 2×ι => (2:ℝ))
    a b B ε ξ saving (fun _ => by norm_num) ha hb hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,hsource.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W X K hs hX hK hvol hKi hcut
  intro Φ rows hΦ hmajor
  let s := fourthInput η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX
  have hv : volume s.toData = X^2*(∏ i,P i)^2 :=
    fourthInput_volume η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX
  have hc : plainControl s W W = (∏ i,M i)^2*(SchwartzMap.seminorm ℝ 0 0 W)^2 :=
    fourthInput_plainControl η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX
  have hsour := hU.2 s W W rfl rfl hs hs (fun _ => le_rfl) fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) 1 1 Φ K hK (hv.symm ▸ hvol) hKi (hv.symm ▸ hcut)
  have hrow := finite_normalized_rows_le_source η fixedBadMask 1 t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s 1 1) Φ K (volume s.toData)
    hK (volume_pos s) (dvd_mul_right _ _) (dvd_mul_left _ _) rows hΦ hmajor
  have he (z : O) : ‖(Real.sqrt (volume s.toData) : ℂ)⁻¹ *
      (∑ I∈finiteColumns (Fintype.piFinset s.pools),coefficient s 1 1 I*
        rowWeight η fixedBadMask 1 z t I)‖^2 =
      (‖original η (fixedBadMask*idealGenerator 1) 1 z W t X‖^2 *
        ∏ i, ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 z (pool i)
          (fun I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t (P i)‖^2)^2 := by
    rw [fourthInput_normalized_product η t pool ν Wslot P M hprime hP hM hν hWslot hWbound W a b X ha hs hX z]
    simp only [norm_pow,norm_mul,norm_prod]
    rw [Finset.prod_pow]
    ring
  simp_rw [he] at hrow
  apply hrow.trans
  rw [hc] at hsour
  change ‖finiteHeckeEnergy η fixedBadMask 1 t (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s 1 1) Φ K‖ / volume s.toData ≤ _ at hsour
  convert hsour using 1 <;> ring

#print axioms short_fourth_source
end
end QRH.Cycle092.ReferenceShortP3
