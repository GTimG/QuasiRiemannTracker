/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseAllSlots

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

/-- The same exact inverse moment on actual free sixth-power cores. -/
theorem normalized_inverse_marked_energy_free (W : ℝ → ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : Continuous W)
    (hεm : 0 < εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ),
        (∀ i,0≤ell i) → (∀ i,∀ P∈L i,Prime P) →
        (∀ i,∀ P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Icc (1:ℝ) 2) →
      ∀ (η : Character) (m A root : O) (ν : ι → Character)
        (σslot vslot : ι → ℝ) (tslot : ℝ),
        (∀ i,lo≤σslot i) → (∀ i,σslot i≤hi) →
      ∀ r : ℝ,0≤r → r+2*(∑ i,ell i)<1 → 2*r+8*(∑ i,ell i)<3 →
      ∀ rows : Finset FreeRow, (∀ u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀ (χ : FreeRow → Character) (reverse : Bool),
        (∀ u∈rows,∀ I : Ideal O, idealCoeff (χ u) I =
          if reverse then conj (idealCoeff (data.character (ProbeHighRowFamily.momentElement u)) I) else idealCoeff (data.character (ProbeHighRowFamily.momentElement u)) I) →
      ∀ tstar : ℝ,∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,
      ∀ height freq : ℝ,0≤height → freq∈Icc (-height) height →
      (∑ u∈rows,‖polynomial (χ u) true
        ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ freq *
          (∏ i, normalizedSlot η m A (u.val*root^6) (L i)
            (fun I => idealCoeff (ν i) I*
              HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I)
            tslot (U^(ell i)))‖^2) ≤ (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,henergy⟩ := normalized_inverse_marked_energy_no_separation W lo hi εm hWs hW hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hp hratio η m A root ν σslot vslot tslot hσlo hσhi
    r hr hfirst hsecond rows hrows χ reverse hχ tstar n hn σ hσ height freq hh ht
  let castRow : FreeRow → NonzeroElement := ProbeHighRowFamily.momentElement
  have hinj : Function.Injective castRow := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : NonzeroElement => z.val) hxy
  let rows' := rows.image castRow
  let χ' := fun u : NonzeroElement => if reverse then (data.character u).inverse else data.character u
  have hc (u : NonzeroElement) (hu : u∈rows') (I : Ideal O) :
      idealCoeff (χ' u) I = if reverse then conj (idealCoeff (data.character u) I) else idealCoeff (data.character u) I := by
    cases reverse <;> simp [χ',castRow,idealCoeff_inverse_conj]
  have hrowNorm (u : NonzeroElement) (hu : u∈rows') : ‖eisEmbedding u.val‖^2≤U := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact hrows x hx
  have he := henergy U hU hK L ell hell hp hratio η m A root ν σslot vslot tslot hσlo hσhi
    r hr hfirst hsecond rows' hrowNorm χ' reverse hc tstar n hn σ hσ height freq hh ht
  rw [Finset.sum_image (fun x _ y _ h => hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  have hcoeff (I : Ideal O) : idealCoeff (χ u) I = idealCoeff (χ' (castRow u)) I := by
    rw [hχ u hu I]
    cases reverse <;> simp [χ',castRow,idealCoeff_inverse_conj]
  rw [polynomial_eq_of_idealCoeff (χ u) (χ' (castRow u)) hcoeff]
  rfl

end
end Qrh.JointDetector.RepeatedMarks
