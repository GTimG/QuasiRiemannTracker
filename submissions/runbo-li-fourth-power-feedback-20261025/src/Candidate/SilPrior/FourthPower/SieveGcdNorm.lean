/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform GCD sorting into concrete smoothed coprime norms, with actual
lengths and an explicit finite maximum. No analytic bound is assumed. -/
import Candidate.SilPrior.FourthPower.SieveSmoothed

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveGcdNorm
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CompletedGauss ConcretePrimeRowBridge IdealMobiusDivisorSum CenteredExceptionalCount
open CanonicalRowCompletion
open SexticSieve SieveSmoothed SieveGcd SieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

def pairs (B : ℝ) : Finset (Id × Id) := insert (1,1)
  ((SieveRanges.fullRange B).biUnion (fun D => (idealDivisors D).image (fun E => (D,E))))

def envelope (M B : ℝ) : ℝ := (pairs B).sup' (Finset.insert_nonempty _ _)
  (fun p => coprimeNorm (M/(Ideal.absNorm p.2 : ℝ)) (B/(Ideal.absNorm p.1 : ℝ)))

theorem entry_le_envelope (M B : ℝ) {D E : Id} (hD : D ∈ SieveRanges.fullRange B)
    (hE : E ∈ idealDivisors D) :
    coprimeNorm (M/(Ideal.absNorm E : ℝ)) (B/(Ideal.absNorm D : ℝ)) ≤ envelope M B := by
  exact Finset.le_sup'
    (fun p : Id × Id => coprimeNorm (M/(Ideal.absNorm p.2 : ℝ)) (B/(Ideal.absNorm p.1 : ℝ)))
    (show (D,E) ∈ pairs B from Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨E,hE,rfl⟩⟩))

theorem envelope_nonneg (M B : ℝ) : 0 ≤ envelope M B := by
  have he : coprimeNorm (M/(Ideal.absNorm (1:Id) : ℝ)) (B/(Ideal.absNorm (1:Id) : ℝ)) ≤ envelope M B :=
    Finset.le_sup'
      (fun p : Id × Id => coprimeNorm (M/(Ideal.absNorm p.2 : ℝ)) (B/(Ideal.absNorm p.1 : ℝ)))
      (show (1,1) ∈ pairs B from Finset.mem_insert_self _ _)
  exact (coprimeNorm_nonneg _ _).trans he

theorem pair_geometry (B : ℝ) (hB : 1 ≤ B) (p : Id × Id) (hp : p ∈ pairs B) :
    1 ≤ (Ideal.absNorm p.2 : ℝ) ∧ (Ideal.absNorm p.2 : ℝ) ≤ (Ideal.absNorm p.1 : ℝ) ∧
      (Ideal.absNorm p.1 : ℝ) ≤ B := by
  rcases Finset.mem_insert.mp hp with he | hp
  · subst p
    simpa using hB
  · obtain ⟨D,hD,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hp
    have hd := SieveRanges.mem_fullRange.mp hD
    have hED := (mem_idealDivisors hd.1.1).mp hE
    have he0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.1 hED
    exact ⟨norm_one_le he0,norm_le_of_dvd hd.1.1 hED,hd.2⟩

theorem envelope_attained (M B : ℝ) (hB : 1 ≤ B) :
    ∃ Δ₁ Δ₂ : ℝ, 1 ≤ Δ₁ ∧ Δ₁ ≤ Δ₂ ∧ Δ₂ ≤ B ∧
      envelope M B = coprimeNorm (M/Δ₁) (B/Δ₂) := by
  obtain ⟨p,hp,he⟩ := Finset.exists_mem_eq_sup' (Finset.insert_nonempty _ _)
    (fun p : Id × Id => coprimeNorm (M/(Ideal.absNorm p.2 : ℝ)) (B/(Ideal.absNorm p.1 : ℝ)))
  have hg := pair_geometry B hB p hp
  exact ⟨Ideal.absNorm p.2,Ideal.absNorm p.1,hg.1,hg.2.1,hg.2.2,he⟩

theorem finite_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type*} [Fintype n] (cols : n → Id),
      Function.Injective cols → (∀ j, Supported (cols j)) → (∀ j, PowerFree 6 (cols j)) →
      ∀ (B : ℝ), 1 ≤ B → (∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ B) →
      ∀ (a : n → ℂ) (R : Finset O) (M : ℝ), 0 < M →
      (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
      (∑ z ∈ R, ‖∑ j, row (cols j) z*a j‖^2) ≤ C*B^ε*envelope M B*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,h⟩ := quantitative_gcd_descent ε hε
  refine ⟨C,hC,?_⟩
  intro n _ cols hinj hc hf B hB hN a R M hM hR
  apply h cols hc B hB hN a R M hM hR (envelope M B) (envelope_nonneg M B)
  intro D hD E hE
  apply (descendant_norm D cols hinj hc hf (M/(Ideal.absNorm E : ℝ)) B hN a (idealGenerator E)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  apply entry_le_envelope M B _ hE
  apply SieveRanges.mem_fullRange.mpr
  refine ⟨gcdPool_supported cols hc D hD,?_⟩
  obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact (norm_le_of_dvd (hc i).1 (gcd_dvd_left _ _)).trans (hN i)

theorem lambda_gcd_descent (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M B : ℝ, 1 ≤ M → 1 ≤ B →
      SieveRanges.lambda M B ≤ C*B^ε*envelope M B := by
  obtain ⟨C,hC,h⟩ := finite_energy_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M B hM hB
  apply (bound_iff _ _ _
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hB) _)) (envelope_nonneg M B))).mpr
  intro a
  let cols : SieveRanges.freeRange B → Id := Subtype.val
  let R := (SieveRanges.fullRange M).image primaryGenerator
  have hr : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
    intro z hz
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hz
    have hi := SieveRanges.mem_fullRange.mp hI
    rw [(primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hi.1)).1]
    exact hi.2
  have hb := h cols Subtype.val_injective
    (fun I => (SieveRanges.mem_freeRange.mp I.property).1)
    (fun I => (SieveRanges.mem_freeRange.mp I.property).2.1) B hB
    (fun I => (SieveRanges.mem_freeRange.mp I.property).2.2)
    (fun I => a I.val) R M (zero_lt_one.trans_le hM) hr
  have hinj : Set.InjOn primaryGenerator (SieveRanges.fullRange M : Set Id) := by
    intro I hI J hJ he
    have hi := (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (SieveRanges.mem_fullRange.mp hI).1)).1
    have hj := (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J (SieveRanges.mem_fullRange.mp hJ).1)).1
    rw [← hi,← hj,he]
  change (∑ z ∈ (SieveRanges.fullRange M).image primaryGenerator,
    ‖∑ j, row (cols j) z*a j.val‖^2) ≤ _ at hb
  rw [Finset.sum_image (fun I hI J hJ hij => hinj hI hJ hij)] at hb
  have hinner (z : O) : (∑ j : SieveRanges.freeRange B, row (cols j) z*a j.val) =
      ∑ I ∈ SieveRanges.freeRange B, a I*idealRowHom z I := by
    calc
      _ = ∑ I : SieveRanges.freeRange B, a I.val*idealRowHom z I.val := by
        apply Finset.sum_congr rfl
        intro I _
        simp only [cols,row,mul_comm]
      _ = _ := Finset.sum_coe_sort (SieveRanges.freeRange B) (fun I : Id => a I*idealRowHom z I)
  have hmass : (∑ j : SieveRanges.freeRange B, ‖a j.val‖^2) =
      coefficientMass (SieveRanges.freeRange B) a := by
    exact Finset.sum_coe_sort (SieveRanges.freeRange B) (fun I : Id => ‖a I‖^2)
  simp_rw [hinner] at hb
  rw [hmass] at hb
  exact hb

end
end Candidate.SilPrior.FourthPower.SieveGcdNorm
