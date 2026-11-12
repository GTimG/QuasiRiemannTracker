/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Oriented
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Keys

/-!
# Inverse.Restore.Uniform — child source constants uniform over the child data of `q`

**`uniform_child_sources`**: for a fixed parent class (`W`, `rayM`, `G`), slot bound `K`, modulus
`q` and two child profiles `Φ₂`, `Φ₀`, one degree, one constant and one threshold serve every child
datum that the restoration produces (orientation, `δ = deletedBase data`, child twist `ψ`): the child
classes and data range over the finite key set `Bool × deletedModuli q × childChars q`
(`Glue.childClass_congr`, `Keys.childData_eq_charOf`), and the source constants are summed. Also a
uniform bound `c₀` for the child deletion moduli.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.SevenEighths.HeckeInverseAmplification (RowData)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor)
open DetectorDictionaryInverseRawInitialGates (deletedBase basePeriod)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

theorem oBump_contDiff (neg : Bool) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2) : ContDiff ℝ ∞ (oBump neg W) := by
  cases neg
  · exact childBump_contDiff W hW 1 2 one_pos hWs
  · exact childBumpN_contDiff W hW 1 2 one_pos hWs

theorem oBump_support (neg : Bool) (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2) :
    Function.support (oBump neg W) ⊆ Set.Icc (1 : ℝ) 2 := by
  cases neg
  · exact childBump_support W 1 2 hWs
  · exact childBumpN_support W 1 2 hWs

theorem finite_hom_units {G : Type*} [CommGroup G] [Finite G] : Finite (G →* ℂˣ) := by
  haveI := Fintype.ofFinite G
  haveI : NeZero (Fintype.card G) := ⟨Fintype.card_pos.ne'⟩
  let φ : (G →* ℂˣ) → (G → rootsOfUnity (Fintype.card G) ℂ) := fun f g =>
    ⟨f g, by rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
  refine Finite.of_injective φ (fun f₁ f₂ h => MonoidHom.ext fun g => ?_)
  have := congrFun h g
  exact congrArg Subtype.val this

theorem childChars_finite (q : ℕ) (hq : q ≠ 0) : Finite (childChars q) := by
  haveI : Finite (O ⧸ childModulus q) :=
    Ring.HasFiniteQuotients.finiteQuotient (childModulus_ne_bot q hq)
  haveI : Finite (MulChar (O ⧸ childModulus q) ℂ) := by
    haveI : Finite ((O ⧸ childModulus q)ˣ →* ℂˣ) := finite_hom_units
    exact Finite.of_equiv _ MulChar.equivToUnitHom.symm
  unfold childChars
  infer_instance

/-- The child keys of modulus `q`. -/
abbrev KeyT (q : ℕ) : Type := Bool × deletedModuli q × childChars q × Bool

theorem uniform_child_sources {ρ : AnchorRect} {meshS ε' : ℝ}
    (hS : InverseRectSource canonicalFamily ρ meshS ε')
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (K q : ℕ) (hq : q ≠ 0)
    (Φ₂ Φ₀ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hab : ao ≤ bo)
    (h₂s : Function.support Φ₂ ⊆ Set.Icc ao bo) (h₂ : ContDiff ℝ ∞ Φ₂)
    (h₀s : Function.support Φ₀ ⊆ Set.Icc ao bo) (h₀ : ContDiff ℝ ∞ Φ₀) :
    ∃ (dU : ℕ) (CU Z₀ c₀ : ℝ), 0 < CU ∧ 1 < Z₀ ∧ 0 < c₀ ∧
      ∀ (neg : Bool) (data : RowData),
        InverseInitialExcludedPeriod.deletedPeriod (basePeriod data) = q →
      ∀ (ψ : O →* ℂ) (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ),
        (((deletedBase (childData q hq ψ hψ)).modulus.absNorm : ℕ) : ℝ) < c₀ ∧
        ∀ Z' : ℝ, Z₀ ≤ Z' →
          InverseRectAt (canonicalSlotsRay (oBump neg W) (33/50)
              (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
              (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
              (childSlotTwist_hH rayM G hH _ _)) ρ Φ₂ K meshS 1 1 ε' Z'
            (childData q hq ψ hψ) dU CU ∧
          InverseRectAt (canonicalSlotsRay (oBump neg W) (33/50)
              (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
              (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
              (childSlotTwist_hH rayM G hH _ _)) ρ Φ₀ K meshS 1 1 ε' Z'
            (childData q hq ψ hψ) dU CU := by
  haveI : Finite (deletedModuli q) := (deletedModuli_finite q).to_subtype
  haveI : Finite (childChars q) := childChars_finite q hq
  haveI : Fintype (KeyT q) := Fintype.ofFinite (KeyT q)
  haveI : Fintype (childChars q) := Fintype.ofFinite _
  let δrep : deletedModuli q → Character := fun M => deletedBase (Classical.choose M.2)
  have hδrep : ∀ M : deletedModuli q, (δrep M).modulus = M.1 :=
    fun M => (Classical.choose_spec M.2).2
  let clsK : KeyT q → SlotClass := fun k => canonicalSlotsRay (oBump k.1 W) (33/50)
    (childRay rayM (δrep k.2.1) (charOf q hq k.2.2.1))
    (childSlotTwist rayM G hH (δrep k.2.1) (charOf q hq k.2.2.1))
    (childSlotTwist_hH rayM G hH _ _)
  let ΦK : KeyT q → ℝ → ℂ := fun k => if k.2.2.2 then Φ₀ else Φ₂
  have hfam : ∀ k : KeyT q, canonicalFamily (clsK k) := fun k =>
    ⟨oBump k.1 W, oBump_contDiff k.1 W hW hWs, oBump_support k.1 W hWs, _, inferInstance, _, _, rfl⟩
  have hsrc : ∀ k : KeyT q, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → InverseRectAt (clsK k) ρ (ΦK k) K meshS 1 1 ε' Z
        (childRowData (charOf q hq k.2.2.1)) degree C := by
    intro k
    by_cases hk : k.2.2.2
    · have := hS K (clsK k) (hfam k) Φ₀ ao bo hao hab h₀s h₀ (childRowData (charOf q hq k.2.2.1))
      simpa only [ΦK, hk, if_true] using this
    · have := hS K (clsK k) (hfam k) Φ₂ ao bo hao hab h₂s h₂ (childRowData (charOf q hq k.2.2.1))
      simpa only [ΦK, hk, if_false, Bool.false_eq_true] using this
  choose degF CF Z0F hCF hZ0F hbF using hsrc
  refine ⟨∑ k, degF k, 1 + ∑ k, CF k, 2 + ∑ k, Z0F k,
    1 + ∑ χ : childChars q,
      (((deletedBase (childRowData (charOf q hq χ))).modulus.absNorm : ℕ) : ℝ),
    by have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => (hCF k).le); linarith,
    by have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => (zero_lt_one.trans (hZ0F k)).le)
       linarith,
    by have := Finset.sum_nonneg (fun χ (_ : χ ∈ (Finset.univ : Finset (childChars q))) =>
         (Nat.cast_nonneg (((deletedBase (childRowData (charOf q hq χ))).modulus.absNorm : ℕ)) :
           (0:ℝ) ≤ _))
       linarith, ?_⟩
  intro neg data hdq ψ hψ
  obtain ⟨χ, hdata, hηmod⟩ := childData_eq_charOf q hq ψ hψ
  refine ⟨?_, ?_⟩
  · rw [hdata]
    have := Finset.single_le_sum (f := fun χ : childChars q =>
      (((deletedBase (childRowData (charOf q hq χ))).modulus.absNorm : ℕ) : ℝ))
      (fun χ _ => Nat.cast_nonneg _) (Finset.mem_univ χ)
    linarith
  intro Z' hZ'
  let M : deletedModuli q := ⟨(deletedBase data).modulus, data, hdq, rfl⟩
  have hcls : ∀ b : Bool, canonicalSlotsRay (oBump neg W) (33/50)
      (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
      (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
      (childSlotTwist_hH rayM G hH _ _) = clsK (neg, M, χ, b) := by
    intro b
    exact childClass_congr rayM G hH (oBump neg W) (33/50) _ _ _ _ (hδrep M).symm
      (hηmod.trans rfl)
  have hZ0 : ∀ k : KeyT q, Z0F k ≤ Z' := by
    intro k
    have := Finset.single_le_sum (f := Z0F) (fun k _ => (zero_lt_one.trans (hZ0F k)).le)
      (Finset.mem_univ k)
    linarith
  have hZ'0 : 0 ≤ Z' := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => (zero_lt_one.trans (hZ0F k)).le)
    linarith
  have hdeg : ∀ k : KeyT q, degF k ≤ ∑ k, degF k :=
    fun k => Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ k)
  have hC : ∀ k : KeyT q, CF k ≤ 1 + ∑ k, CF k := by
    intro k
    have := Finset.single_le_sum (f := CF) (fun k _ => (hCF k).le) (Finset.mem_univ k)
    linarith
  rw [hcls false, hdata]
  exact ⟨inverseRectAt_mono_dc hZ'0 (hCF _).le (hdeg _) (hC _) (hbF (neg, M, χ, false) Z' (hZ0 _)),
    inverseRectAt_mono_dc hZ'0 (hCF _).le (hdeg _) (hC _) (hbF (neg, M, χ, true) Z' (hZ0 _))⟩

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.uniform_child_sources
