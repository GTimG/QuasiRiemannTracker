/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.ChildCol
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Contract

/-!
# Inverse.Restore.Keys — finitely many child data per modulus `q`

* `finite_ideals_ge`: a nonzero ideal has finitely many divisors (ideals above it).
* `deletedModuli q`: the moduli of `deletedBase data` over all row data with
  `deletedPeriod (basePeriod data) = q`; **`deletedModuli_finite`** (each contains
  `(q' · rc(q')^k)`, `2592 q'^2 = q`).
* `childChars q`: unit-trivial residue characters modulo `childModulus q` (finite).
* `inverseRectAt_mono_dc`: the source bound is monotone in the degree and the constant.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.SevenEighths.HeckeInverseAmplification (RowData)
open OAI.CanonicalRowCompletion (reflectionConductor reflectionExcludedPrimes)
open DetectorDictionaryInverseRawInitialGates (deletedBase basePeriod)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

theorem finite_ideals_ge (N : Ideal O) (hN : N ≠ ⊥) : {M : Ideal O | N ≤ M}.Finite := by
  haveI : Finite (O ⧸ N) := Ring.HasFiniteQuotients.finiteQuotient hN
  haveI : Finite (Ideal (O ⧸ N)) :=
    Finite.of_injective (fun J : Ideal (O ⧸ N) => (J : Set (O ⧸ N))) SetLike.coe_injective
  refine (Set.finite_range (fun J : Ideal (O ⧸ N) => J.comap (Ideal.Quotient.mk N))).subset ?_
  intro M hM
  refine ⟨M.map (Ideal.Quotient.mk N), ?_⟩
  show Ideal.comap (Ideal.Quotient.mk N) (Ideal.map (Ideal.Quotient.mk N) M) = M
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]
  exact sup_eq_left.mpr hM

/-- The moduli of the deleted base characters of the row data of modulus `q`. -/
def deletedModuli (q : ℕ) : Set (Ideal O) :=
  {M | ∃ data : RowData, InverseInitialExcludedPeriod.deletedPeriod (basePeriod data) = q ∧
    (deletedBase data).modulus = M}

/-- The fixed ideal below every deleted modulus of base period `q'`. -/
def deletedFloor (q' : ℕ) : Ideal O :=
  Ideal.span {(q' : O) * reflectionConductor q' ^ (reflectionExcludedPrimes q').card}

theorem deletedFloor_ne_bot (q' : ℕ) (hq' : q' ≠ 0) : deletedFloor q' ≠ ⊥ := by
  unfold deletedFloor
  rw [Ne, Ideal.span_singleton_eq_bot]
  refine mul_ne_zero (by exact_mod_cast hq') (pow_ne_zero _ ?_)
  exact CanonicalRowCompletion.reflectionConductor_ne_zero q' hq'

theorem deletedFloor_le (data : RowData) :
    deletedFloor (basePeriod data) ≤ (deletedBase data).modulus := by
  have hmod : (deletedBase data).modulus =
      (InverseInitialDetectorSource.baseCharacter data).modulus *
        ∏ P ∈ DetectorDictionaryInverseRawInitialGates.excluded data, P := rfl
  rw [hmod, deletedFloor, ← Ideal.span_singleton_mul_span_singleton]
  apply Ideal.mul_mono (DetectorDictionaryInverseRawInitialGates.basePeriod_le data)
  rw [Ideal.span_singleton_le_iff_mem, ← Finset.prod_const]
  apply Ideal.prod_mem_prod
  intro P hP
  have h := excluded_le (basePeriod data) P hP
  exact h (Ideal.mem_span_singleton_self _)

theorem deletedModuli_finite (q : ℕ) : (deletedModuli q).Finite := by
  have hsub : deletedModuli q ⊆ ⋃ q' ∈ (Finset.range (q + 1)).filter (· ≠ 0),
      {M : Ideal O | deletedFloor q' ≤ M} := by
    rintro M ⟨data, hq, rfl⟩
    have hq0 := DetectorDictionaryInverseRawInitialGates.basePeriod_ne_zero data
    have hle : basePeriod data ≤ q := by
      rw [← hq]
      unfold InverseInitialExcludedPeriod.deletedPeriod
      have : 1 ≤ basePeriod data := Nat.one_le_iff_ne_zero.mpr hq0
      nlinarith
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range]
    exact ⟨basePeriod data, ⟨by omega, hq0⟩, deletedFloor_le data⟩
  refine Set.Finite.subset ?_ hsub
  apply Set.Finite.biUnion (Finset.finite_toSet _)
  intro q' hq'
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hq'
  exact finite_ideals_ge _ (deletedFloor_ne_bot q' hq'.2)

/-- Unit-trivial residue characters modulo the child modulus. -/
def childChars (q : ℕ) : Type :=
  {χ : MulChar (O ⧸ childModulus q) ℂ // ∀ u : Oˣ, χ (Ideal.Quotient.mk _ (u : O)) = 1}

/-- The child character of a residue character. -/
def charOf (q : ℕ) (hq : q ≠ 0) (χ : childChars q) : Character :=
  Character.ofResidue (childModulus q) (childModulus_ne_bot q hq) χ.1 χ.2

theorem childData_eq_charOf (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : CanonicalCoefficientClass.FactorsModulo
      (CanonicalCoefficientClass.fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) :
    ∃ χ : childChars q, childData q hq ψ hψ = childRowData (charOf q hq χ) ∧
      (childCharacter q hq ψ hψ).modulus = childModulus q :=
  ⟨⟨HeckeRowClosure.residueRow (childModulus q) (primaryTwist ψ) (primaryTwist_factors q ψ hψ),
    (childCharacter q hq ψ hψ).unit_trivial⟩, rfl, rfl⟩

/-- The source bound is monotone in the degree and the constant. -/
theorem inverseRectAt_mono_dc {cls : SlotClass} {ρ : AnchorRect} {Φ : ℝ → ℂ} {K : ℕ}
    {mesh Mmin Mmax ε Z : ℝ} {data : RowData} {d d' : ℕ} {C C' : ℝ} (hZ : 0 ≤ Z)
    (hC : 0 ≤ C) (hd : d ≤ d') (hCC : C ≤ C')
    (h : InverseRectAt cls ρ Φ K mesh Mmin Mmax ε Z data d C) :
    InverseRectAt cls ρ Φ K mesh Mmin Mmax ε Z data d' C' := by
  intro ι _ _ hK L ell β hv hv0 hc h1 h2 h3 h5 h6 h7 M hMlo hMhi r hadm rows hrows θ
  refine (h hK L ell β hv hv0 hc h1 h2 h3 h5 h6 h7 M hMlo hMhi r hadm rows hrows θ).trans ?_
  have hZp : 0 ≤ Z^(M+ε) := Real.rpow_nonneg hZ _
  have hb : 1 ≤ 1 + ‖θ‖ + hv := by have := norm_nonneg θ; linarith
  apply mul_le_mul (mul_le_mul_of_nonneg_right hCC hZp)
    (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hb hd) 2) (by positivity)
    (mul_nonneg (hC.trans hCC) hZp)

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.deletedModuli_finite
#print axioms Qrh.MarkedAnchor.Inverse.Restore.childData_eq_charOf
#print axioms Qrh.MarkedAnchor.Inverse.Restore.inverseRectAt_mono_dc
