import Submissions.hailey_collet_1252270103.LocalMoment.UnmarkedBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

set_option autoImplicit false

/-! Actual incumbent inverse moments, actual buffered-zero witnesses, and
the cost of the finite label/dyadic partition for the unmarked batch.

This removes an inverse-moment assumption for a fixed finite family of
`RowData`; it does not provide the unmarked plain moment or identify the
joint physical row with that family. The witness constructor retains the
nonprincipal, conductor, coefficient, and buffered-maximum conditions. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorCoefficientTransfer
open HeckeDetectorDyadicProfiles HeckeDetectorRawFiber
open HeckeDetectorInverseFiberCount HeckeDetectorProfiles

private theorem rawMoment_mono_constant (data : RowData) (W : ℝ → ℂ)
    (c κ A B : ℝ) (hAB : A ≤ B) (h : RawMoment data W c κ A) :
    RawMoment data W c κ B := by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

/-- One incumbent constant works for a fixed finite character-label family,
uniformly over all dyadic lengths, orientations, and independent frequencies.
The input contains no assumed raw moment. -/
theorem fixed_family_inverse_raw {Label : Type*} [Fintype Label]
    (data : Label → RowData) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ label reverse, ∀ n : ℕ, n ≤ 2 → ∀ U : ℝ, 0 < U →
      ∀ tstar r : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ height t : ℝ, 0 ≤ height → t ∈ Icc (-height) height →
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar r)) n) s t
        RawMoment (data label) W c κ (C * (1 + height)^J) ∧
        RawMoment (data label) (scaleProfile W) c κ (C * (1 + height)^J) := by
  obtain ⟨J, hJ⟩ := ProbeDetectorInverseRawField.fixed_raw_profiles c κ hc hκ
  choose A hA hbound using (fun label => hJ (data label))
  let C : ℝ := 1 + ∑ label, A label
  have hsum : 0 ≤ ∑ label, A label := Finset.sum_nonneg (fun j _ => (hA j).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC (label) : A label ≤ C := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hA j).le)
      (Finset.mem_univ label)
    dsimp [C]
    linarith
  refine ⟨J, C, hC, ?_⟩
  intro label reverse n hn U hU tstar r s hs height t hh ht
  have hb := hbound label reverse n hn U hU tstar r s hs height t hh ht
  have hconst : A label * (1 + height)^J ≤ C * (1 + height)^J :=
    mul_le_mul_of_nonneg_right (hAC label) (by positivity)
  exact ⟨rawMoment_mono_constant _ _ _ _ _ _ hconst hb.1,
    rawMoment_mono_constant _ _ _ _ _ _ hconst hb.2⟩

/-- With the actual incumbent inverse input supplied above, only the plain
unmarked field remains to build `UnmarkedMoments` for every batch fiber. -/
theorem batch_moments_of_plain_unmarked {Label : Type*} [Fintype Label]
    (data : Label → RowData) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {U a ε tstar T allowance εm height : ℝ} {i : ℕ},
      0 < U → 0 ≤ height →
      ∀ (B : UnmarkedBatch Label U a ε tstar T allowance i), B.data = data →
      ∀ label left right, ∀ hne : (B.fiberRows label left right).Nonempty,
        let F := B.fiber label left right hne
        (∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ t ∈ Icc (-height) height,
          ∑ u ∈ F.rows, ‖HeckeDyadic.polynomial (F.family u F.label) false
            ((HeckeDetectorRowwisePolynomial.logProfile^[j]) positiveAnnular)
            (U^F.m) s t * HeckeDyadic.polynomial (F.family u F.label) false
            ((HeckeDetectorRowwisePolynomial.logProfile^[k]) positiveAnnular)
            (U^F.m) s t‖^2 ≤
              (C * (1 + height)^J) * U^(max 1 (2 * F.m) + εm)) →
        UnmarkedMoments F c κ (C * (1 + height)^J) height εm := by
  obtain ⟨J, C, hC, hraw⟩ := fixed_family_inverse_raw data c κ hc hκ
  refine ⟨J, C, hC, ?_⟩
  intro U a ε tstar T allowance εm height i hU hh B hd label left right hne F hp
  refine ⟨?_, hp⟩
  intro n hn s hs t ht
  have hdata : F.rowData = data label := by
    change B.data label = data label
    rw [hd]
  rw [hdata]
  exact hraw label F.reverse n hn U hU tstar F.r s hs height t hh ht

/-- Construct supported witnesses from actual buffered maxima on just the
nonempty source set, and retain the exact coefficient dictionary. No
detector witness is postulated for an arbitrary ambient free row. -/
theorem unmarked_batch_from_actual_maxima
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * η)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * η ≤ ε / 2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ {Label : Type*} [Fintype Label] (rows : Finset FreeRow), rows.Nonempty →
      ∀ (family : rows → Label → Character)
        (hχ : ∀ u j, (family u j).residue ≠ 1)
        (data : Label → RowData) (reverse : Label → Bool),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ Z^d) →
      (∀ u : rows, ∀ j, ∀ Q : Ideal O, idealCoeff (family u j) Q =
        if reverse j then starRingEnd ℂ
          (idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) Q)
        else idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) Q) →
      ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u, HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        (3 * (i + 1 : ℕ) * Z^τ) < a + 2 * e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (family u) (hχ u)
        ((3 * i : ℕ) * Z^τ)) →
      (∀ u j, (family u j).modulus.absNorm ≤ Z^d) →
      ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
        ∃ B : UnmarkedBatch Label (Z^d) a ε tstar (Z^τ)
          ((Z^d)^(τ / (2 * dmax))) i,
          B.rows = rows ∧ B.data = data ∧ B.reverse = reverse ∧
          ∀ u : rows, B.family u.val = family u := by
  obtain ⟨Z₀, hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀, ?_⟩
  intro Z hZ d hd hd' Label _ rows hne family hχ data reverse hrow hcoeff
    a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨w⟩ := hZ₀ Z hZ d hd hd' family hχ a i hi ha ha' hnext hcurrent hQ
    tstar ht ht'
  obtain ⟨u₀, hu₀⟩ := hne
  let B := UnmarkedBatch.ofSupportedRows rows ⟨u₀, hu₀⟩ family w hrow data reverse hcoeff
  refine ⟨B, rfl, rfl, rfl, ?_⟩
  intro u
  change family (supportedRowRetraction rows ⟨u₀, hu₀⟩ u.val) = family u
  rw [supportedRowRetraction_mem]

/-- The label family is fixed before the row scale. Both dyadic counts
are paid by an arbitrary positive power, with the label cost in a fixed
constant. This assertion would not cover a growing family of labels. -/
theorem fixed_label_dyadic_cost {Label : Type*} [Fintype Label]
    (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ U : ℝ in atTop,
      (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 ≤ K * U^η := by
  obtain ⟨K, hK, hbound⟩ := HeckeDetectorClassBudget.dyadic_cost_eventually η hη
  refine ⟨(Fintype.card Label : ℝ) * K, by positivity, ?_⟩
  filter_upwards [hbound] with U hU
  calc
    _ ≤ (Fintype.card Label : ℝ) * (K * U^η) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ = _ := by ring

end SevenEighths.LocalMoment
end
end OAI
