/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 2: the label-side norm facts of a source used by `GeometryAt`.

* `rad_norm_le`: the radical `∏_{P ∣ I} P` has norm at most `N(I)`.
* `lA_norm_le`, `lA_norm_ge`: the second twist of a label has `1 ≤ N(A₂) ≤ N(C₂)·N(D₂)`.
* `labelPool_le`: every second Möbius divisor of a label is a nonzero ideal of norm at most the
  column bound of the source.
* `box_exists`: the dyadic box of radius `M = ⌊c_b log₂ Z⌋ + 2` contains every in-range dyad
  vector once the columns are `≤ Z⁸`, `1 ≤ K_c ≤ Z¹⁸`, `4R ≤ Z¹⁸`, `H ≤ Z¹⁸` and `c_b ≥ 19`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows

noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondActiveDyadic CenteredMomentMobiusRegroup CenteredMomentSecondWholeKernel
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### Norms of divisors -/

theorem absNorm_le_of_dvd {I J : Id} (h : I ∣ J) (hJ : J ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h)
  have hpos : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast Nat.le_of_dvd hpos hd

theorem one_le_absNorm {I : Id} (hI : I ≠ 0) : (1:ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- **The radical has norm at most the ideal.** -/
theorem rad_norm_le (I : Id) (hI : I ≠ 0) :
    (Ideal.absNorm (∏ P ∈ QRH.Record1252270103KernelMass.primeSupport I, P) : ℝ) ≤
      Ideal.absNorm I := by
  apply absNorm_le_of_dvd _ hI
  change (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P) ∣ I
  calc (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P)
      = ((UniqueFactorizationMonoid.normalizedFactors I).dedup).prod := by
        rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.map_id']
    _ ∣ (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.dedup_le _)
    _ = I := Ideal.prod_normalizedFactors_eq_self hI

theorem normValue_le_of_dvd {a b : O} (h : a ∣ b) (hb : b ≠ 0) : normValue a ≤ normValue b := by
  unfold normValue
  apply absNorm_le_of_dvd _ (Ideal.span_singleton_eq_bot.not.mpr hb)
  exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr h)

theorem normValue_primary (I : Id) (hI : Supported I) :
    normValue (primaryGenerator I) = Ideal.absNorm I := by
  unfold normValue; rw [primary_span_supported I hI]

/-! ### The second twist of a label -/

theorem lA_norm_le (S : Finset Id) (l : Lab S) :
    normValue (lA S l) ≤ (Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2 := by
  obtain ⟨hC, hD, hCD⟩ := lab_data S l
  unfold lA Packet.secondTwist
  rw [normValue_mul]
  have h1 : normValue (commonFrequencyGenerator l.1.val.1 l.1.val.2) ≤ Ideal.absNorm l.1.val.1 :=
    (normValue_le_of_dvd (commonFrequencyGenerator_dvd _ _ hC hD hCD).1
      (supported_primaryGenerator_ne_zero _ hC)).trans_eq (normValue_primary _ hC)
  have hdvd : nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2 ∣ primaryGenerator l.1.val.2 := by
    rw [← right_generator_product _ _ hC hD hCD]
    unfold nonunitFrequencyGenerator
    calc (∏ P ∈ nonunitPartitionSet l.1.val.1 l.1.val.2 l.2, commonPrime l.1.val.1 l.1.val.2 P)
        ∣ ∏ P : CommonIndex l.1.val.1 l.1.val.2, commonPrime l.1.val.1 l.1.val.2 P :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      _ ∣ ∏ P : CommonIndex l.1.val.1 l.1.val.2,
            commonPrime l.1.val.1 l.1.val.2 P ^ rightExponent l.1.val.1 l.1.val.2 P :=
          Finset.prod_dvd_prod_of_dvd _ _ (fun P _ =>
            dvd_pow_self _ (rightExponent_pos l.1.val.1 l.1.val.2 P).ne')
  have h2 : normValue (nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2) ≤
      Ideal.absNorm l.1.val.2 :=
    (normValue_le_of_dvd hdvd (supported_primaryGenerator_ne_zero _ hD)).trans_eq
      (normValue_primary _ hD)
  exact mul_le_mul h1 h2 (normValue_pos _ (nonunitFrequencyGenerator_ne_zero _ _ hC _)).le
    (Nat.cast_nonneg _)

theorem lA_norm_ge (S : Finset Id) (l : Lab S) : 1 ≤ normValue (lA S l) :=
  normValue_ge_one _ (lA_ne S l)

/-! ### The second Möbius divisors -/

/-- **Every second Möbius divisor of a label is a nonzero ideal below the column bound.** -/
theorem labelPool_le (S : Finset Id) (X : ℝ) (hX : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X)
    (l : Lab S) (Lp : Id) (hLp : Lp ∈ labelPool S l) :
    Lp ≠ 0 ∧ (Ideal.absNorm Lp : ℝ) ≤ X := by
  unfold labelPool at hLp
  obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hLp
  unfold divisorPool at hmem
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hmem
  dsimp only at hj
  rw [sectorElement_span] at hj
  have hjp := (Finset.mem_filter.mp j.property).1
  rw [mem_residualPool] at hjp
  have hjs := Finset.mem_filter.mp hjp
  have hprod0 : l.1.val.2 * j.val ≠ 0 := hjs.2.1
  have hj0 : j.val ≠ 0 := right_ne_zero_of_mul hprod0
  have hdvd : Lp ∣ j.val := (OAI.IdealMobiusDivisorSum.mem_idealDivisors hj0).mp hj
  have hLp0 : Lp ≠ 0 := by
    rintro rfl
    exact hj0 (zero_dvd_iff.mp hdvd)
  refine ⟨hLp0, ?_⟩
  have h1 := absNorm_le_of_dvd hdvd hj0
  have h2 := absNorm_le_of_dvd (dvd_mul_left j.val l.1.val.2) hprod0
  exact (h1.trans h2).trans (hX _ hjs.1)

/-! ### The dyadic box -/

theorem lab_cols_le (S : Finset Id) (X : ℝ) (hX : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X)
    (l : Lab S) :
    (Ideal.absNorm l.1.val.1 : ℝ) ≤ X ∧ (Ideal.absNorm l.1.val.2 : ℝ) ≤ X := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp l.1.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have e1 : l.1.val.1 = CenteredMomentCompleteCommon.commonPart q.1 q.2 := by rw [← he]
  have e2 : l.1.val.2 = CenteredMomentCompleteCommon.commonPart q.2 q.1 := by rw [← he]
  rw [e1, e2]
  constructor
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hI.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.1 q.2) : ℝ) ≤ Ideal.absNorm q.1).trans
      (hX _ hI.1)
  · exact (by exact_mod_cast CenteredMomentCompleteCommon.absNorm_commonPart_le _ _ hJ.2.1 :
      (Ideal.absNorm (CenteredMomentCompleteCommon.commonPart q.2 q.1) : ℝ) ≤ Ideal.absNorm q.2).trans
      (hX _ hJ.1)

theorem logb_le_of_le_rpow (Z y e : ℝ) (hZ : 1 < Z) (hy : 0 < y) (h : y ≤ Z^e) :
    Real.logb 2 y ≤ e * Real.logb 2 Z := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  calc Real.logb 2 y ≤ Real.logb 2 (Z^e) :=
        Real.logb_le_logb_of_le (by norm_num) hy h
    _ = e * Real.logb 2 Z := Real.logb_rpow_eq_mul_logb_of_pos hZ0

/-- One coordinate of the box from its scale bounds. -/
theorem scale_ok (Z x M lo up : ℝ) (hZ : 2 ≤ Z) (hx : 19 * Real.logb 2 Z ≤ x)
    (hM : x + 1 < M) (hlo0 : 0 < lo) (hlo : 1 / Z^(16:ℝ) ≤ lo) (hup0 : 0 < up)
    (hup : up ≤ Z^(18:ℝ)) :
    0 < lo ∧ -M ≤ Real.logb 2 lo ∧ Real.logb 2 (4 * up) ≤ M := by
  have hZ1 : 1 < Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hl2 : 1 ≤ Real.logb 2 Z := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hZ0]; simpa using hZ
  refine ⟨hlo0, ?_, ?_⟩
  · have h1 : Real.logb 2 (1 / Z^(16:ℝ)) ≤ Real.logb 2 lo :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hlo
    have h2 : Real.logb 2 (1 / Z^(16:ℝ)) = -(16 * Real.logb 2 Z) := by
      rw [one_div, Real.logb_inv, Real.logb_rpow_eq_mul_logb_of_pos hZ0]
    linarith
  · have h1 : Real.logb 2 (4 * up) = 2 + Real.logb 2 up := by
      rw [Real.logb_mul (by norm_num) hup0.ne', show (4:ℝ) = 2^(2:ℝ) by norm_num,
        Real.logb_rpow (by norm_num) (by norm_num)]
    have h2 := logb_le_of_le_rpow Z up 18 hZ1 hup0 hup
    linarith

theorem box_exists (S : Finset Id) (Kc R H Z cb : ℝ) (hZ : 2 ≤ Z) (hcb : 19 ≤ cb)
    (hX : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z^(8:ℝ)) (hKc1 : 1 ≤ Kc) (hKc : Kc ≤ Z^(18:ℝ))
    (hR : 4 * R ≤ Z^(18:ℝ)) (hH : H ≤ Z^(18:ℝ)) :
    ∃ Mbox : ℤ, (0 ≤ Mbox ∧ (Mbox : ℝ) ≤ cb * Real.logb 2 Z + 2) ∧
      ∀ l n, inRange S Kc R H l n → n ∈ box Mbox := by
  have hZ1 : 1 < Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hl2 : 1 ≤ Real.logb 2 Z := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hZ0]; simpa using hZ
  set x := cb * Real.logb 2 Z with hx
  have hx0 : 0 ≤ x := by positivity
  have hx19 : 19 * Real.logb 2 Z ≤ x := mul_le_mul_of_nonneg_right hcb (by linarith)
  have hfl := Int.floor_le x
  have hfl' := Int.lt_floor_add_one x
  have hZ18 : (1:ℝ) ≤ Z^(18:ℝ) := Real.one_le_rpow hZ1.le (by norm_num)
  have hZ16 : 1 / Z^(16:ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact Real.one_le_rpow hZ1.le (by norm_num)
  refine ⟨⌊x⌋ + 2, ⟨by have := Int.floor_nonneg.mpr hx0; omega, by push_cast; linarith⟩, ?_⟩
  apply box_of_scales S Kc R H
  intro l i
  have hM : (x + 1 : ℝ) < ((⌊x⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
  obtain ⟨hC8, hD8⟩ := lab_cols_le S _ hX l
  have hA1 := lA_norm_ge S l
  have hA2 := lA_norm_le S l
  have hC1 := one_le_absNorm (lab_data S l).1.1
  have hD1 := one_le_absNorm (lab_data S l).2.1.1
  have hNN : (Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2 ≤ Z^(16:ℝ) := by
    rw [show (16:ℝ) = 8 + 8 by norm_num, Real.rpow_add hZ0]
    exact mul_le_mul hC8 hD8 (by positivity) (by positivity)
  have hNN0 : (0:ℝ) < (Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2 := by positivity
  have hsec : secondEffectiveScale l.1.val.1 l.1.val.2 (lA S l) Kc =
      Kc * normValue (lA S l) / ((Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2) := by
    unfold secondEffectiveScale; rw [← normValue_eq_embedding]
  have hsec_lo : 1 / Z^(16:ℝ) ≤ secondEffectiveScale l.1.val.1 l.1.val.2 (lA S l) Kc := by
    rw [hsec]
    calc 1 / Z^(16:ℝ) ≤ 1 / ((Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2) :=
          one_div_le_one_div_of_le hNN0 hNN
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hNN0.le
  have hsec_hi : secondEffectiveScale l.1.val.1 l.1.val.2 (lA S l) Kc ≤ Z^(18:ℝ) := by
    rw [hsec, div_le_iff₀ hNN0]
    calc Kc * normValue (lA S l) ≤ Kc * ((Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2) :=
          mul_le_mul_of_nonneg_left hA2 (by linarith)
      _ ≤ Z^(18:ℝ) * ((Ideal.absNorm l.1.val.1 : ℝ) * Ideal.absNorm l.1.val.2) :=
          mul_le_mul_of_nonneg_right hKc hNN0.le
  have hsec0 : 0 < secondEffectiveScale l.1.val.1 l.1.val.2 (lA S l) Kc :=
    lt_of_lt_of_le (by positivity) hsec_lo
  have hA0 : 0 < normValue (lA S l) := by linarith
  have h1 : 4 * R / normValue (lA S l) ≤ Z^(18:ℝ) := by
    rw [div_le_iff₀ hA0]; nlinarith
  have h2 : H / (Ideal.absNorm l.1.val.1 : ℝ) ≤ Z^(18:ℝ) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : H / (Ideal.absNorm l.1.val.2 : ℝ) ≤ Z^(18:ℝ) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcoord : ∀ i : Fin 4,
      (0 < sourceLower l.1.val.1 l.1.val.2 (lA S l) Kc i ∧
        1 / Z^(16:ℝ) ≤ sourceLower l.1.val.1 l.1.val.2 (lA S l) Kc i) ∧
      (0 < sourceUpper l.1.val.1 l.1.val.2 (lA S l) Kc R H i ∧
        sourceUpper l.1.val.1 l.1.val.2 (lA S l) Kc R H i ≤ Z^(18:ℝ)) := by
    intro i
    fin_cases i
    · exact ⟨⟨hsec0, hsec_lo⟩, ⟨hsec0, hsec_hi⟩⟩
    · exact ⟨⟨one_pos, hZ16⟩, ⟨lt_of_lt_of_le one_pos (le_max_left _ _), max_le hZ18 h1⟩⟩
    · exact ⟨⟨one_pos, hZ16⟩, ⟨lt_of_lt_of_le one_pos (le_max_left _ _), max_le hZ18 h2⟩⟩
    · exact ⟨⟨one_pos, hZ16⟩, ⟨lt_of_lt_of_le one_pos (le_max_left _ _), max_le hZ18 h3⟩⟩
  obtain ⟨⟨hl0, hl⟩, ⟨hu0, hu⟩⟩ := hcoord i
  exact scale_ok Z x _ _ _ hZ hx19 hM hl0 hl hu0 hu

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
