/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Candidate.Local.Qrh.JointDetector.NaturalSelectedNorm
import Candidate.Local.Qrh.JointDetector.DetectorWords
import Candidate.Local.Qrh.JointDetector.NaturalPositiveGram
import Candidate.Local.Qrh.JointDetector.NaturalTuplePartition

/-! Assembly of the natural selected norm. The long-source predicate below is
an explicit intermediate obligation. The amplification theorem discharges the
short-source completion using actual common slot coefficients and all ordinary
ideal products; it does not assume an amplifier or a completed natural norm. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeInverseAmplification ProbeHighRowFamily
local notation "O" => ActualEisensteinCubic.O

def NaturalLongCellNormBound (N : ℕ) (Z A P mesh Cslot wmin δ K : ℝ) : Prop :=
  ∀ (d : SelectedSlotData N) (cores : Finset FreeRow) (S : Finset (Ideal O)) (Y L : ℝ),
    d.Bounded Z mesh Cslot → d.Selects Z (cores.image Subtype.val) → d.HasSlope δ →
    wmin ≤ ∑ i, d.width i →
    1 ≤ Y → Y ≤ Z^A → (∀ u ∈ cores, rowNorm u ≤ Y) →
    Y ≤ L → L ≤ Z^P → (∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) →
    selectedNorm (cores.image Subtype.val) S ≤ K*L

/-- Actual joint amplification is performed on the WHOLE natural row set,
before fixing any higher-colour tuple. Its source range remains the fixed `P`.
The only pending analytic input is the displayed long-source natural norm. -/
theorem natural_cell_long_to_all (A P loss : ℝ)
    (hA : 0 < A) (hP : 3*A+1 ≤ P) (hloss : 0 < loss) :
    ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
      0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
      ∀ (Z mesh δ K : ℝ), Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2 ≤ δ → δ ≤ 1 → 1 ≤ K →
      NaturalLongCellNormBound N Z A P mesh Cslot wmin δ K →
      NaturalCellNormBound N Z A P mesh Cslot wmin δ (C*K*Z^loss) := by
  let ε := min (loss/8) (1/4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεloss : ε ≤ loss/8 := min_le_left _ _
  have hε1 : ε ≤ 1/4 := min_le_right _ _
  refine ⟨ε,hε,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Ca,Z₀,hCa,hamp⟩ := uniform_slot_crossing P (3*A) ε
    (by linarith) (by positivity) hε N Cslot wmin hCslot hwmin
  let C := 2*(Ca+1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C,max Z₀ 2,hC,?_⟩
  intro Z mesh δ K hZ hm hmU hδ hδ1 hK hlong
  intro d cores S B L hb hs hslope hwidth hB hBU hcores hL hLP hS
  have hz2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hz1 : 1 ≤ Z := by linarith
  have hz : 0 < Z := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hK0 : 0 < K := by linarith
  have hd : 0 < δ := by linarith
  have hZloss : 1 ≤ Z^loss := Real.one_le_rpow hz1 hloss.le
  have hother : 0 ≤ B^(1-δ)*L^δ := by positivity
  by_cases hlarge : B ≤ L
  · have hbound := hlong d cores S B L hb hs hslope hwidth hB hBU hcores hlarge hLP hS
    calc
      _ ≤ K*L := hbound
      _ ≤ (C*K*Z^loss)*L := by
        have hh : 1 ≤ C*Z^loss := (by linarith : 1 ≤ C).trans (le_mul_of_one_le_right hC.le hZloss)
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hK0.le) hL0.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hother) (by positivity)
  · have hecross : B^(δ/δ)=B := by rw [div_self hd.ne',Real.rpow_one]
    obtain ⟨target,ht,htU,heq⟩ := crossing_log_target Z A L B δ δ
      (by linarith) hA.le hL hB hBU hd le_rfl (by linarith) (by simpa [hecross] using (le_of_not_ge hlarge))
    rw [hecross] at heq
    obtain ⟨Y,merged,hYlo,hYhi,hmerged,hamplified⟩ := hamp Z L mesh δ target d
      (cores.image Subtype.val) S ((le_max_left _ _).trans hZ) hL hLP hm
      (by linarith) (by linarith) hδ1 ht htU hb hs hslope hwidth hS
    have hYcross : B ≤ Y := by rwa [heq] at hYlo
    have hY0 : 0 < Y := hB0.trans_le hYcross
    have hYupper : Y ≤ Z^(mesh+ε)*B := by
      apply hYhi.trans_eq
      rw [show target+mesh+ε = target+(mesh+ε) by ring,
        Real.rpow_add hz target (mesh+ε),← mul_assoc,heq]
      ring
    have hYP : Y ≤ Z^P := by
      calc
        _ ≤ Z^(mesh+ε)*Z^A := hYupper.trans
          (mul_le_mul_of_nonneg_left hBU (Real.rpow_nonneg hz.le _))
        _ = Z^(mesh+ε+A) := (Real.rpow_add hz _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
    have htarget := hlong d cores merged B Y hb hs hslope hwidth hB hBU hcores hYcross hYP hmerged
    have hden : 0 < (Y/L)^δ := Real.rpow_pos_of_pos (div_pos hY0 hL0) _
    have hscalar := amplified_long_envelope_le Z L B Y δ δ (mesh+ε)
      hz1 hL0 hB0 hY0 hd hδ1 (by positivity)
      (by simpa [hecross] using hYcross) (by simpa [hecross] using hYupper)
    have hratio : Contraction.ratio δ*δ=1-δ := by
      unfold Contraction.ratio
      field_simp
    rw [hratio] at hscalar
    calc
      _ ≤ Ca*Z^ε*selectedNorm (cores.image Subtype.val) merged/(Y/L)^δ := hamplified
      _ ≤ Ca*Z^ε*(K*Y)/(Y/L)^δ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htarget (by positivity)) hden.le
      _ ≤ Ca*Z^ε*(K*(Y+B^δ*Y^(1-δ)))/(Y/L)^δ := by
        apply div_le_div_of_nonneg_right _ hden.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hK0.le
        exact le_add_of_nonneg_right (by positivity)
      _ = Ca*K*Z^ε*((Y+B^δ*Y^(1-δ))/(Y/L)^δ) := by ring
      _ ≤ Ca*K*Z^ε*(2*Z^(mesh+ε)*B^(1-δ)*L^δ) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = (2*Ca)*K*Z^(ε+(mesh+ε))*(B^(1-δ)*L^δ) := by
        rw [Real.rpow_add hz ε (mesh+ε)]; ring
      _ ≤ C*K*Z^loss*(B^(1-δ)*L^δ) := by
        apply mul_le_mul_of_nonneg_right _ hother
        apply mul_le_mul (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith : 2*Ca ≤ C) hK0.le)
          (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (Real.rpow_nonneg hz.le _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL0.le) (by positivity)

namespace NaturalSelectedNorm
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open NaturalRowColours IdealMobiusDivisorSum CenteredExceptionalCount

/-- The good-prime long-source obligation has arbitrary nonrectangular tuple
sets. All bad-row states are discharged by the theorem below. -/
def GoodTupleLongCellNormBound (N : ℕ) (Z A P mesh Cslot wmin δ K : ℝ) : Prop :=
  ∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (S : Finset (Ideal O)) (Y L : ℝ),
    d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
    wmin ≤ ∑ i, d.width i →
    (∀ c ∈ F, ∀ j, Admissible (c j)) →
    (∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k))) →
    1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
    Y ≤ L → L ≤ Z^P → (∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) →
    selectedNorm (F.image tupleRow) S ≤ K*L

theorem reflectionBadIdeal_ne_zero : reflectionBadIdeal ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · exact Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  · have he := Finset.mem_singleton.mp hP
    subst P
    exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2:O) ≠ 0)

local instance : Fintype Oˣ := by
  letI : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

abbrev BadRowState := Oˣ × idealDivisors (reflectionBadIdeal^15)

def badRowFactor (s : BadRowState) : O := s.1.val*idealGenerator s.2.val

def badStateTuples (cores : Finset FreeRow) (s : BadRowState) : Finset ColourTuple :=
  (cores.filter fun z => z.val=badRowFactor s*goodElement (Ideal.span {z.val})).image
    (fun z => goodColour (Ideal.span {z.val}))

theorem badStateTuples_selected {N : ℕ} (d : SelectedSlotData N) (Z : ℝ)
    (cores : Finset FreeRow) (h : d.Selects Z (cores.image Subtype.val)) (s : BadRowState) :
    (d.quotient (badRowFactor s)).Selects Z ((badStateTuples cores s).image tupleRow) := by
  apply SelectedSlotData.quotient_selects h
  intro x hx
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  have hz' := Finset.mem_filter.mp hz
  exact Finset.mem_image.mpr ⟨z,hz'.1,hz'.2⟩

theorem badStateTuples_admissible (cores : Finset FreeRow) (s : BadRowState) :
    ∀ c ∈ badStateTuples cores s, ∀ j, Admissible (c j) := by
  intro c hc
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  exact goodColour_admissible _

theorem badStateTuples_pairwise (cores : Finset FreeRow) (s : BadRowState) :
    ∀ c ∈ badStateTuples cores s, Pairwise (fun j k => IsCoprime (c j) (c k)) := by
  intro c hc
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  exact goodColour_pairwise _

theorem badStateTuples_norm (cores : Finset FreeRow) (s : BadRowState) (Y : ℝ)
    (h : ∀ z ∈ cores, rowNorm z ≤ Y) :
    ∀ c ∈ badStateTuples cores s, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y := by
  intro c hc
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
  have hI : (Ideal.span {z.val} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr z.property.1
  exact (goodElement_norm_le _ hI z.property.2).trans (h z (Finset.mem_filter.mp hz).1)

theorem natural_rows_bad_cover (cores : Finset FreeRow) :
    cores.image Subtype.val ⊆ Finset.univ.biUnion
      (fun s : BadRowState => ((badStateTuples cores s).image tupleRow).image (badRowFactor s * ·)) := by
  intro z hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨v,J,hJ,hdiv,he⟩ := exists_bad_good_factor u
  let s : BadRowState := ⟨v,⟨J,(mem_idealDivisors (pow_ne_zero _ reflectionBadIdeal_ne_zero)).mpr hdiv⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨s,Finset.mem_univ _,Finset.mem_image.mpr ⟨goodElement (Ideal.span {u.val}),?_,he.symm⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨goodColour (Ideal.span {u.val}),?_,rfl⟩
  exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,he⟩,rfl⟩

theorem selectedNorm_le_primal (rows : Finset O) (S : Finset (Ideal O))
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ c : S → ℂ, (∑ z : rows, ‖ordinaryPolynomial S c z.val‖^2) ≤ K*∑ I, ‖c I‖^2) :
    selectedNorm rows S ≤ K := by
  have hp : ‖FiniteSieveOperator.operator (selectedMatrix rows S).conjTranspose‖^2 ≤ K := by
    apply FiniteSieveOperator.squared_norm_le_of_energy _ K hK
    intro c
    have hc := h (fun I => star (c I))
    have hid (z : rows) :
        (∑ I : S, (selectedMatrix rows S).conjTranspose z I*c I)=
          star (ordinaryPolynomial S (fun I => star (c I)) z.val) := by
      simp only [ordinaryPolynomial,star_sum,star_mul,star_star,selectedMatrix,
        Matrix.conjTranspose_apply,mul_comm]
    simpa only [hid,norm_star] using hc
  simpa only [FiniteSieveOperator.operator_conjTranspose_norm,selectedNorm] using hp

private theorem sum_biUnion_nonneg_le {T U : Type*} [DecidableEq U]
    (labels : Finset T) (S : T → Finset U) (f : U → ℝ) (hf : ∀ u, 0 ≤ f u) :
    ∑ u ∈ labels.biUnion S, f u ≤ ∑ t ∈ labels, ∑ u ∈ S t, f u := by
  induction labels using Finset.induction_on with
  | empty => simp
  | @insert t ts ht ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ht]
    have hh := Finset.sum_union_inter (s₁ := S t) (s₂ := ts.biUnion S) (f := f)
    have hn : 0 ≤ ∑ u ∈ S t ∩ ts.biUnion S, f u := Finset.sum_nonneg fun u _ => hf u
    linarith

/-- A finite union of source sectors costs their summed operator bounds.
This remains true with overlap, since the source energies are nonnegative. -/
theorem selectedNorm_rows_biUnion_le {T : Type*}
    (labels : Finset T) (rows : T → Finset O) (S : Finset (Ideal O)) :
    selectedNorm (labels.biUnion rows) S ≤ ∑ t ∈ labels, selectedNorm (rows t) S := by
  apply selectedNorm_le_primal _ _ _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  intro c
  rw [Finset.sum_coe_sort (labels.biUnion rows)
    (fun z => ‖ordinaryPolynomial S c z‖^2)]
  calc
    _ ≤ ∑ t ∈ labels, ∑ z ∈ rows t, ‖ordinaryPolynomial S c z‖^2 :=
      sum_biUnion_nonneg_le labels rows _ (fun z => sq_nonneg _)
    _ ≤ ∑ t ∈ labels, selectedNorm (rows t) S * ∑ I : S, ‖c I‖^2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← Finset.sum_coe_sort (rows t)
        (fun z => ‖ordinaryPolynomial S c z‖^2)]
      exact ordinaryPolynomial_energy (rows t) S c
    _ = _ := (Finset.sum_mul ..).symm

/-- All natural bad-place and unit states cost a fixed constant. There is no
ramified Gauss hypothesis, and all ordinary source columns remain present. -/
theorem goodTuple_long_to_natural {N : ℕ} {Z A P mesh Cslot wmin δ K : ℝ}
    (hgood : GoodTupleLongCellNormBound N Z A P mesh Cslot wmin δ K) :
    NaturalLongCellNormBound N Z A P mesh Cslot wmin δ ((Fintype.card BadRowState:ℝ)*K) := by
  intro d cores S Y L hb hs hδ hw hY hYA hcores hYL hLP hS
  apply (selectedNorm_mono_rows (natural_rows_bad_cover cores) S).trans
  apply (selectedNorm_rows_biUnion_le Finset.univ _ S).trans
  calc
    _ ≤ ∑ _s : BadRowState, K*L := by
      apply Finset.sum_le_sum
      intro s hs'
      apply (selectedNorm_mul_image_le _ _ _).trans
      exact hgood (d.quotient (badRowFactor s)) (badStateTuples cores s) S Y L
        (SelectedSlotData.quotient_bounded hb _) (badStateTuples_selected d Z cores hs s)
        (SelectedSlotData.quotient_hasSlope hδ _) hw
        (badStateTuples_admissible cores s) (badStateTuples_pairwise cores s)
        hY hYA (badStateTuples_norm cores s Y hcores) hYL hLP hS
    _ = _ := by simp [mul_assoc]

/-- Finite-cost completion of every source, row cell and diagonal. The sole
remaining input here is the actual offdiagonal form on each radial/ray cell;
it is quantified over ALL coefficient vectors, not one selected vector. -/
theorem goodTuple_norm_of_cell_offDiagonal (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (S : Finset (Ideal O))
    (Y L K : ℝ) (hL : 1 ≤ L) (hK : 0 ≤ K)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L)
    (hcell : ∀ k : TuplePartition.Key Y, ∀ a : TuplePartition.cell F Y k → ℂ,
      ‖tupleOffDiagonalGram (TuplePartition.cell F Y k) a L‖ ≤ K*L*∑ c, ‖a c‖^2) :
    selectedNorm (F.image tupleRow) S ≤
      (Fintype.card (TuplePartition.Key Y):ℝ)*
        ((BadFrequencySectors.boundedKeys L).card:ℝ)*
        ((1/6:ℝ)*QuadraticInitialBound.diagonalControl QuadraticInitialBound.sieveCutoff+K)*L := by
  let D := (1/6:ℝ)*QuadraticInitialBound.diagonalControl QuadraticInitialBound.sieveCutoff
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (QuadraticInitialBound.diagonalControl_nonneg _)
  have hcost : 0 ≤ ((BadFrequencySectors.boundedKeys L).card:ℝ)*((D+K)*L) := by positivity
  have hpart := TuplePartition.selectedNorm_partition_le F Y S _ hcost (fun k => ?_)
  · exact hpart.trans_eq (by dsimp [D]; ring)
  · apply tuple_selectedNorm_all_sources_le _ S L ((D+K)*L) (by linarith) (by positivity) hS
    intro a
    have hfcell : ∀ c ∈ TuplePartition.cell F Y k, ∀ j, Admissible (c j) := by
      intro c hc
      exact hF c (Finset.mem_filter.mp hc).1
    calc
      _ ≤ (D*L)*(∑ c, ‖a c‖^2)+‖tupleOffDiagonalGram (TuplePartition.cell F Y k) a L‖ :=
        tupleSmoothGram_le_diagonal_offDiagonal _ a hfcell L hL
      _ ≤ (D*L)*(∑ c, ‖a c‖^2)+K*L*(∑ c, ‖a c‖^2) := add_le_add le_rfl (hcell k a)
      _ = _ := by ring

/-- All cell and ordinary-source-sector counts have an arbitrarily small
power cost. The coefficient `K` here bounds the literal cell offdiagonal;
this theorem does not assert that analytic bound. -/
theorem goodTuple_long_of_cell_offDiagonal (A P loss : ℝ)
    (hA : 0 < A) (hP : 0 ≤ P) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Z mesh Cslot wmin δ K : ℝ),
      1 ≤ Z → 0 ≤ K →
      (∀ (d : SelectedSlotData N) (F : Finset ColourTuple) (Y L : ℝ),
        d.Bounded Z mesh Cslot → d.Selects Z (F.image tupleRow) → d.HasSlope δ →
        wmin ≤ ∑ i, d.width i →
        (∀ c ∈ F, ∀ j, Admissible (c j)) →
        (∀ c ∈ F, Pairwise (fun j k => IsCoprime (c j) (c k))) →
        1 ≤ Y → Y ≤ Z^A → (∀ c ∈ F, ((Ideal.span {tupleRow c}).absNorm:ℝ) ≤ Y) →
        Y ≤ L → L ≤ Z^P →
        ∀ k : TuplePartition.Key Y, ∀ a : TuplePartition.cell F Y k → ℂ,
          ‖tupleOffDiagonalGram (TuplePartition.cell F Y k) a L‖ ≤
            K*Z^(loss/3)*L*∑ c, ‖a c‖^2) →
      GoodTupleLongCellNormBound N Z A P mesh Cslot wmin δ (C*(1+K)*Z^loss) := by
  obtain ⟨Cr,hCr,hrows⟩ := TuplePartition.key_card_small_power A (loss/3) hA (by positivity)
  obtain ⟨Cs,hCs,hsectors⟩ := badSector_small_power P (loss/3) hP (by positivity)
  let D : ℝ := (1/6:ℝ)*QuadraticInitialBound.diagonalControl QuadraticInitialBound.sieveCutoff
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (QuadraticInitialBound.diagonalControl_nonneg _)
  let C := Cr*Cs*(D+1)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N Z mesh Cslot wmin δ K hZ hK hcell d F S Y L hb hs hδ hw hF hpF hY hYA hheight hYL hLP hS
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hL : 1 ≤ L := hY.trans hYL
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzpow : 1 ≤ Z^(loss/3) := Real.one_le_rpow hZ (by positivity)
  have hdiag : D+K*Z^(loss/3) ≤ (D+1)*(1+K)*Z^(loss/3) := by
    have hh := mul_le_mul_of_nonneg_left hzpow hD
    have hhK : 0 ≤ D*K*Z^(loss/3) := by positivity
    nlinarith
  have hbase := goodTuple_norm_of_cell_offDiagonal F hF S Y L (K*Z^(loss/3)) hL
    (by positivity) hS (hcell d F Y L hb hs hδ hw hF hpF hY hYA hheight hYL hLP)
  change selectedNorm (F.image tupleRow) S ≤ C*(1+K)*Z^loss*L
  calc
    _ ≤ (Fintype.card (TuplePartition.Key Y):ℝ)*
        ((BadFrequencySectors.boundedKeys L).card:ℝ)*(D+K*Z^(loss/3))*L := by
      simpa only [D,mul_assoc] using hbase
    _ ≤ (Cr*Z^(loss/3))*(Cs*Z^(loss/3))*((D+1)*(1+K)*Z^(loss/3))*L := by
      apply mul_le_mul_of_nonneg_right _ hL0.le
      apply mul_le_mul
        (mul_le_mul (hrows Z Y hZ hY hYA) (hsectors Z L hZ hL0 hLP)
          (Nat.cast_nonneg _) (by positivity)) hdiag (by positivity) (by positivity)
    _ = _ := by
      have hpow : Z^(loss/3)*Z^(loss/3)*Z^(loss/3)=Z^loss := by
        rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = C*(1+K)*(Z^(loss/3)*Z^(loss/3)*Z^(loss/3))*L := by dsimp [C]; ring
        _ = _ := by rw [hpow]

/-- Uniform long-source good-tuple estimates finish the precise natural
contract by fixed bad/unit states and actual whole-row joint amplification.
The displayed hypothesis remains an explicit intermediate obligation. -/
theorem natural_selected_norm_of_goodTuple_long
    (hlong : ∀ A P gap loss : ℝ, 0 < A → 3*A+1 ≤ P →
      0 < gap → gap < 1/2 → 0 < loss →
      ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot wmin : ℝ),
        0 ≤ Cslot → 0 < wmin → ∃ C Z₀ : ℝ, 0 < C ∧
        ∀ Z mesh δ : ℝ, Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
          1/2+gap ≤ δ → δ ≤ 3/4 →
          GoodTupleLongCellNormBound N Z A P mesh Cslot wmin δ (C*Z^loss)) :
    NaturalSelectedCellNorm := by
  intro A P gap loss hA hP hgap hgaphalf hloss
  obtain ⟨ma,hma,hamp⟩ := natural_cell_long_to_all A P (loss/2) hA hP (by positivity)
  obtain ⟨mg,hmg,hgood⟩ := hlong A P gap (loss/2) hA hP hgap hgaphalf (by positivity)
  refine ⟨min ma mg,lt_min hma hmg,?_⟩
  intro N Cslot wmin hCslot hwmin
  obtain ⟨Ca,Za,hCa,hamp⟩ := hamp N Cslot wmin hCslot hwmin
  obtain ⟨Cg,Zg,hCg,hgood⟩ := hgood N Cslot wmin hCslot hwmin
  let D : ℝ := (Fintype.card BadRowState:ℝ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  let K := D*Cg+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Ca*K,max 1 (max Za Zg),mul_pos hCa hK,?_⟩
  intro Z mesh δ hZ hm hmm hδlo hδhi
  have hz1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hz0 : 0 < Z := lt_of_lt_of_le zero_lt_one hz1
  have hzpow : 1 ≤ Z^(loss/2) := Real.one_le_rpow hz1 (by positivity)
  have hgood := hgood Z mesh δ ((le_max_right _ _).trans hZ |>.trans' (le_max_right _ _))
    hm (hmm.trans (min_le_right _ _)) hδlo hδhi
  have hnatural := goodTuple_long_to_natural hgood
  have hnatural' : NaturalLongCellNormBound N Z A P mesh Cslot wmin δ (K*Z^(loss/2)) := by
    intro d cores S Y L hb hs hδ hw hY hYA hheight hYL hLP hS
    apply (hnatural d cores S Y L hb hs hδ hw hY hYA hheight hYL hLP hS).trans
    change (D*(Cg*Z^(loss/2)))*L ≤ (K*Z^(loss/2))*L
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have := mul_le_mul_of_nonneg_right (show D*Cg ≤ K by dsimp [K]; linarith) (by positivity : 0 ≤ Z^(loss/2))
    nlinarith
  have hKone : 1 ≤ K*Z^(loss/2) := by
    have hKone : 1 ≤ K := by
      have hh : 0 ≤ D*Cg := mul_nonneg hD hCg.le
      dsimp [K]
      linarith
    exact hKone.trans (le_mul_of_one_le_right hK.le hzpow)
  have hh := hamp Z mesh δ (K*Z^(loss/2))
    ((le_max_right _ _).trans hZ |>.trans' (le_max_left _ _)) hm
    (hmm.trans (min_le_left _ _)) (by linarith) (by linarith) hKone hnatural'
  have heq : Ca*(K*Z^(loss/2))*Z^(loss/2)=(Ca*K)*Z^loss := by
    calc
      _ = (Ca*K)*(Z^(loss/2)*Z^(loss/2)) := by ring
      _ = _ := by rw [← Real.rpow_add hz0,show loss/2+loss/2=loss by ring]
  simpa only [heq] using hh

end NaturalSelectedNorm

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.natural_cell_long_to_all

#print axioms Qrh.JointDetector.NaturalSelectedNorm.goodTuple_long_to_natural

#print axioms Qrh.JointDetector.NaturalSelectedNorm.goodTuple_norm_of_cell_offDiagonal
#print axioms Qrh.JointDetector.NaturalSelectedNorm.goodTuple_long_of_cell_offDiagonal
#print axioms Qrh.JointDetector.NaturalSelectedNorm.natural_selected_norm_of_goodTuple_long
