/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Contract
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.DeletionOverlapEnergy
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.ColoringEnergy

/-!
# Interface.Native

The native instances of the anchor contracts and the base anchor `(311/400, 0)`.

* `NativeDirectInverse` is, verbatim, the statement of HC
  `OAI.SevenEighths.Record12518109GainDeletion.direct_reference_energy`
  (Record12518109Gain/Upstream/DeletionInverse.lean) with `directPrimeSlot` written as
  `directSlot` (same definition). It is a premise here; it is supplied by
  `Inverse.nativeDirectInverse` from a prebuilt copy of `direct_reference_energy`.
* `nativeDirectInverseOverlap`: the disjoint native theorem implies the same
  estimate for OVERLAPPING pools (full product), by HC
  `Record12518109GainDeletion.overlapping_direct_energy` fed with the disjoint estimate on all
  sub-pools of all sub-embeddings (gates by `sum_comp_le_total`; cost `overlapCost 1 K`).
  It is what `inverseRectSource_of_native` uses for the contract without `PairwiseDisjoint L`.
* `ReserveParametricSource` is PR103's reserve-parametric ordinary family: global sources
  `G(B,L,c)` arbitrarily close to `(1,2,3/20)`.
* `base_anchor`: both premises give `AnchorAt (311/400) 0`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Interface.Native
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- HC `direct_reference_energy`, verbatim (native gates, unit row ball, all rows). -/
def NativeDirectInverse : Prop :=
  ∀ (W : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support W ⊆ Icc ao bo →
    ContDiff ℝ ∞ W → ∀ εm : ℝ, 0 < εm → ∀ K : ℕ,
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0 < C ∧ 1 < U₀ ∧
      ∀ U : ℝ, U₀ ≤ U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀ i, 0 ≤ ell i) → (∀ i, ∀ P ∈ L i, Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/U^(ell i)) ∈ Icc (1 : ℝ) 2) →
        (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
        (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < U^(ell i)) →
      ∀ r : ℝ, 0 ≤ r → r+2*(∑ i, ell i) < 1 → 2*r+8*(∑ i, ell i) < 3 →
      ∀ rows : Finset HeckeInverseAmplification.NonzeroElement,
        (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ U) → ∀ θ : ℝ,
      (∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest W θ)
          (U^r) 0 0 * (∏ i, directSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2

/-- `NativeDirectInverse` without `PairwiseDisjoint L`: overlapping pools, full product. -/
def NativeDirectInverseOverlap : Prop :=
  ∀ (W : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support W ⊆ Icc ao bo →
    ContDiff ℝ ∞ W → ∀ εm : ℝ, 0 < εm → ∀ K : ℕ,
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0 < C ∧ 1 < U₀ ∧
      ∀ U : ℝ, U₀ ≤ U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀ i, 0 ≤ ell i) → (∀ i, ∀ P ∈ L i, Prime P) →
        (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/U^(ell i)) ∈ Icc (1 : ℝ) 2) →
        (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
        (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < U^(ell i)) →
      ∀ r : ℝ, 0 ≤ r → r+2*(∑ i, ell i) < 1 → 2*r+8*(∑ i, ell i) < 3 →
      ∀ rows : Finset HeckeInverseAmplification.NonzeroElement,
        (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ U) → ∀ θ : ℝ,
      (∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest W θ)
          (U^r) 0 0 * (∏ i, directSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2

/-- The disjoint native estimate gives the overlapping one (HC
`overlapping_direct_energy` with `B = 1`; the separated input on every sub-pool family of every
sub-embedding is the disjoint estimate itself, with inherited primes, ratios, coefficient bounds
and deletion gates, and the width gates by `sum_comp_le_total`). -/
theorem nativeDirectInverseOverlap (hnat : NativeDirectInverse) : NativeDirectInverseOverlap := by
  intro W ao bo hao hab hsW hW εm hεm K
  obtain ⟨degree, hd⟩ := hnat W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree, fun data => ?_⟩
  obtain ⟨C, U₀, hC, hU₀, hb⟩ := hd data
  refine ⟨Record12518109GainDeletion.overlapCost 1 K * C, U₀,
    mul_pos (Record12518109GainDeletion.overlapCost_pos 1 le_rfl K) hC, hU₀, ?_⟩
  intro U hU ι _ _ hK L ell β hell hp hratio hβ hlarge r hr hfirst hsecond rows hrows θ
  have hU1 : 1 < U := hU₀.trans_le hU
  have hUp : 0 < U := zero_lt_one.trans hU1
  let D : HeckeInverseAmplification.NonzeroElement → ℂ := fun u =>
    polynomial (data.character u) true (InverseMoment.childLogTest W θ) (U^r) 0 0
  let E : ℝ := C*U^(1+εm)*((1+‖θ‖)^degree)^2
  have hE : 0 ≤ E := by positivity
  have hP (i : ι) : 1 ≤ U^(ell i) := Real.one_le_rpow hU1.le (hell i)
  have hN (i : ι) (p : Ideal O) (hp' : p ∈ L i) : (p.absNorm : ℝ) ≤ 2*U^(ell i) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i p hp').2
  have hsep : ∀ {J : Type} [Fintype J] [DecidableEq J],
      ∀ f : J → ι, Function.Injective f → ∀ L' : J → Finset (Ideal O),
      (∀ j, L' j ⊆ L (f j)) →
      (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') →
      (∑ v ∈ rows, ‖D v * (∏ j, Record12518109GainDeletion.directPrimeSlot v.val (L' j)
        (β (f j)) (U^(ell (f j))))‖^2) ≤ E := by
    intro J _ _ f hf L' hsub hdis
    have hJK : Fintype.card J ≤ K := (Fintype.card_le_of_injective f hf).trans hK
    have hsum : (∑ j, ell (f j)) ≤ ∑ i, ell i :=
      RepeatedPrimeSlots.sum_comp_le_total f hf ell hell
    exact hb U hU hJK L' (fun j => ell (f j)) (fun j => β (f j))
      (fun j => hell (f j)) (fun j p hp' => hp (f j) p (hsub j hp')) hdis
      (fun j p hp' => hratio (f j) p (hsub j hp'))
      (fun j p hp' => hβ (f j) p (hsub j hp')) (fun j => hlarge (f j))
      r hr (by linarith) (by linarith) rows hrows θ
  have he := Record12518109GainDeletion.overlapping_direct_energy rows (fun u => u.val) D L β
    (fun i => U^(ell i)) 1 E le_rfl hE K hK hP hβ (fun i p hp' => (hp i p hp').ne_zero) hN hsep
  calc (∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest W θ)
          (U^r) 0 0 * (∏ i, directSlot u.val (L i) (β i) (U^(ell i)))‖^2)
      = ∑ u ∈ rows, ‖D u * (∏ i, Record12518109GainDeletion.directPrimeSlot u.val (L i) (β i)
          (U^(ell i)))‖^2 := rfl
    _ ≤ Record12518109GainDeletion.overlapCost 1 K * E := he
    _ = Record12518109GainDeletion.overlapCost 1 K * C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
      simp only [E]; ring

/-- (a) The native theorem gives the inverse contract on every rectangle of the native region,
for every slot family (the native theorem admits all bounded slot vectors; overlapping pools by
`nativeDirectInverseOverlap`). -/
theorem inverseRectSource_of_native (hnat : NativeDirectInverse) (fam : SlotClass → Prop)
    {ρ : AnchorRect} (hρ : ρ.NativeInverse) : UniformInverseRectSource fam ρ := by
  intro ε hε
  refine ⟨1,one_pos,?_⟩
  intro K cls _ Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,hd⟩ := nativeDirectInverseOverlap hnat Φ ao bo hao hab hΦs hΦ ε hε K
  obtain ⟨C,U₀,hC,hU₀,hb⟩ := hd data
  refine ⟨degree,C,U₀,hC,hU₀,fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 _ hell _ hp hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hM : M = 1 := le_antisymm hM2 hM1
  subst hM
  obtain ⟨g1,g2⟩ := AnchorRect.native_gates hρ hadm
  have hrows' : ∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z := fun u hu => by
    simpa using hrows u hu
  -- the native bound pays the row height only; the slot heights are absorbed
  -- (`‖β‖ ≤ 1`), so the full height factor dominates.
  refine (hb Z hZ hK L ell β hell hp hratio hβ hlarge r hadm.1 g1 g2 rows hrows' θ).trans ?_
  have hZ1 : 0 ≤ C*Z^(1+ε) := by
    have : 0 < Z := lt_of_lt_of_le (zero_lt_one.trans hU₀) hZ
    positivity
  exact mul_le_mul_of_nonneg_left (heightFactor_row_le θ hv0 degree) hZ1

/-- PR103 reserve-parametric ordinary sources approaching `(B,L,c) = (1,2,3/20)`. -/
def ReserveParametricSource : Prop :=
  ∀ η : ℝ, 0 < η → ∃ B L c : ℝ, QRH.Record1252270103Source.GlobalSource B L c ∧
    0 ≤ L ∧ L ≤ 2+η ∧ 1-η ≤ B ∧ 3/20-η ≤ c

/-- The base anchor `(R, z_R) = (311/400, 0)` of the stage chain. -/
theorem base_anchor (hnat : NativeDirectInverse) (hres : ReserveParametricSource) :
    AnchorAt (311/400) 0 := by
  apply AnchorAt.of_small (δ₀ := 1/100) (by norm_num)
  intro δ hδ hδ1
  refine ⟨inverseRectSource_of_native hnat canonicalFamily ?_,?_⟩
  · constructor <;> simp only [anchorRect] <;> linarith
  · obtain ⟨B,L,c,hsrc,hL0,hL,hB,hc⟩ := hres δ hδ
    apply ordinaryRectSource_of_global hsrc hL0
    · simp only [anchorRect]
      have hS0 : 0 ≤ (1-311/400)/2+0-δ := by linarith
      have hS1 : (1-311/400)/2+0-δ ≤ 2 := by linarith
      have h1 := mul_le_mul_of_nonneg_right hL hS0
      have h2 := mul_le_mul_of_nonneg_left hS1 hδ.le
      nlinarith
    · simp only [anchorRect]
      linarith

end
end Qrh.MarkedAnchor.Interface.Native

#print axioms Qrh.MarkedAnchor.Interface.Native.nativeDirectInverseOverlap
#print axioms Qrh.MarkedAnchor.Interface.Native.inverseRectSource_of_native
#print axioms Qrh.MarkedAnchor.Interface.Native.base_anchor
