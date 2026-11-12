/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet's `Record1252270103Source/High/{ActualFiber,WeightedFiber,WeightedRows}.lean`
(`OrdinaryFiberMoments`, `weighted_bound_of_card`, `adaptiveFiber`, `weighted_row_sum`, Apache-2.0):
the earlier ordinary face is replaced by the anchor-gated moments and the cutoff
may depend on the amplitude bin. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.FiberExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount

/-!
# High.Weighted

The weighted HIGH row sum of one batch at a fixed buffered zero bin `a` (`ν = 2a-1`).

* `AnchorFiberMoments`: the four primitive inputs of one detector fiber — native unmarked inverse
  count, native unmarked ordinary moment, and the marked inverse / squared ordinary moments for
  every whole-slot selection of width `≤ selW a0 a1 S x` at the witness width `x` (anchor of an
  earlier stage or native source, `High.Sources`).
* `anchor_fiber_count`: `#fiber ≤ 192(1+h)C · U^(fiberTarget + 154ε + ν·mesh + εm)`.
* `anchorFiber` / `anchor_fiber_sum`: the partition of the rows by slot amplitude bin, witness label and
  dyadic witness widths, with a cutoff `cut bin` chosen per amplitude bin.
* `anchor_weighted_row_sum`: with the buffered slot bound `‖Q u s‖ ≤ (U^w_s)^(ν/2 + binWidth)`,
  `∑_rows ‖∏ Q‖² ≤ (#bins·#labels·dyadic²·192(1+h)C) · U^(E + 154ε + ν·mesh + εm + 2·binWidth·S)`
  whenever `fiberTarget(ν, e_bin, cut bin, S) + e_bin S ≤ E` for every occupied bin
  (`e_bin = 2·weightedMean` of the bin values; the slot pointwise payment `e s`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition

variable {Row Label Slot : Type*}

/-- The primitive moment inputs of one HIGH detector fiber (anchor-gated marked moments). -/
structure AnchorFiberMoments (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε tstar a0 a1 w εm C height : ℝ) (label : Label)
    (J K : Fin (dyadicLength U)) : Prop where
  inverseUnmarked : (rows.card : ℝ) ≤ (192*(1+height)*C)*
    U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J.val))/6)-
      (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm)
  plainUnmarked : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,
    ∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
      polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
        C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)
  inverseMarked : w ≤ Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val) < 1 →
    ∀ selected : Finset Slot, selected⊆slots →
      (∑ s∈selected,widths s) ≤ selW a0 a1 (∑ s∈slots,widths s) (Real.logb U ((2 : ℝ)^J.val)) →
    ∀ n : ℕ,n≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) true
      ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
      (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*(∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)
  plainMarked : w ≤ 2*Real.logb U ((2 : ℝ)^K.val) → 2*Real.logb U ((2 : ℝ)^K.val) < 1 →
    ∀ selected : Finset Slot, selected⊆slots →
      (∑ s∈selected,widths s) ≤ selW a0 a1 (∑ s∈slots,widths s) (2*Real.logb U ((2 : ℝ)^K.val)) →
    ∀ j k : ℕ,j+k≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
      polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*(∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)

/-- **Count of one HIGH fiber from its primitive inputs.** -/
theorem anchor_fiber_count (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth εm C height a0 a1 w : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hε0 : 0≤ε) (hε : ε≤1/1000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh) (hL : 0≤∑ s∈slots,widths s)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (hwc : w ∈ cutoffs)
    (witness : ∀u,SupportedWitness (χ u) U a ε (3*w/2+1/1000000) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : AnchorFiberMoments rows slots χ Q widths U a ε (3*w/2+1/1000000) a0 a1 w εm C height
      label J K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(fiberTarget a0 a1 (2*a-1) (2*weightedMean slots widths g) w (∑ s∈slots,widths s) +
        150*ε + (4*ε+(2*a-1)*mesh+εm)) := by
  have hU1 : 1 ≤ U := hU.le
  have hK0 : 0 ≤ 192*(1+height)*C := by positivity
  have hI0 : (rows.card : ℝ) ≤ (192*(1+height)*C) *
      U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J.val))/6)
        - (2*a-1)*Real.logb U ((2 : ℝ)^J.val) + (4*ε+εm)) :=
    count_promote hU1 le_rfl hK0 hmom.inverseUnmarked (by linarith)
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε (3*w/2+1/1000000)
    T allowance i hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C
    height hC hheight hfreq hmom.plainUnmarked
  have hP0' : (rows.card : ℝ) ≤ (192*(1+height)*C) *
      U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))
        - 2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val) + (4*ε+εm)) :=
    count_promote hU1 le_rfl hK0 hP0 (by linarith)
  have hc := high_fiber_count rows hne χ U a ε (3*w/2+1/1000000) T allowance i hU ha hν witness
    label J K hlabel hJ hK slots Q widths g mesh binWidth εm C height hmesh hbin hw hwm hL
    hbins hC hheight hfreq a0 a1 w (192*(1+height)*C) (4*ε+εm) ha1 ha1' hwc rfl hε0 hε hK0 hI0
    hP0' hmom.inverseMarked hmom.plainMarked
  have hνm : 0 ≤ (2*a-1)*mesh := mul_nonneg (by linarith) hmesh
  refine count_promote hU1 (by rw [max_self]) hK0 hc ?_
  have : max (4*ε+εm) (4*ε+(2*a-1)*mesh+εm) ≤ 4*ε+(2*a-1)*mesh+εm := max_le (by linarith) le_rfl
  linarith

/-! ### Partition by amplitude bin, label and dyadic widths, with per-bin cutoffs -/

section Partition
variable [Fintype Label]

/-- The key of a row: its amplitude bin, and the label and dyadic widths of its witness at the
cutoff of that bin. -/
def anchorKey (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (u : Row) : BinLabel slots ((2*a-1)/2) binWidth × Label ×
        Fin (dyadicLength U) × Fin (dyadicLength U) :=
  let b := amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u
  (b,(witness b u).label,(witness b u).left,(witness b u).right)

/-- One fiber of the partition. -/
def anchorFiber (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => anchorKey slots widths Q χ U a ε T allowance binWidth i hbin cut witness u =
    (bin,j,J,K))

theorem anchorFiber_fields
    (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u ∈ anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K) :
    u ∈ rows ∧ (witness bin u).label=j ∧ (witness bin u).left=J ∧
      (witness bin u).right=K ∧ ∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
        binValue slots ((2*a-1)/2) binWidth bin s := by
  obtain ⟨hrow,hkey⟩ := Finset.mem_filter.mp hu
  have hb : amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u = bin :=
    congrArg Prod.fst hkey
  have hw : (witness bin u).label=j ∧ (witness bin u).left=J ∧ (witness bin u).right=K := by
    dsimp [anchorKey] at hkey
    rw [hb] at hkey
    simpa only [Prod.mk.injEq,true_and] using hkey
  refine ⟨hrow,hw.1,hw.2.1,hw.2.2,?_⟩
  intro s hs
  have hv := congrArg (fun b : BinLabel slots ((2*a-1)/2) binWidth => (b ⟨s,hs⟩).val) hb
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

theorem anchor_fiber_sum (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (f : Row → ℝ) :
    (∑u∈rows,f u) = ∑bin,∑j,∑J,∑K,
      ∑u∈anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K,
        f u := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=rows) (t:=Finset.univ)
    (g:=anchorKey slots widths Q χ U a ε T allowance binWidth i hbin cut witness)
    (f:=f) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,anchorFiber] using hh.symm

end Partition

/-- Slot product payment (as Hailey Collet's `weighted_bound_of_card`): rows with common amplitude
bins `g` and the buffered upper bound have `‖∏ Q‖² ≤ U^(2 q S + 2 binWidth S)`. -/
theorem weighted_of_card (rows : Finset Row) (slots : Finset Slot) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U ν binWidth A X : ℝ) (hU : 1<U) (hbin : 0<binWidth)
    (hw : ∀s∈slots,0<widths s) (hL : 0≤∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (ν/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(ν/2+binWidth))
    (hcard : (rows.card : ℝ)≤A*U^X) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*U^(X+2*weightedMean slots widths g*(∑s∈slots,widths s)+
      2*binWidth*(∑s∈slots,widths s)) := by
  set S := ∑s∈slots,widths s with hSdef
  set q := weightedMean slots widths g with hqdef
  have hU0 : 0<U := zero_lt_one.trans hU
  have hmeanS : q*S=∑s∈slots,widths s*g s := by
    rcases lt_or_eq_of_le hL with hLp | hzero
    · rw [hqdef, hSdef]; unfold weightedMean; exact div_mul_cancel₀ _ hLp.ne'
    · have hempty : slots=∅ := by
        by_contra hne
        have hpos := Finset.sum_pos hw (Finset.nonempty_iff_ne_empty.mpr hne)
        linarith
      subst hempty
      simp [hSdef]
  have hprod (u : Row) (hu : u∈rows) : ‖∏s∈slots,Q u s‖^2≤U^(2*q*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (ν/2) binWidth
      hU hbin hw (hQ u hu)
    have hg : (∑s∈slots,widths s*HeckePrimeAmplitudeBins.amplitude
        (U^(widths s)) (ν/2) binWidth (Q u s))=∑s∈slots,widths s*g s :=
      Finset.sum_congr rfl (fun s hs=>by rw [hbins u hu s hs])
    rw [hg,←hmeanS] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hU0.le _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
    congr 1
    ring
  have hA : 0 ≤ A*U^X := (Nat.cast_nonneg _).trans hcard
  calc
    _ ≤ ∑u∈rows,U^(2*q*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*q*S+2*binWidth*S) := by simp
    _ ≤ (A*U^X)*U^(2*q*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hU0.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hU0]; congr 1; congr 1; ring

/-- **The weighted HIGH row sum of one batch at the zero bin `a`.** -/
theorem anchor_weighted_row_sum [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth εm C height a0 a1 E : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hε0 : 0≤ε) (hε : ε≤1/1000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh) (hL : 0≤∑s∈slots,widths s)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ) (hcut : ∀ bin, cut bin ∈ cutoffs)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ bin j J K, AnchorFiberMoments
      (anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K)
      slots χ Q widths U a ε (3*cut bin/2+1/1000000) a0 a1 (cut bin) εm C height j J K)
    (hE : ∀ bin, (∃ u ∈ rows, ∀ s ∈ slots,
        HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
          binValue slots ((2*a-1)/2) binWidth bin s) → fiberTarget a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin)
        (∑s∈slots,widths s) +
      2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)*(∑s∈slots,widths s)
        ≤ E) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(E + 154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s)) := by
  set A := 192*(1+height)*C with hAdef
  set X := E + 154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s) with hXdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hU0 : 0<U := zero_lt_one.trans hU
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K,
        ‖∏s∈slots,Q u s‖^2) ≤ A*U^X := by
    set F := anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := anchorFiber_fields rows slots widths Q χ U a ε
        T allowance binWidth i hbin cut witness bin j J K u hu
      have hc := anchor_fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth εm C height
        a0 a1 (cut bin) i hU ha hν hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1'
        (hcut bin) (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K)
      have hh := weighted_of_card F slots Q widths (binValue slots ((2*a-1)/2) binWidth bin)
        U (2*a-1) binWidth A _ hU hbin hw hL (fun u hu=>(hfields u hu).2.2.2.2)
        (fun u hu=>hQ u (hfields u hu).1) hc
      refine hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU.le ?_) hA)
      obtain ⟨u0, hu0⟩ := hne
      have := hE bin ⟨u0, (hfields u0 hu0).1, (hfields u0 hu0).2.2.2.2⟩
      rw [hXdef]; linarith
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.sum_empty]
      exact mul_nonneg hA (Real.rpow_nonneg hU0.le _)
  rw [anchor_fiber_sum rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness]
  calc
    _ ≤ ∑bin : BinLabel slots ((2*a-1)/2) binWidth,∑j : Label,
        ∑J : Fin (dyadicLength U),∑K : Fin (dyadicLength U),A*U^X := by
      exact Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end
end Qrh.MarkedAnchor.High
