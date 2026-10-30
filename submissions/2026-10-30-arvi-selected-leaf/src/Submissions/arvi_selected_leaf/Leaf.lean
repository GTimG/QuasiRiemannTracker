/-
The selected leaf (Seam A at the selected-leaf price).

From the parent `G(B₀,L₀,c₀)` (`GlobalSource`) and the selected root energy `SelectedRootEnergy K` (R1),
the packed leaf with price `max (K·deletionNeed) selExcess` on `[Mmin, Mmax]`, `Lplain = 4`.

Proof (Sil's `parent_priced_source`, with the deleted block split by its mass):
* the deleted block `D` is the whole slot set if the ordinary lengths alone leave the face (fallback),
  else Sil's greedy set of width `∈ [need, need+mesh]`;
* if `w(D) < smin`: Sil's argument at `3/4` (native fallback, or partial deletion and the parent);
  the excess `(3/4 - K)·smin` is paid by `ε`;
* else the packed energy is unpacked to the natural state and split by the block mass:
  rows with `mass(D) < Z^{K w(D)}` delete `D` at the cut `K` (`unselected_delete`) and the retained slots
  are bounded by the parent (or the zero-slot energy in the fallback); the other rows are R1.
-/
import Submissions.arvi_selected_leaf.Unselected
import Submissions.arvi_selected_leaf.Combine
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Parent
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeNonfixedEnergy

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QRH.ArviSelectedLeaf
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open Cycle61Moment
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
open CenteredMomentNaturalRowSource
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRayMaskedFloor
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open ConcretePrimeRowBridge
open QRH.SilDensitySplit.CubeFree
local notation "O" => HeckeFamily.O
local instance selLeafQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The `3/4`-cost of a small deleted block is paid at the cut `K` up to `(3/4)·smin`. -/
theorem small_block_cost {K need wD mesh smin : ℝ} (hK : 0 ≤ K) (hK1 : K ≤ 3/4)
    (hneed0 : 0 ≤ need) (hneed : need ≤ wD) (hwD : wD ≤ need + mesh) (hsmall : wD < smin)
    (hm : 0 ≤ mesh) :
    3/4*wD ≤ K*need + 3/4*smin + mesh := by
  have h1 : (3/4 - K)*wD ≤ (3/4)*smin := by
    have hwD0 : 0 ≤ wD := hneed0.trans hneed
    nlinarith
  have h2 : K*wD ≤ K*need + K*mesh := by nlinarith
  have h3 : K*mesh ≤ mesh := by nlinarith
  nlinarith

/-- **The selected leaf.** -/
theorem e5_priced_source (K : ℝ) (hK0 : 0 < K) (hK1 : K ≤ 3/4) (hR1 : SelectedRootEnergy K)
    (B₀ L₀ c₀ Mmin Mmax : ℝ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < L₀ ∧ 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (e5Price K B₀ L₀ c₀ hK0.le hface.1) Mmin Mmax 4 := by
  intro ε hε
  set smin : ℝ := ε/16 with hsmin
  have hsmin0 : 0 < smin := by positivity
  obtain ⟨meshN, hmeshN, hnat⟩ := native_priced_source hβ Mmin Mmax 4 h0 h1 (ε/2) (by positivity)
  have hMmax : 0 < Mmax := h0.trans_le h1
  have hden : 0 < max (1:ℝ) Mmax := zero_lt_one.trans_le (le_max_left _ _)
  have hue : 0 < (ε/4)/(max 1 Mmax) := div_pos (by positivity) hden
  obtain ⟨unitMesh, hum, hu⟩ := hparent ((ε/4)/(max 1 Mmax)) hue
  have he : Mmax*((ε/4)/(max 1 Mmax)) ≤ ε/4 := by
    calc Mmax*((ε/4)/(max 1 Mmax)) ≤ (max 1 Mmax)*((ε/4)/(max 1 Mmax)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hue.le
      _ = ε/4 := mul_div_cancel₀ _ hden.ne'
  obtain ⟨meshR, hmeshR, hR⟩ := hR1 (ε/2) (by positivity) smin Mmin (Mmax + ε/8) hsmin0 h0
    (by linarith)
  have hm₀ : 0 < min (min (min (unitMesh*Mmin) meshN) (min (ε/16) 1)) meshR :=
    lt_min (lt_min (lt_min (mul_pos hum h0) hmeshN) (lt_min (by positivity) one_pos)) hmeshR
  refine ⟨min (min (min (unitMesh*Mmin) meshN) (min (ε/16) 1)) meshR, hm₀, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q hQ hQ0 hQt hQ72
  have hm' : max 0 mesh ≤ min (min (min (unitMesh*Mmin) meshN) (min (ε/16) 1)) meshR :=
    max_le hm₀.le hmesh
  have hmU : max 0 mesh ≤ unitMesh*Mmin :=
    hm'.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hmN : mesh ≤ meshN :=
    hmesh.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hmE : max 0 mesh ≤ ε/16 :=
    hm'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm1 : max 0 mesh ≤ 1 :=
    hm'.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmR : max 0 mesh ≤ meshR := hm'.trans (min_le_right _ _)
  -- native constants (fallback with a small block)
  obtain ⟨degN, SN, CN, hCN, hevN⟩ := hnat mesh hmN α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  -- parent constants
  obtain ⟨degP, SP, CP, hCP, hevP⟩ :=
    QRH.Record1252270103Source.PhysicalParentSources.unit_source_finite_anchors (α:=α) hu
      rayM H hH W hW hWs bΦ (max 0 mesh) Mmin Mmax (ε/4) hbΦ h0 hum.le hmU hue.le he
      anchors η₀ Q hQ hQ0 hQt hQ72
  -- natural deletion at `3/4` (small blocks)
  obtain ⟨degD, CD, hCD, hdel⟩ := canonical_partial_delete rayM H hH (α:=α) W 1 2 bΦ
    (Mmax + ε/8) 1 (ε/8) (33/50) (33/50) (3/4) one_pos hWs hW (by linarith) (by positivity)
    zero_le_one (by positivity) hβ Candidate.FourthPower.IncumbentInput.native_kappa_bound
  -- zero-slot energy (fallback, unselected rows)
  haveI : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  obtain ⟨degZ, SZ, hceZ⟩ := Candidate.FourthPower.NativeNonfixedEnergy.canonical_energy
    rayM H hH (∅ : Finset α) W 1 2 (1/4) (9/4) bΦ (Mmax + ε/8) 4 1 (ε/8)
    (33/50) (33/50) (3/4) one_pos hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by positivity) zero_le_one (by positivity) hβ
    Candidate.FourthPower.IncumbentInput.native_kappa_bound (internalQ Q η₀) hQt hQ72
    (inf_le_left.trans hQ)
  obtain ⟨CZ, hCZ, hevZ⟩ := hceZ η₀ inf_le_right
  -- the selected root energy (R1)
  obtain ⟨degR, SR, CR, hCR, hevR⟩ := hR (max 0 mesh) hmR α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  refine ⟨degN + degP + degD + degZ + degR, SN ∪ SP ∪ SZ ∪ SR,
    CN + CD*CP + CP + CZ + CR, by positivity, ?_⟩
  have hanch : ∀ᶠ Z : ℝ in atTop, ∀ j, ((anchors j).modulus.absNorm : ℝ) ≤ Z^(ε/8) :=
    eventually_all.mpr (fun j =>
      (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε/8)).eventually (eventually_ge_atTop _))
  filter_upwards [hevN, hevP, hdel η₀, hevZ, hevR, hanch] with Z hZN hZP hZD hZZ hZR hZa
  intro j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V Ksc hV hKsc hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZD.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hbase : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hdg := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  set S := SN ∪ SP ∪ SZ ∪ SR with hSdef
  have hcN : p.control SN ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  have hcP : p.control SP ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  have hcZ : p.control SZ ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans Finset.subset_union_left)
  have hcR : p.control SR ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p Finset.subset_union_right
  have hctl0 (S' : Finset (ℕ×ℕ)) : 0 ≤ p.control S' := p.control_nonneg S'
  rw [e5Price_f]
  set M := Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * Ksc) with hMdef
  have hM0 : 0 ≤ M := h0.le.trans hM₁
  set Pl := length Z X₁ + length Z X₂ with hPl
  set need := deletionNeed B₀ L₀ c₀ Pl (∑ i, w i) M with hneed
  have hneed0 : 0 ≤ need := deletionNeed_nonneg _ _ _ _ _ _
  have hneeds : need ≤ ∑ i, w i := deletionNeed_le_self hs0
  set price := max (K*need) (selExcess Pl (∑ i, w i) M) with hprice
  have hKneed : K*need ≤ price := le_max_left _ _
  have hselle : selExcess Pl (∑ i, w i) M ≤ price := le_max_right _ _
  have hprice0 : 0 ≤ price := (mul_nonneg hK0.le hneed0).trans hKneed
  have hCtot : 0 ≤ CN + CD*CP + CP + CZ + CR := by positivity
  have hUpos := packed_scale_pos V hV hKsc
  have hUM : ((Ideal.span {V}).absNorm : ℝ) * Ksc = Z^M := packed_scale_eq hZ1 V hV hKsc
  let st := packedState (anchors j) (internalQ Q η₀) Φ bΦ Z
    (((Ideal.span {V}).absNorm : ℝ) * Ksc) M (ε/8) hZ1.le hM0 (by positivity) hUpos hUM hΦ
    hΦpos (hZa j)
  have hwidth : st.width ≤ Mmax + ε/8 := by
    change M + ε/8 ≤ Mmax + ε/8
    linarith
  have hw' : ∀ i, 0 ≤ extend T w 0 i := extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl
  have hwm' : ∀ i, extend T w 0 i ≤ max 0 mesh :=
    extend_forall T w 0 (fun x => x ≤ max 0 mesh) (fun i => (hwm i).trans (le_max_right _ _))
      (le_max_left _ _)
  have hσ₁' : ∀ i, (33/50:ℝ) ≤ extend T σ (33/50) i :=
    extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ₁ le_rfl
  have hσ₂' : ∀ i, extend T σ (33/50) i ≤ 33/50 :=
    extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ₂ le_rfl
  have hv' : ∀ i, |extend T v 0 i| ≤ height :=
    extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh)
  have hz := hZZ.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t height
    (fun i _ => hw' i) (fun i _ => (hwm' i).trans hm1) (fun i _ => hσ₁' i) (fun i _ => hσ₂' i) hh
    (fun i _ => hv' i) st rfl rfl hwidth ∅ (Finset.Subset.refl _) p X₁ X₂ hX₁ hX₂
    (le_rpow_of_length_le hZ1 hl₁) (le_rpow_of_length_le hZ1 hl₂)
  simp only [Finset.sum_empty, mul_zero, add_zero] at hz
  -- sublattice packing
  have hpack := Packet.packed_energy_le (anchors j) (fixedBadMask*idealGenerator 1) V hV t
    (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
    ((p.support 0).trans Set.Icc_subset_Iic_self) ((p.support 1).trans Set.Icc_subset_Iic_self)
    hX₁ hX₂ (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) (initialKeep (anchors j) (internalQ Q η₀)) Φ hΦpos Ksc hKsc
  have hsT : ∑ i ∈ T, extend T w 0 i = ∑ i, w i := sum_extend T w 0
  -- the large-block argument, for any retained set `F ⊆ T` with a bound on its energy
  have large_block : ∀ (F : Finset α), F ⊆ T → smin ≤ ∑ i ∈ T \ F, extend T w 0 i →
      ∀ (B₁ : ℝ),
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : F => primePool rayM H 2 (Z^(extend T w 0 i)))
        (fun (i : F) I => idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i)) (extend T σ (33/50) i)
            (extend T v 0 i) I)
        (fun i : F => Z^(extend T w 0 i)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale
        ≤ B₁ →
      energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ
        (((Ideal.span {V}).absNorm : ℝ) * Ksc) ≤
      CR*QuadraticInitialBound.diagonalControl Φ*(p.control SR)^2*(1+|t|+height)^degR*
        Z^(M + selExcess Pl (∑ i, w i) M + ε/2) +
      Z^(K * ∑ i ∈ T \ F, extend T w 0 i) * B₁ := by
    intro F hFT hD B₁ hB₁
    set L : O → Prop := fun z => Z^(K * ∑ i ∈ T \ F, extend T w 0 i) ≤
      blockMass rayM H hH W η₀ st.character (extend T θ 1) (extend T w 0) (extend T σ (33/50))
        (extend T v 0) t Z (T \ F) z with hLdef
    have hsplit := QRH.SilDensitySplit.Density.energy_split st.character st.mask 1 t
      (p.profile 0) (p.profile 1)
      (fun i : T => primePool rayM H 2 (Z^(extend T w 0 i)))
      (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i)) (extend T σ (33/50) i)
          (extend T v 0 i) I)
      (fun i : T => Z^(extend T w 0 i)) X₁ X₂ st.radial.keep L st.radial.profile st.radial.scale
      bΦ st.radial.scale_pos st.radial_support
    have hsel := hZR.2 j st rfl rfl hM₁ hwidth T (T \ F) Finset.sdiff_subset (extend T θ 1)
      (extend T w 0) (extend T σ (33/50)) (extend T v 0) t height hw' hwm' hσ₁' hσ₂' hh hv' hD p
      X₁ X₂ hX₁ hX₂ hl₁ hl₂
    have hun := unselected_delete rayM H hH W η₀ st rfl T F hFT (extend T θ 1) (extend T w 0)
      (extend T σ (33/50)) (extend T v 0) t K hZ0 p X₁ X₂ hX₁ hX₂
    rw [hsT] at hsel
    simp only [extend_coe] at hsplit hsel hun
    have hB := mul_le_mul_of_nonneg_left hB₁ (Real.rpow_nonneg hZ0.le (K * ∑ i ∈ T \ F, extend T w 0 i))
    change _ ≤ _ at hsel
    calc _ = energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i => primePool rayM H 2 (Z^(w i)))
          (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
          (fun i => Z^(w i)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := rfl
      _ = _ := hsplit
      _ ≤ _ := add_le_add hsel (hun.trans hB)
  have hdgΦ : QuadraticInitialBound.diagonalControl st.radial.profile =
      QuadraticInitialBound.diagonalControl Φ := rfl
  have hstw : st.width = M + ε/8 := rfl
  by_cases hfall : B₀ * M < Pl
  · ---------------- fallback: the whole slot set must be deleted
    have hneedeq : need = ∑ i, w i := deletionNeed_eq_self_of_lengths hface.1 hs0 hfall
    by_cases hsmallF : ∑ i, w i < smin
    · -- small block: the native bound at loss `ε/2`
      have hn := hZN j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V Ksc hV hKsc hM₁ hM₂ Φ hΦ hΦpos
        p X₁ X₂ hX₁ hX₂ hl₁ hl₂
      rw [nativePrice_f, max_eq_right hs0] at hn
      refine hn.trans (fit_bound hCN.le (by linarith [mul_nonneg hCD.le hCP.le]) hdg (hctl0 SN)
        hcN hbase (by omega) hZ1.le ?_)
      have h34 : 3/4*(∑ i, w i) ≤ K*need + 3/4*smin := by
        rw [hneedeq]; nlinarith
      rw [hsmin] at h34
      linarith
    · -- large block `D = T`: unselected rows delete every slot at `K`, retained = zero slots
      have hD : smin ≤ ∑ i ∈ T \ ∅, extend T w 0 i := by
        rw [Finset.sdiff_empty, hsT]; linarith
      have hlb := large_block ∅ (Finset.empty_subset _) hD _ hz
      refine hpack.trans (hlb.trans ?_)
      rw [Finset.sdiff_empty, hsT, hdgΦ, hstw]
      apply fit_add2 hdg hbase hZ1.le (C₁ := CR) (C₂ := CZ)
      · exact fit_bound hCR.le le_rfl hdg (hctl0 SR) hcR hbase (by omega) hZ1.le (by linarith)
      · exact fit_scaled hCZ.le le_rfl hdg (hctl0 SZ) hcZ hbase (by omega) hZ1.le
          (by rw [← hneedeq]; linarith)
      · linarith [mul_nonneg hCD.le hCP.le]
  · ---------------- paid deletion into the parent face
    replace hfall := not_lt.mp hfall
    obtain ⟨F, hFT, hlo, hhi⟩ := greedy_deletion T (extend T w 0) (max 0 mesh) need
      (le_max_left _ _) hneed0 (fun i _ => hw' i) (fun i _ => hwm' i) (by rw [hsT]; exact hneeds)
    have hsplit : ∑ i ∈ F, extend T w 0 i + ∑ i ∈ T \ F, extend T w 0 i = ∑ i, w i :=
      (sum_retained_add_deleted T F hFT (extend T w 0)).trans hsT
    have hF0 : 0 ≤ ∑ i ∈ F, extend T w 0 i := Finset.sum_nonneg (fun i _ => hw' i)
    have hface' := retained_in_face (del := ∑ i ∈ T \ F, extend T w 0 i) hface.1
      hface.2.2.2.le hM0 hfall hlo (by linarith)
    have hsF : ∑ i : F, extend T w 0 i = ∑ i ∈ F, extend T w 0 i :=
      Finset.sum_coe_sort F (extend T w 0)
    have hadm : (QRH.Record1252270103Source.globalFace B₀ L₀ c₀).Admissible
        (length Z X₁) (length Z X₂) (∑ i : F, extend T w 0 i) M := by
      rw [QRH.Record1252270103Source.globalFace_admissible_iff (length_nonneg Z X₁ hZ1)
        (length_nonneg Z X₂ hZ1) (by rw [hsF]; exact hF0) hface.1.le, hsF]
      have e : ∑ i ∈ F, extend T w 0 i = (∑ i, w i) - ∑ i ∈ T \ F, extend T w 0 i := by
        linarith
      rw [e]
      exact hface'
    have hp := hZP j F (fun i : F => extend T θ 1 i) (fun i : F => extend T w 0 i)
      (fun i : F => extend T σ (33/50) i) (fun i : F => extend T v 0 i) t height
      (fun i => hw' i) (fun i => hwm' i) (fun i => hσ₁' i) (fun i => hσ₂' i) hh (fun i => hv' i)
      M hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
    rw [← hUM] at hp
    have hmesh0 : max 0 mesh ≤ ε/16 := hmE
    by_cases hsmallD : ∑ i ∈ T \ F, extend T w 0 i < smin
    · -- small block: Sil's deletion at `3/4`, then the parent
      have hd := hZD.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t height
        hw' (fun i => (hwm' i).trans hm1) hσ₁' hσ₂' hh hv' 0 st rfl hwidth Q rfl hQ T F hFT
        (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
      simp only [extend_coe] at hd
      have hcost : 0 ≤ CD*(1+|t|+height)^degD*Z^(ε/8+3/4*(∑ i ∈ T \ F, extend T w 0 i)) := by
        have := (Real.rpow_pos_of_pos hZ0 (ε/8+3/4*(∑ i ∈ T \ F, extend T w 0 i))).le
        have := pow_nonneg (zero_le_one.trans hbase) degD
        positivity
      refine hpack.trans (hd.trans ((mul_le_mul_of_nonneg_left hp hcost).trans ?_))
      have hsb := small_block_cost hK0.le hK1 hneed0 hlo hhi hsmallD (le_max_left 0 mesh)
      exact fit_product hCD.le hCP.le (by linarith [mul_nonneg hCD.le hCP.le]) hdg (hctl0 SP) hcP
        hbase (by omega) hZ1.le (by rw [hsmin] at hsb; linarith)
    · -- large block: split, deletion at `K` on the unselected rows, R1 on the selected rows
      have hlb := large_block F hFT (not_lt.mp hsmallD) _ hp
      refine hpack.trans (hlb.trans ?_)
      apply fit_add2 hdg hbase hZ1.le (C₁ := CR) (C₂ := CP)
      · exact fit_bound hCR.le le_rfl hdg (hctl0 SR) hcR hbase (by omega) hZ1.le (by linarith)
      · have hKD : K * ∑ i ∈ T \ F, extend T w 0 i ≤ K*need + max 0 mesh := by
          have := mul_le_mul_of_nonneg_left hhi hK0.le
          have : K*(max 0 mesh) ≤ max 0 mesh := by nlinarith [le_max_left 0 mesh]
          nlinarith
        exact fit_scaled hCP.le le_rfl hdg (hctl0 SP) hcP hbase (by omega) hZ1.le (by linarith)
      · linarith [mul_nonneg hCD.le hCP.le]

end
end QRH.ArviSelectedLeaf
