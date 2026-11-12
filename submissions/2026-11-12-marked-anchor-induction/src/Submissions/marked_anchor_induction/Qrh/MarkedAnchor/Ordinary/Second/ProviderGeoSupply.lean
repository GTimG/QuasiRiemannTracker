/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: the geometric supplier `GeoSupply G` from `geometryAt_left/right`
(`ProviderGeometry7`), with `cb = 19`, `Bmask = 24`, `ξr = mesh`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderFinal
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry7

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSectorLocalization
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentNaturalFixedRaySource
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedFirstCommonSum
open MixedFirstExceptionalWindow MixedFirstRetainedFixed MixedFirstLiveSource
open RepairedRawContext RepairedSourceSideSupply Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderGS {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

theorem rootReserve_le_one {D : StepData} (G : StepGates D) : rootReserve G ≤ 1 := by
  unfold rootReserve
  have := min_le_right (min G.refReserve (1 - D.B)) (1/100)
  have h0 := (rootReserve_spec G).1
  unfold rootReserve at h0
  linarith

/-- **The geometric supplier holds.** -/
theorem geoSupply_holds {D : StepData} (G : StepGates D) : GeoSupply G := by
  intro ε hε meshF hm0 hmF α _ _ M _ H hH W hW hWs bΦ hbΦ η η₀ Q _ hQt hQ72 hQM hQη
  refine ⟨19, 24, by norm_num, by norm_num, ?_⟩
  set N := Fintype.card α
  filter_upwards [ProviderGeometry.eventually_bigZ G N ε hε N (64 * 16^N) (by positivity),
    ProviderGeometry.eventually_hZc N meshF hm0] with Z hb hc
  intro k d hK hmesh p E hE n hn
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hcκ : Fintype.card (RootSlot k) ≤ N := root_slot_card k
  have hcf := first_label_cubeFree d.root (by norm_num) p
  have hparts := first_label_parts d.root (by norm_num) p
  have h8 := first_label_norm d.root (by norm_num) _ (root_columns_le d) p
  have hn' : (n 1).val ∈ retainedIndices
      (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G N ε)) := (n 1).property
  have hξ : meshF ≤ 2 := by
    have := (mesh_spec G ε hε).2.1
    have := rootReserve_le_one G
    linarith
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hsC := commonLabels_supported (activeSource (sourceColumns d.root)
    (sourceCoefficient d.root (by norm_num : (0:ℝ) < 1/4) 1)) p
  have hZc' : 32 * ((9/4:ℝ)^2 * 2^(Fintype.card (RootSlot k)))^2 * Z^(meshF/2) ≤ Z^meshF := by
    refine le_trans ?_ hc
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_right₀ (by norm_num) hcκ
  have hZ1' : Real.logb Z (64 * 16^(Fintype.card (RootSlot k))) ≤ cutoffLoss G N ε / 2 := by
    refine le_trans ?_ hb1
    apply Real.logb_le_logb_of_le hZ1 (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcκ) (by norm_num)
  have hZ2' : 2 * (Fintype.card (RootSlot k) : ℝ) * Real.logb Z 2 ≤ rootReserve G := by
    refine le_trans ?_ hb2
    have hx0 : 0 ≤ Real.logb Z 2 := Real.logb_nonneg hZ1 (by norm_num)
    have : (Fintype.card (RootSlot k) : ℝ) ≤ N := by exact_mod_cast hcκ
    nlinarith
  have hZ4' : (81/16:ℝ) * 4^(Fintype.card (RootSlot k)) ≤ Z := by
    refine le_trans ?_ hb4
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcκ) (by norm_num)
  refine ⟨?_, ?_⟩
  · exact ProviderGeometry.geometryAt_left d hW hWs bΦ hbΦ Q hQM (iq_ne_zero Q η₀)
      (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀) hε 24 (by norm_num) (by norm_num) meshF hm0.le hmesh
      hmF p.val.1 p.val.2 hsC.1 hsC.2 E hcf hparts.1 hparts.2 h8.1 (n 1) hn' hn meshF 19 hξ (by norm_num)
      hZc' (cutoffLoss_le_hmin G N ε) hZ1' hZ2' hb3 hZ4' (by norm_num)
  · exact ProviderGeometry.geometryAt_right d hW hWs bΦ hbΦ Q hQM (iq_ne_zero Q η₀)
      (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀) hε 24 (by norm_num) (by norm_num) meshF hm0.le hmesh
      hmF p.val.1 p.val.2 hsC.1 hsC.2 E hcf hparts.1 hparts.2 h8.2 (n 1) hn' hn meshF 19 hξ (by norm_num)
      hZc' (cutoffLoss_le_hmin G N ε) hZ1' hZ2' hb3 hZ4' (by norm_num)

theorem cutoffLoss_unit {D : StepData} (G : StepGates D) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ cutoffLoss G N ε ∧ cutoffLoss G N ε ≤ 1 := by
  have h1 := internal_spec G N ε hε
  have h2 := omega_spec G ε hε
  unfold cutoffLoss
  constructor
  · have := h1.1; positivity
  · linarith [h1.2.2.1, h2.2.2.2]

set_option maxHeartbeats 4000000 in
/-- **The contrary raw side provider**, from the step leaf and the diagonal supplier. -/
theorem contrary_raw_side_provider {D : StepData} (G : StepGates D) (Lplain : ℝ) (hL : 4 ≤ Lplain)
    (hleaf : PricedPackedSource D.price D.Hmin (D.Hmax + 1) Lplain) (hdiag : DiagSupply G) :
    ContraryRawSideProvider G := by
  intro hβ ε hε
  obtain ⟨hlarge, hsmall⟩ := frame_leaves G Lplain hL hleaf hβ
  obtain ⟨meshMax, hmM, hsplit⟩ := split_bound_late D G 3 (by norm_num) hlarge hsmall ε hε
  refine ⟨meshMax, hmM, ?_⟩
  intro α _ _ M _ H hH W hW hWs bΦ hbΦ η η₀ Q _ hQt hQ72 hQM hQη N Kslot
  set meshF := min (mesh G ε) meshMax with hmeshF
  have hmF0 : 0 < meshF := lt_min (mesh_spec G ε hε).1 hmM
  have hmFle : meshF ≤ mesh G ε := min_le_left _ _
  have hmFM : meshF ≤ meshMax := min_le_right _ _
  obtain ⟨J₀, ctl₀, C₀, hdZ⟩ :=
    hdiag ε hε meshF hmF0 hmFle α M H hH W hW hWs bΦ hbΦ η η₀ Q hQt hQ72 hQM hQη
  obtain ⟨cb, Bmask, hcb, hBmask, hgZ⟩ :=
    geoSupply_holds G ε hε meshF hmF0 hmFle α M H hH W hW hWs bΦ hbΦ η η₀ Q hQt hQ72 hQM hQη
  have hspl : ∀ n : ℕ, ∃ J : ℕ, ∃ control : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ cb : ℝ, 0 ≤ cb →
      ∀ᶠ Z : ℝ in atTop, SplitBoundAt D G (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM
        (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀) (iq_le72 Q hQ72 η₀) (2 * N) N ε hε Bmask hBmask n)
        meshF η Z ε cb J control C :=
    fun n => hsplit meshF hmF0 hmFM _ η
  choose Jf ctl Cf hCf0 hev using hspl
  obtain ⟨Cm, hCm, hdivm⟩ := Packet.Fibre.divisor_power_subpower N 40 (ε/8) (by norm_num)
    (by positivity)
  obtain ⟨Cδ, hCδ, hms⟩ := ConcreteLabelAssembly.mult_subpower 4 (ε/8) (by norm_num) (by positivity)
  obtain ⟨Ca, hCa, hdiva⟩ := Packet.Fibre.divisor_power_subpower (N+2) 8 (ε/8) (by norm_num)
    (by positivity)
  set Jmax := (Finset.range (N+1)).sup Jf
  set ctlU := (Finset.range (N+1)).biUnion ctl
  set Cmax := ∑ n ∈ Finset.range (N+1), Cf n
  set Jt := max Jmax J₀
  set control : Finset (ℕ × ℕ) := ctlU ∪ ctl₀ ∪ {((0:ℕ), (0:ℕ))}
  set Cside := max (max 1 C₀) (labelSide Kslot Ca Cm Cmax N)
  have hCmax : 0 ≤ Cmax := Finset.sum_nonneg fun n _ => (hCf0 n).le
  have hside0 : 0 ≤ Cside := zero_le_one.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨Jt, control, Cside, (le_max_left _ _).trans (le_max_left _ _), by simp [control], ?_⟩
  have hev' : ∀ᶠ Z : ℝ in atTop, ∀ n ∈ Finset.range (N+1), SplitBoundAt D G
      (thetaOf G M H hH W hW hWs bΦ hbΦ η₀ Q hQM (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀)
        (iq_le72 Q hQ72 η₀) (2 * N) N ε hε Bmask hBmask n) meshF η Z ε cb (Jf n) (ctl n) (Cf n) :=
    (Filter.eventually_all_finset _).mpr (fun n _ => hev n cb hcb)
  have hε8 : 0 < ε/8 := by positivity
  have ev64 : ∀ᶠ Z : ℝ in atTop, 64 * (16:ℝ)^N ≤ Z^(4:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4)).eventually_ge_atTop _
  have evMc : ∀ᶠ Z : ℝ in atTop, max Cm 1 * Z^(ε/8) ≤ Z^(ε/4) := by
    filter_upwards [(tendsto_rpow_atTop hε8).eventually_ge_atTop (max Cm 1),
      eventually_gt_atTop (0:ℝ)] with Z h h0
    have e : Z^(ε/4) = Z^(ε/8) * Z^(ε/8) := by rw [← Real.rpow_add h0]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg h0.le _)
  have evMm : ∀ᶠ Z : ℝ in atTop, ((⌈Cδ * Z^(ε/8)⌉₊ : ℕ) : ℝ) ≤ Z^(ε/2) := by
    filter_upwards [(tendsto_rpow_atTop (by positivity : (0:ℝ) < 3*ε/8)).eventually_ge_atTop
      (Cδ + 1), (tendsto_rpow_atTop hε8).eventually_ge_atTop 1, eventually_gt_atTop (0:ℝ)]
      with Z h3 h1 h0
    have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ Cδ * Z^(ε/8))).le
    have e : Z^(ε/2) = Z^(ε/8) * Z^(3*ε/8) := by rw [← Real.rpow_add h0]; ring_nf
    rw [e]
    nlinarith
  filter_upwards [hdZ Jt control Cside (le_max_right _ _)
      (fun x hx => by simp [control, hx]) ((le_max_right 1 C₀).trans (le_max_left _ _)),
    hgZ, hev', eventually_ge_atTop (5:ℝ), ev64, evMc, evMm] with Z hd hg hsp hZ5 h64 hMcZ hMmZ
  refine ⟨hZ5, ?_⟩
  intro k d hK hw
  have hZ1 := d.one_lt_Z
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hmesh : ∀ i, d.w i ≤ meshF := fun i => le_min (d.hwm i) (hw i)
  have hcκ : Fintype.card (RootSlot k) ≤ N := root_slot_card k
  have hZbig : 64 * (16:ℝ)^(Fintype.card (RootSlot k)) ≤ Z^(4:ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcκ) (by norm_num)) h64
  obtain ⟨hκ0, hκ1⟩ := cutoffLoss_unit G N ε hε
  apply supplyFor_of_blockData d Jt control Cside
  intro p E hE n hn
  have hsC := commonLabels_supported (activeSource (sourceColumns d.root)
    (sourceCoefficient d.root (by norm_num : (0:ℝ) < 1/4) 1)) p
  have hdat := commonLabels_data _ _ p.val.1 p.val.2 p.property
  have hn1 : (n 1).val ∈ retainedIndices
      (firstRadius d.root p.val.1 p.val.2 E d.Kroot Z (cutoffLoss G N ε)) := (n 1).property
  have hK0 : 0 < childScale Z (cutoffLoss G N ε) (n 1) := Real.rpow_pos_of_pos hZ0 _
  have hJcard : ∀ (C' : Id) (B : actualAllocations (tuplePools d.root) C'),
      Fintype.card (selOf d hε meshF hmF0.le hmesh C' B) ≤ N := fun C' B =>
    (Fintype.card_le_of_injective (fun j : selOf d hε meshF hmF0.le hmesh C' B => j.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)).trans hcκ
  have hML := multBound_of_divisor N 40 (ε/8) Cm Z hZ1.le hε8 (hdivm Z hZ1.le) d.root
    (by norm_num) d.cover p.val.1 (selOf d hε meshF hmF0.le hmesh p.val.1)
    (childScale Z (cutoffLoss G N ε) (n 1))
    (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.1 B)
      (selOf d hε meshF hmF0.le hmesh p.val.1 B)) (hJcard p.val.1)
    (fun B => block_Kc_le d (by norm_num) p E _ hκ0 hκ1 (n 1) hn1 p.val.1 B _ hZbig)
  have hMR := multBound_of_divisor N 40 (ε/8) Cm Z hZ1.le hε8 (hdivm Z hZ1.le) d.root
    (by norm_num) d.cover p.val.2 (selOf d hε meshF hmF0.le hmesh p.val.2)
    (childScale Z (cutoffLoss G N ε) (n 1))
    (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover p.val.2 B)
      (selOf d hε meshF hmF0.le hmesh p.val.2 B)) (hJcard p.val.2)
    (fun B => block_Kc_le d (by norm_num) p E _ hκ0 hκ1 (n 1) hn1 p.val.2 B _ hZbig)
  have hMc0 : 0 ≤ max Cm 1 * Z^(ε/8) := by
    have := le_max_right Cm 1; have := Real.rpow_nonneg hZ0.le (ε/8); positivity
  have hA := amplitude_nonneg d.root d.t₀ d.V d.hV Jt control Cside hside0
  have hDH := hd k d hK hmesh p E hE n hn (max Cm 1 * Z^(ε/8)) hMc0 hMcZ hML hMR
  have h8 := first_label_norm d.root (by norm_num) _ (root_columns_le d) p
  have hparts := first_label_parts d.root (by norm_num) p
  have hLH := labelHalf_of_rootInput d hW hWs bΦ hbΦ Q hQM (iq_ne_zero Q η₀) (iq_ne_top Q hQt η₀)
    (iq_le72 Q hQ72 η₀) hε Bmask hBmask meshF hmF0.le hmesh p.val.1 p.val.2 hsC.1 hsC.2 E
    (childScale Z (cutoffLoss G N ε) (n 1)) hK0 meshF (max Cm 1 * Z^(ε/8)) hML hMR cb Jf ctl Cf
    Jt control Cmax
    (fun n' hn' => (Finset.le_sup (Finset.mem_range.mpr (by omega))).trans (le_max_left _ _))
    (fun n' hn' x hx => by
      have : x ∈ ctlU := Finset.mem_biUnion.mpr ⟨n', Finset.mem_range.mpr (by omega), hx⟩
      simp [control, this])
    (fun n' hn' => ⟨(hCf0 n').le, Finset.single_le_sum (fun i _ => (hCf0 i).le)
      (Finset.mem_range.mpr (by omega))⟩)
    (fun n' hn' => hsp n' (Finset.mem_range.mpr (by omega))) (by norm_num)
    (hg k d hK hmesh p E hE n hn).1 (hg k d hK hmesh p E hE n hn).2 Cδ (ε/8) (hms Z hZ1.le) hMmZ
    N (hJcard p.val.1) (hJcard p.val.2) (first_label_cubeFree d.root (by norm_num) p)
    hparts.1 hparts.2 (amplitude d.root d.t₀ d.V Jt control Cside) (3*ε) (1/2)
    (labelConst_final d hε p.val.1 hdat.1 h8.1 hcκ Ca Cm Cmax hCa.le hCmax hdiva Jt control Cside
      (le_max_right _ _))
    (labelConst_final d hε p.val.2 hdat.2.1 h8.2 hcκ Ca Cm Cmax hCa.le hCmax hdiva Jt control Cside
      (le_max_right _ _))
    (by norm_num) hA
  exact blockData_of_halves d.root (by norm_num) (by norm_num) d.cover η p.val.1 p.val.2 hsC.1 hsC.2
    (first_label_support d.root (by norm_num) p) E (childScale Z (cutoffLoss G N ε) (n 1))
    (amplitude d.root d.t₀ d.V Jt control Cside) Z (3*ε) Jt hA hZ0.le _ (1/2) (1/2) (by norm_num)
    hDH hLH

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
