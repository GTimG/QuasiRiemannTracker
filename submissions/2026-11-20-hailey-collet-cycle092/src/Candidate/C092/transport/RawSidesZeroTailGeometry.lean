/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Q's actual ordered box supplies the strict volume/cap collar used in H.5. -/
import Candidate.C092.transport.RawSidesZeroTailQ
import Candidate.C092.transport.MeasuredBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RawSides
noncomputable section
local instance (priority := 2000) instDecEqZT {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentEnergyBands
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedFirstRemainder
open MixedPrincipalAllocations MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle090 QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- The original source volume, not a replacement count or coefficient mass. -/
theorem root_volume_of_box {ι : Type} [Fintype ι] {a b Z n y : ℝ}
    (s : Source ι a b) (w : ι → ℝ) (hP : ∀ i, s.P i = Z^(w i)) (hZ : 1 < Z)
    (hy : sourceY0 ≤ y) (hy' : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (hbox : Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑ i,w i)) :
    sourceVolume s ≤ Z^(9179599/10000000:ℝ) := by
  have hX₁ : 0 < s.X₁ := s.hL.trans_le s.hX₁
  have hX₂ : 0 < s.X₂ := s.hL.trans_le s.hX₂
  have h := QRH.Cycle092.MeasuredBall.support_cap hZ hX₁ hX₂ hy hy' hn hbox
  simpa only [sourceVolume, hP, ← Real.rpow_sum_of_pos (zero_lt_one.trans hZ)] using h

/-- A true allocation cannot have zero common factor. -/
theorem allocation_common_ne_zero {ι : Type} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G) : G ≠ 0 := by
  have hprod := (Finset.mem_filter.mp B.property).2
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  rw [← hprod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hB i)

/-- All actual allocated and selected residuals have normalized volume at
    most the original root volume times the fixed slot collar. -/
theorem allocated_residual_volume {ι : Type} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    sourceVolume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm
      (restOf s hb cover G B J)) ≤ (2:ℝ)^(Fintype.card ι)*sourceVolume s := by
  let r := allocatedLiveSource s hb cover G B
  have hr := QRH.SilDensitySplit.CubeFree.Second.Provider.rest_volume_mul r (fun _ => rfl) J
  have hp : 1 ≤ ∏ j : J, r.P j.val := Finset.one_le_prod₀ (fun j _ => r.hP j.val)
  have hv : 0 ≤ sourceVolume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm (restSource r (fun _ => rfl) J)) :=
    (sourceVolume_pos _).le
  have hle : sourceVolume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm (restOf s hb cover G B J)) ≤
      sourceVolume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm r) := by
    exact (le_mul_of_one_le_right hv hp).trans_eq hr
  have hG : 1 ≤ (G.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (allocation_common_ne_zero s G B))
  have hl := QRH.SilDensitySplit.CubeFree.Second.Provider.live_volume_le s hb cover G B
  exact hle.trans ((le_mul_of_one_le_right (sourceVolume_pos _).le hG).trans hl)

/-- The original ordered root controls every allocated residual source norm
    cap. The collar `.919` is strict above Q's `.9179599`, and below one. -/
theorem allocated_residual_caps_Q (N : ℕ) : ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type) [Fintype ι] (s : Source ι (1/4) (9/4)), Fintype.card ι ≤ N →
    ∀ (cover : OriginalEnclosure s) (w : ι → ℝ) (hP : ∀ i, s.P i = Z^(w i)) (n y : ℝ),
      sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑ i,w i) →
      sourceVolume s < Z ∧
      ∀ (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)),
        sourceNormCap (restOf s (by norm_num) cover G B J).P (9/4)
          (restOf s (by norm_num) cover G B J).T (restOf s (by norm_num) cover G B J).d ≤ Z^(919/1000:ℝ) := by
  let D : ℝ := Real.exp (supportHeight N (9/4)) * 2^N
  have hδ : (0:ℝ) < 919/1000-9179599/10000000 := by norm_num
  filter_upwards [eventually_gt_atTop (1:ℝ), (tendsto_rpow_atTop hδ).eventually_ge_atTop D]
    with Z hZ hD
  refine ⟨hZ,?_⟩
  intro ι _ s hN cover w hP n y hy hy' hn hbox
  have hV := root_volume_of_box s w hP hZ hy hy' hn hbox
  have hZ0 := zero_lt_one.trans hZ
  have hroot : sourceVolume s < Z := hV.trans_lt (by
    calc Z^(9179599/10000000:ℝ) < Z^(1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hZ (by norm_num)
      _ = Z := Real.rpow_one Z)
  refine ⟨hroot,?_⟩
  intro G B J
  let r := restOf s (by norm_num) cover G B J
  have hcard : Fintype.card (Rest J) ≤ N := by
    refine (Fintype.card_le_of_injective (fun j : Rest J => j.val.val) ?_).trans hN
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hc := source_cap_volume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm r) N hcard
  rw [QRH.SilDensitySplit.CubeFree.Second.Provider.sourceNormCap_renorm] at hc
  have hv := allocated_residual_volume s (by norm_num) cover G B J
  have h2N : (2:ℝ)^(Fintype.card ι) ≤ 2^N := pow_le_pow_right₀ (by norm_num) hN
  have hv' : sourceVolume (QRH.SilDensitySplit.CubeFree.Second.Provider.renorm r) ≤ 2^N*Z^(9179599/10000000:ℝ) :=
    hv.trans (mul_le_mul h2N hV (sourceVolume_pos _).le (by positivity))
  refine hc.trans ((mul_le_mul_of_nonneg_left hv' (Real.exp_pos _).le).trans ?_)
  calc
    _ = D * Z^(9179599/10000000:ℝ) := by dsimp [D]; ring
    _ ≤ Z^((919/1000:ℝ)-9179599/10000000) * Z^(9179599/10000000:ℝ) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ0]; norm_num

/-- The literal selected radius multiplier is controlled before selecting a
    subset, uniformly over all actual whole-slot subsets of a fixed type. -/
theorem selected_width_Q (N : ℕ) : ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type) [Fintype ι] (w : ι → ℝ), Fintype.card ι ≤ N → (∀ i, 0 ≤ w i) →
    ∀ J : Finset ι, (∑ j ∈ J,w j) ≤ 3/5000 →
      1 ≤ ∏ j ∈ J, 2*Z^(w j) ∧ (∏ j ∈ J, 2*Z^(w j)) ≤ Z^(1/1000:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show (0:ℝ) < 1/1000-3/5000 by norm_num)).eventually_ge_atTop ((2:ℝ)^N)]
    with Z hZ hNpow
  refine ⟨hZ,?_⟩
  intro ι _ w hN hw J hJ
  have hZ0 := zero_lt_one.trans hZ
  have hj : J.card ≤ N := (Finset.card_le_univ J).trans hN
  constructor
  · apply Finset.one_le_prod₀
    intro j _
    have := Real.one_le_rpow hZ.le (hw j)
    linarith
  · calc
      _ = (2:ℝ)^J.card * Z^(∑ j ∈ J,w j) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,← Real.rpow_sum_of_pos hZ0]
      _ ≤ (2:ℝ)^N * Z^(3/5000:ℝ) := mul_le_mul (pow_le_pow_right₀ (by norm_num) hj)
        (Real.rpow_le_rpow_of_exponent_le hZ.le hJ) (by positivity) (by positivity)
      _ ≤ Z^((1/1000:ℝ)-3/5000)*Z^(3/5000:ℝ) := mul_le_mul_of_nonneg_right hNpow (by positivity)
      _ = _ := by rw [← Real.rpow_add hZ0]; norm_num

/-- The original allocation and whole-slot deletion cannot increase the
    underlying finite source pool cap. -/
theorem allocated_residual_pool_le {ι : Type} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    poolCap (restOf s hb cover G B J) ≤ poolCap s := by
  have hr := rest_pool_cap_le (allocatedLiveSource s hb cover G B) (fun _ => rfl) J
  have hl := MixedFirstAllocatedRemainders.live_pool_cap_le (allocationSource s hb cover G B)
  exact hr.trans hl

/-- Total original logarithmic support, including the real ordinary lengths. -/
theorem box_total_cap {n y x z S : ℝ} (hy : sourceY0 ≤ y) (hy' : y ≤ sourceY)
    (hn : n ≤ sourceRatio*y) (hbox : Box n y (sourceWidth n y) x z S) :
    x+z+S ≤ 9179599/10000000 := by
  obtain ⟨_,_,hp,_,hs⟩ := hbox
  have hg := QRH.Cycle092.Source.sourceGain_quarter_secant hy hy' le_rfl
  rw [source_native_value] at hg
  unfold sourceWidth at hs
  norm_num [sourceY,sourceRatio] at hg hn hy'
  rcases hp with ⟨_,_⟩ | ⟨_,_⟩ <;> linarith

/-- Both original signed rectangles bound the finite source pool uniformly.
    No coefficient or energy majorant is used to obtain this cap. -/
theorem root_pool_of_boxes (N : ℕ) : ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type) [Fintype ι] (s : Source ι (1/4) (9/4)), Fintype.card ι ≤ N →
    ∀ (w : ι → ℝ), (∀ i,0 ≤ w i) → (∀ i,s.P i = Z^(w i)) →
    ∀ n y : ℝ, sourceY0 ≤ y → y ≤ sourceY → n ≤ sourceRatio*y →
      Box n y (sourceWidth n y) (length Z s.X₁) (length Z s.X₂) (∑ i,w i) →
      Box n y (sourceWidth n y) (length Z s.Y₁) (length Z s.Y₂) (∑ i,w i) →
      poolCap s ≤ Z^(8:ℝ) := by
  filter_upwards [MixedOriginalTailCaps.eventually_source_caps N (9/4) 1 1 1 (by norm_num)]
    with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hN w hw hP n y hy hy' hn hbX hbY
  have hZ0 := zero_lt_one.trans hZ.1
  have hS : 0 ≤ ∑ i,w i := Finset.sum_nonneg (fun i _ => hw i)
  have hx := box_total_cap hy hy' hn hbX
  have hyb := box_total_cap hy hy' hn hbY
  have hlen (X : ℝ) : X ≤ Z^length Z X := by
    rw [length,Real.rpow_logb hZ0 hZ.1.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hpow (X : ℝ) (hh : length Z X ≤ 1) : X ≤ Z^(1:ℝ) :=
    (hlen X).trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hh)
  have hX₁ := hpow s.X₁ (by linarith [hbX.1,hbX.2.1])
  have hX₂ := hpow s.X₂ (by linarith [hbX.1,hbX.2.1])
  have hY₁ := hpow s.Y₁ (by linarith [hbY.1,hbY.2.1])
  have hY₂ := hpow s.Y₂ (by linarith [hbY.1,hbY.2.1])
  have hProd : ∏ i,s.P i ≤ Z^(1:ℝ) := by
    simp_rw [hP]
    rw [← Real.rpow_sum_of_pos hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hbX.1,hbX.2.1])
  have hc := hZ.2 ι (1/4) s hN hX₁ hX₂ hY₁ hY₂ hProd
  exact hc.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by norm_num))

#print axioms allocated_residual_pool_le
#print axioms box_total_cap
#print axioms root_pool_of_boxes
#print axioms root_volume_of_box
#print axioms allocation_common_ne_zero
#print axioms allocated_residual_volume
#print axioms allocated_residual_caps_Q
#print axioms selected_width_Q
end
end QRH.Cycle092.RawSides
