/- Copyright (c) 2026 Joseph Bebel.
Selected-energy adapter for every fixed positive gap above one half.
The aggregate and actual-slot templates are adapted from Joseph Bebel's PR97
FineSlotHistogram and FineActualSelectedNorm. The final capped-energy wrapper
is adapted from ArviFoxy's PR97 R1/Cap at
62b12e08066b0269a01f34696ace896e3cb5eb32. Existing analytic lemmas are imported.
The adapter preserves the original slot, mask and early-mesh quantifiers.
-/
import Submissions.arvi_selected_leaf.JointDetector.FineSlotHistogram
import Submissions.arvi_selected_leaf.JointDetector.FineActualSelectedNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalUniformNear
import Submissions.arvi_selected_leaf.R1.Cap

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Qrh.JointDetector.SelectedGap
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentEnergyState
open CanonicalRowCompletion ConcreteTraceCRT ProbeHighRowFamily
open FineDetectorWords FineSlotHistogram
local notation "O" => ActualEisensteinCubic.O

def AggregateSlotNormAt (gap : ℝ) : Prop :=
  ∀ A P loss : ℝ, 0 < A → 3*A+1 ≤ P → 0 < loss →
  ∃ mesh₀ : ℝ, 0 < mesh₀ ∧ ∀ (N : ℕ) (Cslot smin : ℝ),
    1 ≤ Cslot → 0 < smin → ∃ C Z₀ : ℝ, 0 < C ∧
    ∀ Z mesh δ : ℝ, Z₀ ≤ Z → 0 ≤ mesh → mesh ≤ mesh₀ →
      1/2+gap ≤ δ → δ ≤ 3/4 →
      FineNaturalAggregateNormBound N Z A P mesh Cslot smin δ (C*Z^loss)


def ActualSelectedSlotNormAt (gap : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss P_requested : ℝ,
    0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss → 0 ≤ P_requested →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (δ Y : ℝ) (root : HeckeInverseAmplification.NonzeroIdeal) (cores : Finset FreeRow),
    δ ∈ Icc (1/2+gap : ℝ) (3/4) → Z^(Mmin/20) ≤ Y → Y ≤ bΦ*Z^st.rowWidth →
    (∀ u ∈ cores, rowNorm u ≤ Y ∧
      ∃ hz : st.radial.keep (rowMap (u,root)),
        st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
        Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) →
    SelectedAllSourceNormBound (cores.image Subtype.val) Y δ (C*Z^loss)
      (Z^(detectorAuxiliarySourceCap P_requested (Mcap+1)))


theorem aggregate_of_cell (gap : ℝ) (hgap : 0 < gap) (hgap_half : gap < 1/2)
    (hcell : NaturalSelectedCellNorm) : AggregateSlotNormAt gap := by
  intro A P loss hA hP hloss
  let β : ℝ := min (gap/4) (loss/(8*(A+1)))
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ gap/4 := min_le_left _ _
  have hβ2 : β ≤ loss/(8*(A+1)) := min_le_right _ _
  have hβ : β ∈ Set.Icc (0:ℝ) (1/8) := ⟨hβ0.le,by linarith⟩
  have hexp : loss/4+A*β ≤ loss := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(A+1))).mp hβ2
    nlinarith
  obtain ⟨mesh₀,hmesh₀,hnorm⟩ := hcell A P (gap/2) (loss/4)
    hA hP (by positivity) (by linarith) (by positivity)
  refine ⟨min 1 mesh₀,lt_min zero_lt_one hmesh₀,?_⟩
  intro N Cslot smin hCslot hsmin
  obtain ⟨Cn,Zn,hCn,hnorm⟩ := hnorm N Cslot (smin/4) (by linarith) (by positivity)
  let step : ℝ := min (β*smin/(N+1)) (1/2)
  have hstep0 : 0 < step := by dsimp [step]; positivity
  have hstep1 : step ≤ 1/2 := min_le_right _ _
  have hstepU : step ≤ β*smin/(N+1) := min_le_left _ _
  have hbudget : (N:ℝ)*step ≤ β*smin := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < N+1)).mp hstepU
    nlinarith
  let n : ℕ := ⌈2/step⌉₊
  have hn : (2:ℝ) ≤ (n:ℝ)*step :=
    (div_le_iff₀ hstep0).mp (Nat.le_ceil (2/step))
  let D : ℝ := Fintype.card (Fin N → Fin (n+1))
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Fintype.card_pos
  refine ⟨D*Cn,max 2 (max Zn ((256*Cslot)^(1/step))),mul_pos hD hCn,?_⟩
  intro Z mesh δ hZ hm hmU hδ hδU
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZ
  have hZ1 : 1 < Z := by linarith
  have hZn : Zn ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hRoot : (256*Cslot)^(1/step) ≤ Z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hconst : 0 < 256*Cslot := by linarith
  have hCpower : 256*Cslot ≤ Z^step := by
    calc
      _ = ((256*Cslot)^(1/step))^step := by
        rw [← Real.rpow_mul hconst.le,div_mul_cancel₀ _ hstep0.ne',Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hconst.le _) hRoot hstep0.le
  have hm1 : mesh ≤ 1 := hmU.trans (min_le_left _ _)
  have hδcell : 1/2+(gap/2:ℝ) ≤ δ-β := by linarith
  have hδcellU : δ-β ≤ 3/4 := by linarith
  have hnrm := hnorm Z mesh (δ-β) hZn hm (hmU.trans (min_le_right _ _)) hδcell hδcellU
  intro d cores S Y L hd hs hresponse hY hYU hcores hL hLU hS
  have hupper (i : Fin N) (z : O) : ‖d.polynomial i z‖^2 ≤ Z^(d.width i+step) := by
    calc
      _ ≤ 256*Cslot*Z^(d.width i) := slot_polynomial_upper d Z mesh Cslot hZ1.le (by linarith) hd i z
      _ ≤ Z^step*Z^(d.width i) :=
        mul_le_mul_of_nonneg_right hCpower (Real.rpow_nonneg (by linarith : 0 ≤ Z) _)
      _ = _ := by rw [← Real.rpow_add (by linarith : 0 < Z)]; congr 1; ring
  have hh := finite_aggregate_norm d cores S Z A P mesh Cslot smin δ β step Y L (Cn*Z^(loss/4))
    hZ1 hA.le hm hm1 hCslot hd hsmin hs (by linarith) hβ (by linarith [hδcell])
    ⟨hstep0.le,by linarith⟩ hbudget hn hupper hresponse hY hYU hcores hL hLU hS
    (by positivity) hnrm
  apply hh.trans
  have hpower := Real.rpow_le_rpow_of_exponent_le hZ1.le hexp
  have hp : Z^(loss/4)*Z^(A*β) ≤ Z^loss := by
    rwa [← Real.rpow_add (by linarith : 0 < Z)]
  have hmul := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ D*Cn*(L+Y^(1-δ)*L^δ) by positivity)
  dsimp [D] at hmul ⊢
  nlinarith


theorem actual_of_aggregate (gap : ℝ) (hagg : AggregateSlotNormAt gap) :
    ActualSelectedSlotNormAt gap := by
  intro Mmin Mcap smin loss P_requested hMmin hMc hsmin hloss hPreq
  let A : ℝ := Mcap+1
  let P : ℝ := detectorAuxiliarySourceCap P_requested A
  have hMcap : 0 < Mcap := hMmin.trans_le hMc
  have hA : 0 < A := by dsimp [A]; linarith
  have hP : 3*A+1 ≤ P := by
    dsimp [P,detectorAuxiliarySourceCap]
    simpa only [add_comm] using add_le_add_right (le_max_right P_requested (3*A)) (1:ℝ)
  obtain ⟨mesh₀,hm₀,haggregate⟩ := hagg A P loss hA hP hloss
  refine ⟨mesh₀,hm₀,?_⟩
  intro mesh hm α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Cslot,hCslot,hslots⟩ := ActualSlotData.data_bounded W hW.continuous hWs
  obtain ⟨C,Z₀,hC,hbound⟩ := haggregate (Fintype.card α) Cslot smin hCslot hsmin
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop bΦ,
    eventually_gt_atTop (1:ℝ)] with Z hZZ₀ hΦZ hZ
  refine ⟨hZ,?_⟩
  intro j st hchar hpuncture hMlower hMupper T θ w σ v t height
    hw hwm hσlo hσhi hheight hv hs δ Y root cores hδ hYlo hYhi hcores
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hmpos : 0 ≤ mesh := by
    by_contra hh
    have hh' : mesh ≤ 0 := le_of_lt (lt_of_not_ge hh)
    have hs0 : (∑ k,w k) ≤ 0 := Finset.sum_nonpos (fun k _ => (hwm k).trans hh')
    linarith
  let d := ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
  have hd : d.Bounded Z mesh Cslot :=
    hslots α rayM H hH Z bΦ st η₀ T θ w σ v (fun _ => 0) t root mesh hZ hmpos hw hwm
      (fun k => ⟨hσlo k,hσhi k⟩)
  have hwidth : ∑ i,d.width i = ∑ k,w k :=
    ActualSlotData.data_width rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
  have hresponse : ∀ u ∈ cores,Z^(δ*∑ i,d.width i) ≤ ∏ i,‖d.polynomial i u.val‖^2 := by
    intro u hu
    obtain ⟨hz,hprofile,hamp⟩ := (hcores u hu).2
    simpa only [d,ActualSlotData.data_width,ActualSlotData.data_mass] using hamp
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hZ.le (by positivity : 0 ≤ Mmin/20)).trans hYlo
  have hrow : st.rowWidth ≤ Mcap := by
    have hh : st.rowWidth ≤ st.width := by
      dsimp [NaturalState.width]
      linarith [st.character_nonneg]
    exact hh.trans hMupper
  have hYA : Y ≤ Z^A := by
    calc
      Y ≤ bΦ*Z^st.rowWidth := hYhi
      _ ≤ Z*Z^Mcap := mul_le_mul hΦZ
        (Real.rpow_le_rpow_of_exponent_le hZ.le hrow)
        (Real.rpow_nonneg hZpos.le _) hZpos.le
      _ = Z^(1:ℝ)*Z^Mcap := by rw [Real.rpow_one]
      _ = Z^(1+Mcap) := (Real.rpow_add hZpos _ _).symm
      _ = Z^A := by congr 1; dsimp [A]; ring
  refine ⟨mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _),?_⟩
  intro X S hX hXP hS
  exact hbound Z mesh δ hZZ₀ hmpos hm hδ.1 hδ.2 d cores S Y X hd
    (by simpa only [hwidth] using hs) hresponse hY1 hYA (fun u hu => (hcores u hu).1)
    hX hXP hS


/-- The generic already-proved selected-cell theorem supplies this inlet. -/
theorem actual_norm (gap : ℝ) (hgap : 0 < gap) (hgap_half : gap < 1/2) :
    ActualSelectedSlotNormAt gap :=
  actual_of_aggregate gap (aggregate_of_cell gap hgap hgap_half
    NaturalSelectedNorm.natural_selected_cell_norm)

end
end Qrh.JointDetector.SelectedGap

set_option autoImplicit false
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
open Qrh.JointDetector
local notation "O" => HeckeFamily.O

/-- **R1 in the capped ordered case.** -/
theorem cap_proof_at (gap : ℝ) (hgap : 0 < gap) (hgap_half : gap < 1/2)
    (K : ℝ) (hK1 : 1/2+gap ≤ K) (hK2 : K ≤ 3/4) :
    SelectedRootEnergyCap K := by
  intro ε hε smin Mmin Mcap hsmin hMmin hMcap
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = min ε 1 / 20 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact div_pos (lt_min hε one_pos) (by norm_num)
  have hu1 : u ≤ 1/20 := by rw [hu]; have := min_le_right ε 1; linarith only [this]
  have huε : u ≤ ε/20 := by rw [hu]; have := min_le_left ε 1; linarith only [this]
  obtain ⟨Preq, hPreq⟩ : ∃ x : ℝ, x = 4*(Mcap+1) + 30 := ⟨_, rfl⟩
  have hPreq0 : 0 ≤ Preq := by rw [hPreq]; linarith only [hMmin, hMcap]
  obtain ⟨meshMax₀, hmesh₀, hnorm⟩ := Qrh.JointDetector.SelectedGap.actual_norm gap hgap hgap_half Mmin Mcap smin u Preq hMmin hMcap hsmin hu0 hPreq0
  refine ⟨meshMax₀, hmesh₀, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Knorm, hKnorm, hnormEv⟩ :=
    hnorm mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ (by linarith only [hbΦ])
  obtain ⟨auxCap, hauxCap⟩ : ∃ x : ℝ,
      x = FineDetectorWords.detectorAuxiliarySourceCap Preq (Mcap+1) := ⟨_, rfl⟩
  have hauxCap1 : 4*(Mcap+1) + 31 ≤ auxCap := by
    rw [hauxCap, FineDetectorWords.detectorAuxiliarySourceCap, hPreq]
    linarith only [le_max_left (4*(Mcap+1) + 30) (3*(Mcap+1))]
  have hauxCap0 : 0 < auxCap := by linarith only [hauxCap1, hMmin, hMcap]
  obtain ⟨εd, hεdD⟩ : ∃ x : ℝ, x = u / (auxCap * (2 + (Fintype.card α : ℝ))) := ⟨_, rfl⟩
  have hεd : 0 < εd := by rw [hεdD]; positivity
  have hεdmul : εd * (auxCap * (2 + (Fintype.card α : ℝ))) = u := by
    rw [hεdD]; field_simp
  obtain ⟨cη, hcη⟩ : ∃ x : ℝ, x = ∑ j, ((anchors j).modulus.absNorm : ℝ) + 1 := ⟨_, rfl⟩
  have hcη1 : 1 ≤ cη := by
    rw [hcη]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      (Nat.cast_nonneg ((anchors j).modulus.absNorm) : (0:ℝ) ≤ _))
    linarith only [this]
  obtain ⟨Cscale, hCscale⟩ : ∃ x : ℝ, x = cη * ((Ideal.span {fixedBadMask}).absNorm : ℝ) *
      ((Ideal.span {(72:O)}).absNorm : ℝ) * bΦ := ⟨_, rfl⟩
  have hNm0 : (0:ℝ) < ((Ideal.span {fixedBadMask}).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have hN720 : (0:ℝ) < ((Ideal.span {(72:O)}).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O) ≠ 0)))
  have hbΦ0 : (0:ℝ) < bΦ := by linarith only [hbΦ]
  have hCs : 0 < Cscale := by
    rw [hCscale]
    have : (0:ℝ) < cη := by linarith only [hcη1]
    positivity
  have hMcap0 : 0 < Mcap := lt_of_lt_of_le hMmin hMcap
  obtain ⟨n, Se, Ce, De, La, hCe, hDe, hLa, _, hreflEv⟩ :=
    R1.reflected_class (u/(Mcap+1)) Cscale u Mcap (by positivity) hCs hu0
  obtain ⟨S₁, C₁, hC₁, hscale⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    DetectorDictionaryInverseUniform.scaleCLM {((0:ℕ),(0:ℕ))}
  obtain ⟨S, hS⟩ : ∃ x : Finset (ℕ×ℕ), x = Se ∪ S₁ ∪ {((0:ℕ),(0:ℕ))} := ⟨_, rfl⟩
  have hS0 : ((0:ℕ),(0:ℕ)) ∈ S := by rw [hS]; simp
  have hSeS : Se ⊆ S := by rw [hS]; intro x hx; simp [hx]
  have hS₁S : S₁ ⊆ S := by rw [hS]; intro x hx; simp [hx]
  obtain ⟨LW, hLW⟩ : ∃ LW, ∀ x, ‖W x‖ ≤ LW :=
    hW.continuous.bounded_above_of_compact_support (HasCompactSupport.intro isCompact_Icc
      (fun x hx => by
        by_contra h'
        exact hx (hWs h')))
  have hLW0 : 0 ≤ LW := (norm_nonneg _).trans (hLW 0)
  obtain ⟨Csc, hCsc⟩ : ∃ x : ℝ, x = max 1 C₁ := ⟨_, rfl⟩
  have hCsc1 : 1 ≤ Csc := by rw [hCsc]; exact le_max_left _ _
  have hCscC : C₁ ≤ Csc := by rw [hCsc]; exact le_max_right _ _
  obtain ⟨C₆, hC₆, hsum⟩ := R1.root_class_sum
  refine ⟨2*n, S,
    ((9/4) * (2 * Knorm * (max 1 (Qrh.JointDetector.idealDivisorConstant εd hεd))^(2 + Fintype.card α) *
        ((128*(9/4))^2 + (Ce * (max 1 Cscale) * (1 + 2*(Mcap+1)/u) + De * (max 1 Cscale)^2) *
          (128 * La^2 * (128*(9/4))) * Csc^2) * (max 1 (256 * LW^2))^(Fintype.card α)) *
      (R1.rootZeta (1 + u/(Mcap+1)) * bΦ * (1 + (9/4) * 2^(Fintype.card α)) + C₆ * bΦ +
        R1.rootZeta (1 + u/(Mcap+1)) * (9/4) * ((9/4) * 2^(Fintype.card α)))), ?_, ?_⟩
  · have := le_max_left (1:ℝ) (Qrh.JointDetector.idealDivisorConstant εd hεd)
    have := R1.rootZeta_nonneg (1 + u/(Mcap+1))
    positivity
  filter_upwards [hnormEv, hreflEv, eventually_ge_atTop ((9/4:ℝ)^2 * 2^(Fintype.card α))]
    with Z hZ93 hZref hZbig
  refine ⟨hZ93.1, ?_⟩
  intro j st hchar hpunc hMlow hMup T D θ w σ v t height hw hwm hσ₁ hσ₂ hh hv hsD hsT p X₁ X₂ hX₁ hX₂
    h21 hl₁ hl₂
  have hηmod : ((st.character.modulus.absNorm : ℕ) : ℝ) ≤ cη := by
    rw [hchar, hcη]
    have := Finset.single_le_sum (f := fun j' => ((anchors j').modulus.absNorm : ℝ))
      (fun j' _ => Nat.cast_nonneg _) (Finset.mem_univ j)
    linarith only [this]
  have hsD' : smin ≤ ∑ k : D, w k := by rw [Finset.sum_coe_sort D w]; exact hsD
  exact cap_body K ε Mmin Mcap u auxCap εd Knorm cη Cscale Ce De La Csc C₆ LW bΦ Z t height n Se S
    (by linarith only [hK1, hgap]) (by linarith only [hK2]) hMmin hu0 hu1 huε hauxCap1 rayM H hbΦ hεd
    hεdmul hKnorm hCscale hCs hCe hDe hLa hLW0 hS0 hSeS hCsc1
    (scale_bound S S₁ C₁ Csc hC₁ hCscC hS₁S hscale) hC₆ hsum hZ93.1 hZbig hZref.2 st hpunc hηmod hMlow
    hMup T w hw hsT
    (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i I => R1.annular_coeff_le _ W LW (Z^(w i)) (σ i) (v i) I
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ93.1) _) (by linarith only [hσ₁ i]) hWs hLW)
    (fun z => Z^(K * ∑ i ∈ D, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z D z)
    (fun r cores Y hY1 hY2 hc => hauxCap ▸ hZ93.2 j st hchar hpunc hMlow hMup D (fun k => θ k) (fun k => w k)
      (fun k => σ k) (fun k => v k) t height (fun k => hw k) (fun k => hwm k) (fun k => hσ₁ k)
      (fun k => hσ₂ k) hh (fun k => hv k) hsD' K Y r cores ⟨hK1, hK2⟩ hY1 hY2 (fun u hu => by
        obtain ⟨h1, hz, h2, h3⟩ := hc u hu
        refine ⟨h1, hz, h2, ?_⟩
        rw [slotMass_eq_blockMass rayM H hH st hpunc η₀ W θ w σ v t D _
          (HeckeInverseAmplification.rowMap_ne_zero _), Finset.sum_coe_sort D w]
        exact h3))
    hh p X₁ X₂ hX₁ hX₂ h21 hl₁ hl₂


/-- Research target: R1 at any fixed positive gap above one half. -/
theorem selectedRootEnergy_at (gap : ℝ) (hgap : 0 < gap) (hgap_half : gap < 1/2)
    (K : ℝ) (hK1 : 1/2+gap ≤ K) (hK2 : K ≤ 3/4) : SelectedRootEnergy K :=
  selectedRootEnergy_of_ord K (ord_of_cap K (cap_proof_at gap hgap hgap_half K hK1 hK2))

/-- No uniform mesh in K is asserted as K approaches one half. -/
theorem selectedRootEnergy_above_half (K : ℝ) (hK : 1/2 < K) (hK2 : K ≤ 3/4) :
    SelectedRootEnergy K := by
  exact selectedRootEnergy_at (K-1/2) (by linarith) (by linarith)
    K (by linarith) hK2

/-- Concrete fixed gap requested for the source search. -/
theorem selectedRootEnergy_gap12 : SelectedRootEnergy (500000000001/1000000000000) :=
  selectedRootEnergy_at (1/1000000000000) (by norm_num) (by norm_num)
    (500000000001/1000000000000) (by norm_num) (by norm_num)

end
end QRH.ArviSelectedLeaf

#print axioms QRH.ArviSelectedLeaf.selectedRootEnergy_above_half
#print axioms QRH.ArviSelectedLeaf.selectedRootEnergy_gap12
