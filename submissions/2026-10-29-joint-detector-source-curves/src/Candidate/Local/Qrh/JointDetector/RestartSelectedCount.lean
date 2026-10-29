/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FineNaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptivePrice
import Candidate.Local.Qrh.JointDetector.RefinedSupplier
import Candidate.Local.Qrh.JointDetector.FineAdaptiveSupplier.High
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

namespace Qrh.JointDetector.RestartSelectedCount
open FineNaturalCount FineDetectorWords FineDetectorCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

def WholeSelectedCountOn (νMin : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss : ℝ, 0 < Mmin → Mmin ≤ Mcap → 0 < smin → 0 < loss →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 1 ≤ bΦ →
  ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0 ≤ w k) → (∀ k, w k ≤ mesh) →
    (∀ k, (33/50 : ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
    0 ≤ height → (∀ k, |v k| ≤ height) → smin ≤ ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2 ≤ b → b ≤ 7/8 →
    δ ∈ Icc (500001/1000000 : ℝ) (3/4) → 0 ≤ T' →
  ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
    st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
    b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T' ∧
    Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z) →
    (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(detectorRate (2*b-1) δ+loss)

theorem exists_quantitative_early_count_budget (dmin loss : ℝ) (hdmin : 0 < dmin) (hloss : 0 < loss) :
    ∃ budget : EarlyCountBudget dmin loss, budget.buffer ≤ 1/2000000 := by
  let p := min loss 1
  have hp : 0 < p := lt_min hloss (by norm_num)
  have hp1 : p ≤ 1 := min_le_right _ _
  have hploss : p ≤ loss := min_le_left _ _
  let eps := p/1000
  let buffer := eps/2000
  let normLoss := dmin*p/1000
  let logLoss := p/1000
  let tau := min (dmin*buffer/8) (dmin*p/1000)
  let bins := ⌈(49/100 : ℝ)/buffer⌉₊+1
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heb : 0 < buffer := by dsimp [buffer]; positivity
  have hebcap : buffer < 1/1000 := by dsimp [buffer, eps]; nlinarith
  have htau : 0 < tau := lt_min (by positivity) (by positivity)
  have htau1 : tau ≤ dmin*buffer/8 := min_le_left _ _
  have htau2 : tau ≤ dmin*p/1000 := min_le_right _ _
  have hconvert : (tau+normLoss)/dmin ≤ p/500 := (div_le_iff₀ hdmin).2 (by
    dsimp [normLoss]
    nlinarith)
  have hwidth : (49/100 : ℝ) ≤ (bins : ℝ)*buffer := by
    have h := (div_le_iff₀ heb).mp (Nat.le_ceil ((49/100 : ℝ)/buffer))
    dsimp [bins]
    push_cast
    nlinarith
  refine ⟨{
    eps := eps
    buffer := buffer
    normLoss := normLoss
    logLoss := logLoss
    tau := tau
    bins := bins
    eps_pos := heps
    eps_cap := ?_
    buffer_pos := heb
    buffer_cap := hebcap
    buffer_one := by linarith
    normLoss_pos := by dsimp [normLoss]; positivity
    logLoss_pos := by dsimp [logLoss]; positivity
    tau_pos := htau
    tau_zero := ?_
    tau_height := ?_
    detector_budget := ?_
    bins_pos := by dsimp [bins]; omega
    bins_width := hwidth
    total_loss := ?_
    constant_loss_cap := ?_ }, ?_⟩
  · dsimp [eps]
    linarith
  · have hb1 : buffer ≤ 1 := by linarith
    have h := mul_le_mul_of_nonneg_left hb1 hdmin.le
    nlinarith
  · nlinarith
  · dsimp [buffer]
    linarith
  · dsimp [eps, buffer, logLoss] at *
    linarith
  · dsimp [eps, buffer, logLoss]
    nlinarith

  · dsimp [buffer, eps]
    linarith

theorem wholeSelectedCountOn_of_actualSelectedSlotNorm (hnorm : ActualSelectedSlotNorm)
    (νMin : ℝ) (hνMin : (50001/100000 : ℝ) ≤ νMin) : WholeSelectedCountOn νMin := by
  intro Mmin Mcap smin loss hMmin hMcap hsmin hloss
  let dmin := Mmin/20
  have hdmin : 0 < dmin := by dsimp [dmin]; positivity
  have hdminCap : dmin ≤ Mcap := by dsimp [dmin]; linarith
  have hMcapPos : 0 < Mcap := hMmin.trans_le hMcap
  obtain ⟨budget,hbufferSmall⟩ := exists_quantitative_early_count_budget dmin loss hdmin hloss
  obtain ⟨meshMax,hmeshMax,hoperator⟩ := hnorm Mmin Mcap smin budget.normLoss 0
    hMmin hMcap hsmin budget.normLoss_pos (by norm_num)
  refine ⟨meshMax,hmeshMax,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWsupport κ _ anchors η₀ bΦ hbΦ
  obtain ⟨Knorm,hKnorm,hnormEvent⟩ := hoperator mesh hmesh α rayM H hH W hW hWsupport κ anchors η₀ bΦ hbΦ
  let base := orientedFixedBase (QRH.SilDensitySplit.Density.highDictionary rayM H hH anchors η₀)
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨Cdict,hCdict,hconductor⟩ := D.natural_conductor_bound
  obtain ⟨Jcore,Ccore,hCcore,hcoreEvent⟩ := natural_selected_count_eventually
    dmin Mcap loss Cdict bΦ Knorm budget hdmin hdminCap hMcapPos hCdict hbΦ hKnorm base Prod.snd hconductor
  let J := Jcore
  let C := Ccore
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hnormEvent,hcoreEvent] with Z hnormZ hcoreZ
  have hZ := hcoreZ.1
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro j st hchar hpuncture hMlower hMupper hQM hQη T θ w σ v t height
    hw hwmesh hσ hσ' hheight hv hs b δ T' hb hb' hδ hT' rows hrows
  let B := bΦ*Z^st.rowWidth
  have hMrowCap : st.rowWidth ≤ Mcap := by
    have hw : st.rowWidth ≤ st.width := by
      dsimp [NaturalState.width]
      linarith [st.character_nonneg]
    exact hw.trans hMupper
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact one_le_mul_of_one_le_of_one_le hbΦ (Real.one_le_rpow hZ.le (hMmin.le.trans hMlower))
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hBlower : Z^(20*dmin) ≤ B := by
    have h20 : 20*dmin = Mmin := by dsimp [dmin]; ring
    rw [h20]
    exact (Real.rpow_le_rpow_of_exponent_le hZ.le hMlower).trans
      (le_mul_of_one_le_left (by positivity) hbΦ)
  have hBupper : B ≤ bΦ*Z^Mcap := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le hMrowCap) (by linarith)
  have hbbuffer : b ∈ Icc ((3/4 : ℝ)+budget.buffer) (7/8) :=
    ⟨by linarith,hb'⟩
  let P : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop := fun root u =>
    ∃ hz : st.radial.keep (rowMap (u,root)),
      st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
      Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))
  have hnormActual (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (F : Finset FreeRow)
      (hYlower : Z^dmin ≤ Y) (hYupper : Y ≤ B) (hF : ∀ u ∈ F, rowNorm u ≤ Y ∧ P root u) :
      SelectedAllSourceNormBound (F.image Subtype.val) Y δ (Knorm*Z^budget.normLoss)
        (Z^(3*(Mcap+1)+1)) := by
    have h := hnormZ.2 j st hchar hpuncture hMlower hMupper T θ w σ v t height
      hw hwmesh hσ hσ' hheight hv hs δ Y root F hδ hYlower hYupper hF
    have hcap : detectorAuxiliarySourceCap 0 (Mcap+1) = 3*(Mcap+1)+1 := by
      unfold detectorAuxiliarySourceCap
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 3*(Mcap+1))]
    simpa only [hcap] using h
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card = rows.card := by
    rw [Finset.card_subtype,Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk,_⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hselected : ∀ z ∈ rows', rawFrequencyNorm z ≤ B ∧ naturalActualZeroRow base Prod.snd b T' z ∧
      P (sixthFrequencyEquiv.symm z).2 (sixthFrequencyEquiv.symm z).1 := by
    intro z hz
    have hzrows := Finset.mem_subtype.mp hz
    obtain ⟨hk,hp,hm,ha⟩ := hrows z.val hzrows
    have hnatural := physical_row_to_fixed_natural_zero rayM H hH anchors η₀ j st hchar hpuncture
      hQM hQη b T' (by linarith) z hk hp hm
    refine ⟨hnatural.1,hnatural.2,?_⟩
    have heq : rowMap ((sixthFrequencyEquiv.symm z).1,(sixthFrequencyEquiv.symm z).2) = z.val :=
      congrArg Subtype.val (sixthFrequencyEquiv.apply_symm_apply z)
    dsimp only [P]
    simpa only [heq] using (show ∃ hz : st.radial.keep z.val,
      st.radial.profile (‖eisEmbedding z.val‖^2/st.radial.scale) ≠ 0 ∧
      Z^(δ*∑ k, w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z.val from ⟨hk,hp,ha⟩)
  have hcount := hcoreZ.2 B b δ T' P hBlower hBupper hbbuffer hδ hT' hnormActual rows' hselected
  rw [hcard] at hcount
  exact hcount

end
end Qrh.JointDetector.RestartSelectedCount

#print axioms Qrh.JointDetector.RestartSelectedCount.wholeSelectedCountOn_of_actualSelectedSlotNorm
