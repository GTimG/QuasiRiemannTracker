/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PhysicalCoreCount

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open HeckeDetectorWitnessRows
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT FineNaturalCount
local notation "O" => HeckeFamily.O

/-- Full original natural-row count from the literal physical core theorem.
Every fixed source exception and all natural sixth-root lifts are paid.
The only missing inlet here is the actual core theorem, not a second norm. -/
theorem wholeRepeatedCountOn_of_physicalCoreCount
    {floor B L c : ℝ} (hfloor : (2/5:ℝ) ≤ floor)
    (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 1/6)
    (hcores : PhysicalCoreCount floor B L c) :
    RepeatedWeightedHigh.WholeRepeatedCountOn floor B L c := by
  intro Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin
  let innerLoss := min (loss/2) 1
  have hi : 0 < innerLoss := lt_min (by positivity) one_pos
  have hiLoss : innerLoss ≤ loss := (min_le_left _ _).trans (by linarith)
  obtain ⟨meshMax,hmeshMax,hcount⟩ := hcores Mmin Mcap smin innerLoss dmin
    hMmin hMcap hsmin hi hdmin
  refine ⟨meshMax,hmeshMax,?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨extra,J,Ccore,hCcore,hcount⟩ := hcount mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  let base := orientedFixedBase (QRH.SilDensitySplit.Density.highDictionary rayM H hH anchors η₀)
  obtain ⟨D,Cpr,hD,hCpr,hlift⟩ := natural_count_of_uniform_free_count_away base Prod.snd extra
  let C := Ccore*D+Cpr+98304
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hcount] with Z hZcount
  have hZ := hZcount.1
  have hZp : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro j st hchar hpuncture hMlower hMupper hQM hQη T θ w σ v t height
    hw hwm hσlo hσhi hh hv hs b δ T' hb hb' hδ hT' hphase rows hrows
  let radius := bΦ*Z^st.rowWidth
  have hMpos : 0 ≤ st.rowWidth := hMmin.le.trans hMlower
  have hRadius1 : 1 ≤ radius := by
    exact one_le_mul_of_one_le_of_one_le hbΦ (Real.one_le_rpow hZ.le hMpos)
  have hRadiusLower : Z^(20*(Mmin/20)) ≤ radius := by
    have hE : 20*(Mmin/20)=Mmin := by ring
    rw [hE]
    exact (Real.rpow_le_rpow_of_exponent_le hZ.le hMlower).trans
      (le_mul_of_one_le_left (by positivity) hbΦ)
  have hν0 : 0 < 2*b-1 := by linarith
  have hν1 : 2*b-1 ≤ (3/4:ℝ) := by linarith
  have hδ0 : 0 ≤ δ := hdmin.le.trans hδ.1
  have hr := rawRepeatedCountRate_bounds hB0 hB hL hc0 hc hν0 hν1 hδ0 hδ.2
  let R := rawRepeatedCountRate B L c (2*b-1) δ+innerLoss
  have hR : (1/4:ℝ) ≤ R := by dsimp [R]; linarith [hr.1]
  let P : HeckeInverseAmplification.NonzeroIdeal → FreeRow → Prop := fun root u =>
    ∃ hz : st.radial.keep (rowMap (u,root)),
      st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
      b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη (rowMap (u,root)) hz T' ∧
      Z^(δ*∑ k,w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))
  have hfree (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (F : Finset FreeRow)
      (hY0 : Z^(Mmin/20) ≤ Y) (hY1 : Y ≤ radius)
      (hF : ∀ u ∈ F, rowNorm u ≤ Y ∧
        ¬(FixedUnmarkedDictionary.ofBases base).exceptionalCore u ∧ u ∉ extra ∧
        naturalActualZeroRow base Prod.snd b T' (sixthFrequencyEquiv (u,root)) ∧ P root u) :
      (F.card:ℝ) ≤ Ccore*(1+T')^J*Y^R := by
    apply hZcount.2 j st hchar hpuncture hMlower hMupper hQM hQη T θ w σ v t height
      hw hwm hσlo hσhi hh hv hs b δ T' hb hb' hδ hT' hphase root Y F hY0 hY1
    intro u hu
    exact ⟨(hF u hu).1,(hF u hu).2.2.1,(hF u hu).2.2.2.2⟩
  let rows' : Finset NonzeroFrequency := rows.subtype (fun z => z ≠ 0)
  have hcard : rows'.card=rows.card := by
    rw [Finset.card_subtype,Finset.filter_true_of_mem]
    intro z hz
    obtain ⟨hk,_⟩ := hrows z hz
    exact st.row_ne_zero z hk
  have hselected : ∀ z ∈ rows', rawFrequencyNorm z ≤ radius ∧
      naturalActualZeroRow base Prod.snd b T' z ∧
      P (sixthFrequencyEquiv.symm z).2 (sixthFrequencyEquiv.symm z).1 := by
    intro z hz
    have hzrows := Finset.mem_subtype.mp hz
    obtain ⟨hk,hp,hm,ha⟩ := hrows z.val hzrows
    have hn := physical_row_to_fixed_natural_zero rayM H hH anchors η₀ j st hchar hpuncture
      hQM hQη b T' (by linarith) z hk hp hm
    refine ⟨hn.1,hn.2,?_⟩
    have he : rowMap ((sixthFrequencyEquiv.symm z).1,(sixthFrequencyEquiv.symm z).2)=z.val :=
      congrArg Subtype.val (sixthFrequencyEquiv.apply_symm_apply z)
    dsimp only [P]
    simpa only [he] using (show ∃ hz : st.radial.keep z.val,
      st.radial.profile (‖eisEmbedding z.val‖^2/st.radial.scale) ≠ 0 ∧
      b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z.val hz T' ∧
      Z^(δ*∑ k,w k) ≤ RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t z.val from ⟨hk,hp,hm,ha⟩)
  have h := hlift Z radius b T' (Mmin/20) R Ccore J hZ (by positivity) hRadiusLower hT' hR hCcore P hfree rows' hselected
  rw [hcard] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hRadius1 (by dsimp [R]; linarith)) (by positivity))

end
end Qrh.JointDetector.RepeatedMarks
