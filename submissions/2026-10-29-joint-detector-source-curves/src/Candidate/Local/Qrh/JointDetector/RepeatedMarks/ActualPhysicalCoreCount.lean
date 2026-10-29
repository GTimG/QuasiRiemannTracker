/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PhysicalCoreCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceZeroCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PhysicalZeroTransport
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedRescaling
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BufferedRate
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.HeightBudget
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ZeroBudget
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PhysicalSlotResponse
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CorePopulation

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths LocalMoment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical HeckeDetectorZeros
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT Cycle61Moment
open HeckeDetectorCoefficientTransfer
open QRH.Record1252270103Source
local notation "O" => HeckeFamily.O
local instance (M : Ideal O) [NeZero M] : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def AnchorPhysicalCoreCount (νMin B L c : ℝ) : Prop :=
  ∀ Mmin Mcap smin loss dmin : ℝ, 0 < Mmin → Mmin  ≤  Mcap → 0 < smin → 0 < loss → 0 < dmin →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh  ≤  meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM  ≤  H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Icc (1 : ℝ) 2 →
  ∀ (η η₀ : Character) (bΦ : ℝ), 1  ≤  bΦ →
  ∃ extra : Finset FreeRow, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (st : NaturalState Z 0 bΦ), st.character = η → st.puncture = 1 →
    Mmin  ≤  st.rowWidth → st.width  ≤  Mcap →
  ∀ (hQM : st.fixedModulus  ≤  rayM) (hQη : st.fixedModulus  ≤  η₀.modulus)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ k, 0  ≤  w k) → (∀ k, w k  ≤  mesh) →
    (∀ k, (33/50 : ℝ)  ≤  σ k) → (∀ k, σ k  ≤  33/50) →
    0  ≤  height → (∀ k, |v k|  ≤  height) → smin  ≤  ∑ k, w k →
  ∀ (b δ T' : ℝ), (1+νMin)/2  ≤  b → b  ≤  7/8 →
    δ ∈ Icc dmin (2*b-1) → 0  ≤  T' → |t|+height  ≤  T' →
  ∀ (root : HeckeInverseAmplification.NonzeroIdeal) (Y : ℝ) (cores : Finset FreeRow),
    Z^(Mmin/20)  ≤  Y → Y  ≤  bΦ*Z^st.rowWidth →
    (∀ u ∈ cores, rowNorm u  ≤  Y ∧ u ∉ extra ∧
      ∃ hz : st.radial.keep (rowMap (u,root)),
        st.radial.profile (‖eisEmbedding (rowMap (u,root))‖^2/st.radial.scale) ≠ 0 ∧
        b  ≤  Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη (rowMap (u,root)) hz T' ∧
        Z^(δ*∑ k,w k)  ≤  RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) →
    (cores.card:ℝ)  ≤  C*(1+T')^J*Y^(rawRepeatedCountRate B L c (2*b-1) δ+loss)


/-- Moment height and fixed conductor constants are paid after the
source degree is known, with one total core-radius loss. -/
private theorem absorb_source_count {card U Y Ccond K C A τ r₀ r loss tol : ℝ} (J : ℕ)
    (hY : 1 ≤ Y) (hCond : 1 ≤ Ccond) (hU : U=Ccond*Y)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hA : 0 ≤ A) (hτ : 0 ≤ τ)
    (hr₀ : 0 ≤ r₀) (hr₀hi : r₀ ≤ 1) (htol : 0 ≤ tol) (htolhi : tol ≤ 1/4)
    (hrate : r₀ ≤ r+tol) (hτJ : τ*(J:ℝ) ≤ tol) (hbudget : 3*tol ≤ loss)
    (hcount : card ≤ K*C*(1+A*U^τ)^J*U^(r₀+tol)) :
    card ≤ (K*C*(1+A)^J*Ccond^2)*Y^(r+loss) := by
  have hU1 : 1 ≤ U := by rw [hU]; nlinarith
  have hUp : 0<U := zero_lt_one.trans_le hU1
  have hE0 : 0 ≤ τ*(J:ℝ)+r₀+tol := by positivity
  have hEhi : τ*(J:ℝ)+r₀+tol ≤ 2 := by linarith
  have hEr : τ*(J:ℝ)+r₀+tol ≤ r+loss := by linarith
  have hcondPow : Ccond^(τ*(J:ℝ)+r₀+tol) ≤ Ccond^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hCond hEhi
  have hwhole : U^(τ*(J:ℝ)+r₀+tol) ≤ Ccond^2*Y^(r+loss) := by
    rw [hU,Real.mul_rpow (by linarith) (by linarith)]
    exact mul_le_mul hcondPow (Real.rpow_le_rpow_of_exponent_le hY hEr)
      (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
  calc card  ≤  (K*C)*((1+A)^J*U^(τ*(J:ℝ)))*U^(r₀+tol) :=
        hcount.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (small_height_budget J hU1 hτ hA) (mul_nonneg hK hC))
          (Real.rpow_nonneg hUp.le _))
    _ = K*C*(1+A)^J*U^(τ*(J:ℝ)+r₀+tol) := by
      simp only [Real.rpow_add hUp]
      ring
    _  ≤  K*C*(1+A)^J*(Ccond^2*Y^(r+loss)) :=
      mul_le_mul_of_nonneg_left hwhole (by positivity)
    _ = _ := by ring

/-- The actual one-anchor physical core count is supplied by the proved
parent source, with fixed exceptions and full original slot responses. -/
theorem anchorPhysicalCoreCount_of_globalSource (floor B L c : ℝ)
    (hf : (2/5:ℝ) ≤ floor) (hfhi : floor ≤ 3/4)
    (hBmin : (9/10:ℝ) ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hparent : GlobalSource B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : AnchorPhysicalCoreCount floor B L c := by
  intro Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin
  let dcore := Mmin/20
  let Dcap := Mcap+2
  let tol := (min loss 1)/16
  have hdcore : 0<dcore := by dsimp [dcore]; positivity
  have hMcap : 0<Mcap := hMmin.trans_le hMcap
  have hD : 0<Dcap := by dsimp [Dcap]; linarith
  have htol : 0<tol := by dsimp [tol]; positivity
  have htol1 : tol ≤ 1/16 := by dsimp [tol]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have htolloss : 3*tol ≤ loss := by
    have hh := min_le_left loss (1:ℝ)
    dsimp [tol]
    nlinarith [lt_min hloss (by norm_num : (0:ℝ)<1)]
  have hfp : 0<floor := by linarith
  obtain ⟨buffer,hbuffer,hbuffered⟩ := buffered_rate_budget B L c floor dmin tol hL hfp hdmin htol
  obtain ⟨meshSrc,β,εMax,hmSrc,hβamp,hβd,hεMax,hzeroSource⟩ := zero_count_at_loss
    B L c (floor/2) (dmin/2) (smin/Dcap) tol hL (by linarith) hBmin hB hc0 hc
    (by positivity) (by positivity) (div_pos hsmin hD) htol hparent hβ
  refine ⟨meshSrc*dcore,mul_pos hmSrc hdcore,?_⟩
  intro mesh hmesh α _ _ M _ H hH W hW hWs η η₀ bΦ hbΦ
  let Label := WholeSourceIndex M H×Bool
  let base : Label→Character := orientedFixedBase (RootedBatchConcrete.base M H hH η η₀)
  let anchor : Label→Character := fun j=>WholeAnchorSlots.sourceAnchor M H hH η₀ j.1
  let Q := RootedBatchConcrete.fixedBad M η η₀
  let bad : Label→Ideal O := fun _=>Q
  let D := FixedUnmarkedDictionary.ofBases base
  obtain ⟨hQ0,hQt,hQ72,hQM,hQη₀,hQη⟩ := RootedBatchConcrete.fixedBad_gates M η η₀
  obtain ⟨Esource,hEsource⟩ := RootedBatchConcrete.exists_batch_extraE M H hH η η₀ Q
    hQ0 hQt hQ72 hQη hQM hQη₀
  let extra : Finset FreeRow := Esource ∪ D.exceptional_cores_finite.toFinset
  obtain ⟨Ccond,hCcond,hconductor⟩ := D.natural_conductor_bound
  let Aroot := Dcap/dcore
  have hAr : 0 ≤ Aroot := div_nonneg hD.le hdcore.le
  obtain ⟨J,C,hC,hcounter⟩ := hzeroSource meshSrc hmSrc.le le_rfl
    (Label:=Label) (Slot:=α) M H hH Aroot hAr base anchor bad
    (fun _=>hQM) (fun _=>internalQ_ne_zero Q hQ0 _)
    (fun _=>internalQ_ne_top Q hQt _) (fun _=>inf_le_left.trans hQ72) W hW hWs
  obtain ⟨ε,e,κ,ηaux,τ,n,hε,hεsmall,he,hebuffer,hecap,hκ,hκ1,hηaux,hbudget,
    hτ,hτcap,hτη,hτJ,hn,hne⟩ := choose_zero_budget εMax buffer tol J hεMax hbuffer htol
  obtain ⟨Jout,hlargeHeight⟩ := large_height_budget τ hτ
  let A : ℝ := 2*Real.pi+(3*n:ℕ)+2
  let Kbin : ℝ := ((n+1:ℕ):ℝ)*(⌈1/e⌉₊+2:ℕ)
  let Csmall : ℝ := Kbin*C*(1+A)^J*Ccond^2
  let Cout : ℝ := Csmall+769
  have hA : 1 ≤ A := by
    have hp := Real.pi_pos
    have hn0 : (0:ℝ) ≤ (3*n:ℕ) := Nat.cast_nonneg _
    dsimp [A]
    linarith
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall,Kbin]; positivity
  have hCout : 0<Cout := by dsimp [Cout]; linarith
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp
    (hcounter τ ε e κ ηaux n hτ hτcap hτη hε hεsmall he hecap hκ hκ1 hηaux hbudget hn hne)
  have heventU : ∀ᶠ Z : ℝ in atTop,U₀ ≤ Z^dcore :=
    (tendsto_rpow_atTop hdcore).eventually (eventually_ge_atTop U₀)
  refine ⟨extra,Jout,Cout,hCout,?_⟩
  filter_upwards [RootedRescaling.eventually_ambient Ccond bΦ Mcap dcore hCcond hdcore,
    heventU,eventually_ge_atTop bΦ] with Z hZ hZU hZPhi
  refine ⟨hZ.1,?_⟩
  intro st hchar hp hM hw hstQM hstQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hs
    b δ T' hb hb1 hδ hT hphase root Y cores hYlower hYupper hcores
  have hZp : 0<Z := zero_lt_one.trans hZ.1
  have hrowcap : st.rowWidth ≤ Mcap := by
    have := st.character_nonneg
    have : st.width=st.rowWidth+st.characterWidth := rfl
    linarith
  have hYcap : Y ≤ bΦ*Z^Mcap := hYupper.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.1.le hrowcap) (by linarith))
  let U := Ccond*Y
  obtain ⟨hU,hcoreU,hUcap⟩ := hZ.2 Y hYlower hYcap
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hZ.1.le hdcore.le).trans hYlower
  have hYU : Y ≤ U := by dsimp [U]; nlinarith
  have hUevent := hU₀ U (hZU.trans (hYlower.trans hYU))
  have hrate := rawRepeatedCountRate_bounds (by linarith : 0 ≤ B) hB hL hc0 hc
    (hfp.trans_le (show floor ≤ 2*b-1 by linarith)) (by linarith : 2*b-1 ≤ 3/4) (hdmin.le.trans hδ.1) hδ.2
  have hYpow : 1 ≤ Y^(rawRepeatedCountRate B L c (2*b-1) δ+loss) :=
    Real.one_le_rpow hY1 (by linarith [hrate.1])
  by_cases hempty : cores=∅
  · simp only [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  have hnonempty : cores.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  by_cases hsmall : T' ≤ U^τ
  · have hregular : ∀u∈cores,¬D.exceptionalCore u := by
      intro u hu hbad
      apply (hcores u hu).2.1
      exact Finset.mem_union_right _ (D.exceptional_cores_finite.mem_toFinset.mpr hbad)
    have hkeep : ∀u∈cores,∀j : WholeSourceIndex M H,
        initialKeep (RootedBatchConcrete.base M H hH η η₀ j)
          (internalQ Q (WholeAnchorSlots.sourceAnchor M H hH η₀ j)) u.val := by
      intro u hu
      apply hEsource u
      intro hbad
      exact (hcores u hu).2.1 (Finset.mem_union_left _ hbad)
    choose hk hprofile hmaximum hamplitude using (fun u : cores=>(hcores u.val u.property).2.2)
    have hphysical (u : cores) := PhysicalZeroTransport.physical_row_to_free_source_maximum
      M H hH η η₀ st hchar hp hstQM hstQη b T' (by linarith [hf])
      (sixthFrequencyEquiv (u.val,root)) (hk u) (hprofile u) (hmaximum u)
      (by simpa using hregular u.val u.property)
    have hzeroCore : ∀u : cores,∃hn : ∀j,(D.naturalFamily u.val j).residue≠1,
        b ≤ zeroMaximum (D.naturalFamily u.val) hn T' := by
      intro u
      have hh := (hphysical u).2
      have heq : (sixthFrequencyEquiv.symm (sixthFrequencyEquiv (u.val,root))).1=u.val :=
        congrArg Prod.fst (sixthFrequencyEquiv.symm_apply_apply (u.val,root))
      rw [heq] at hh
      exact hh
    choose hnCore hmaxCore using hzeroCore
    have hrootBound : (root.val.absNorm:ℝ)^6 ≤ bΦ*Z^Mcap := by
      obtain ⟨u₀,hu₀⟩ := hnonempty
      have hrn := rowMap_norm (u₀,root)
      have hnormFull : rawFrequencyNorm (sixthFrequencyEquiv (u₀,root))=
          rowNorm u₀*(root.val.absNorm:ℝ)^6 := by
        change ((Ideal.span {rowMap (u₀,root)}).absNorm:ℝ)=
          ((Ideal.span {u₀.val}).absNorm:ℝ)*(root.val.absNorm:ℝ)^6
        exact_mod_cast hrn
      calc (root.val.absNorm:ℝ)^6  ≤  rowNorm u₀*(root.val.absNorm:ℝ)^6 :=
            le_mul_of_one_le_left (by positivity) (rowNorm_ge_one u₀)
        _ = rawFrequencyNorm (sixthFrequencyEquiv (u₀,root)) := hnormFull.symm
        _  ≤  bΦ*Z^st.rowWidth := (hphysical ⟨u₀,hu₀⟩).1
        _  ≤  bΦ*Z^Mcap := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hZ.1.le hrowcap) (by linarith)
    have hrootU : (root.val.absNorm:ℝ) ≤ U^Aroot :=
      RootedRescaling.root_norm_upper root hZ.1 hdcore hMcap.le hZPhi hcoreU le_rfl hrootBound
    let θext : α→RayQuotient.Characters M H := fun s=>if hs:s∈T then θ ⟨s,hs⟩ else 1
    let wext : α→ℝ := fun s=>if hs:s∈T then w ⟨s,hs⟩ else 0
    let σext : α→ℝ := fun s=>if hs:s∈T then σ ⟨s,hs⟩ else 33/50
    let vext : α→ℝ := fun s=>if hs:s∈T then v ⟨s,hs⟩ else 0
    have hθext : ∀k : T,θext k.val=θ k := by intro k; simp [θext,k.property]
    have hwext : ∀k : T,wext k.val=w k := by intro k; simp [wext,k.property]
    have hσext : ∀k : T,σext k.val=σ k := by intro k; simp [σext,k.property]
    have hvext : ∀k : T,vext k.val=v k := by intro k; simp [vext,k.property]
    have hwext0 : ∀s∈T,0 ≤ wext s := by
      intro s hs
      simpa only [hwext ⟨s,hs⟩] using hw0 ⟨s,hs⟩
    let wr : α→ℝ := fun s=>RootedRescaling.width U Z (wext s)
    have hwr0 : ∀s∈T,0 ≤ wr s := fun s hs=>RootedRescaling.width_nonneg hU hZ.1.le (hwext0 s hs)
    have hwrmesh : ∀s∈T,wr s ≤ meshSrc := by
      intro s hs
      have hh := RootedRescaling.width_upper hU hZ.1 hdcore hcoreU (hw0 ⟨s,hs⟩) (hwm ⟨s,hs⟩)
      have hm : mesh/dcore ≤ meshSrc := (div_le_iff₀ hdcore).2 hmesh
      have hh' : wr s ≤ mesh/dcore := by
        simpa only [wr,hwext ⟨s,hs⟩] using hh
      exact hh'.trans hm
    have hsumOriginal : (∑s∈T,wext s)=∑k:T,w k := by
      rw [←Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl (fun k _=>hwext k)
    have hsumSource : smin/Dcap ≤ ∑s∈T,wr s :=
      RootedRescaling.sum_width_lower T wext hU hZ.1 hD hUcap hwext0 (hsumOriginal.symm ▸ hs)
    let N₀ := RootedBatchConcrete.batch M H hH η η₀ (fun _=>Q) root W U Aroot
      (zero_lt_one.trans hU) hWs hrootU cores T θext wr σext vext t hwr0
      (by intro s hs; simpa only [hσext ⟨s,hs⟩] using hσ0 ⟨s,hs⟩)
      (by intro s hs; simpa only [hσext ⟨s,hs⟩] using hσ1 ⟨s,hs⟩)
      (by intro u hu; exact ((hcores u hu).1).trans hYU)
      (by intro u hu; rw [eisEmbedding_norm_sq_eq_absNorm_span]; exact ((hcores u hu).1).trans hYU)
    let N : RootedBatch (Slot:=α) M H hH base anchor bad W U Aroot := N₀.reindex Prod.fst
    have hNrows : N.rows=cores := by
      change RootedBatchConcrete.goodRows M H hH η η₀ (fun _=>Q) cores=cores
      exact Finset.filter_eq_self.mpr hkeep
    let ν : ℝ := 2*b-1
    let ν₀ : ℝ := ν-2*e
    let a₀ : ℝ := b-e
    let v₀ : ℝ := min δ ν₀
    have hν₀ : 2*a₀-1=ν₀ := by dsimp [a₀,ν₀,ν]; ring
    obtain ⟨hνlow,hvlow,hvpos,hvν,hclose⟩ := hbuffered ν δ e (by dsimp [ν]; linarith)
      (by dsimp [ν]; linarith) hδ.1 hδ.2 he.le hebuffer
    have hνhi : ν₀ ≤ 3/4 := by dsimp [ν₀,ν]; linarith
    have hrate₀ := rawRepeatedCountRate_bounds (by linarith : 0 ≤ B) hB hL hc0 hc
      ((by positivity : 0<floor/2).trans_le hνlow) hνhi hvpos hvν
    let Hlive : ℝ := A*U^τ
    have hHlive : 0 ≤ Hlive := by dsimp [Hlive]; positivity
    have hUH : U^τ ≤ Hlive := le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hU).le _) hA
    have hresponse : ∀u∈N.rows,U^(v₀*(∑s∈N.slots,N.widths s)) ≤ ∏s∈N.slots,‖N.Q u s‖^2 := by
      intro u hu
      have huc : u∈cores := hNrows ▸ hu
      change U^(v₀*(∑s∈T,RootedRescaling.width U Z (wext s))) ≤
        ∏s∈T,‖RootedBatchConcrete.originalSlot M H hH η η₀ root W U θext wr σext vext t u s‖^2
      rw [RootedRescaling.amplitude_radius_eq T wext hU hZp,hsumOriginal,
        RootedBatchConcrete.originalSlot_mass M H hH st η η₀ hchar hp root W T θ w σ v
          θext wext σext vext hθext hwext hσext hvext t u hU hZp]
      exact (Real.rpow_le_rpow_of_exponent_le hZ.1.le
        (mul_le_mul_of_nonneg_right (min_le_left δ ν₀) (Finset.sum_nonneg (fun k _=>hw0 k)))).trans
          (hamplitude ⟨u,huc⟩)
    have hχN : ∀u : N.rows,∀j,(N.family u.val j).residue≠1 := by
      intro u j
      exact hnCore ⟨u.val,hNrows ▸ u.property⟩ j
    have hNconductor : ∀u : N.rows,∀j,(N.family u.val j).modulus.absNorm ≤ U := by
      intro u j
      exact (hconductor u.val j).trans (mul_le_mul_of_nonneg_left
        ((hcores u.val (hNrows ▸ u.property)).1) (by linarith))
    have hNzero : ∀u : N.rows,a₀+e ≤ zeroMaximum (N.family u.val) (hχN u) (U^τ) := by
      intro u
      have hm := hmaxCore ⟨u.val,hNrows ▸ u.property⟩
      change b ≤ zeroMaximum (N.family u.val) (hχN u) T' at hm
      have hmono := zeroMaximum_mono (N.family u.val) (hχN u) hsmall
      dsimp [a₀]
      linarith
    have hHfreq : 2*Real.pi*U^(τ/2)+(3*n:ℕ)*U^τ ≤ Hlive := by
      have hh := Real.rpow_le_rpow_of_exponent_le hU.le (show τ/2 ≤ τ by linarith)
      have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)
      dsimp [Hlive,A]
      nlinarith [Real.rpow_nonneg (zero_lt_one.trans hU).le τ]
    have hraw := hUevent.2 N hwrmesh a₀ v₀ Hlive (by dsimp [a₀]; linarith [hf])
      (hν₀.symm ▸ hνlow) (hν₀.symm ▸ hνhi) hvlow (hν₀.symm ▸ hvν)
      hHlive (by
        intro s hs'
        have hh' := abs_add_le t (vext s)
        have hvs : |vext s| ≤ height := by simpa only [hvext ⟨s,hs'⟩] using hv ⟨s,hs'⟩
        exact (by linarith : |t+vext s| ≤ T').trans (hsmall.trans hUH))
      hsumSource hresponse hχN hNconductor hNzero hHfreq
    have hraw' : (cores.card:ℝ) ≤ Kbin*C*(1+A*U^τ)^J*
        U^(rawRepeatedCountRate B L c ν₀ v₀+tol) := by
      simpa only [hNrows,hν₀,Kbin,Hlive,mul_assoc] using hraw
    have hsmallCount : (cores.card:ℝ) ≤ Csmall*Y^(rawRepeatedCountRate B L c ν δ+loss) := by
      exact absorb_source_count J hY1 hCcond rfl (by dsimp [Kbin]; positivity) hC.le
        (zero_le_one.trans hA) hτ.le (by linarith [hrate₀.1]) hrate₀.2 htol.le
        (by linarith) hclose (by linarith) htolloss hraw'
    have hCmul : Csmall ≤ Cout*(1+T')^Jout :=
      (show Csmall ≤ Cout by dsimp [Cout]; linarith).trans
        (le_mul_of_one_le_right hCout.le (one_le_pow₀ (by linarith : 1 ≤ 1+T')))
    exact hsmallCount.trans (mul_le_mul_of_nonneg_right hCmul (Real.rpow_nonneg (by linarith) _))
  · have htrivial : (cores.card:ℝ) ≤ 768*U := by
      have hc := free_core_population cores Y hY1 (fun u hu=>(hcores u hu).1)
      nlinarith
    have hheight := hlargeHeight U T' hU.le hT (le_of_not_ge hsmall)
    calc (cores.card:ℝ)  ≤  768*U := htrivial
      _  ≤  768*(1+T')^Jout := mul_le_mul_of_nonneg_left hheight (by norm_num)
      _  ≤  Cout*(1+T')^Jout := mul_le_mul_of_nonneg_right (by dsimp [Cout]; linarith) (by positivity)
      _  ≤  Cout*(1+T')^Jout*Y^(rawRepeatedCountRate B L c (2*b-1) δ+loss) :=
        le_mul_of_one_le_right (by positivity) hYpow

/-- Finite anchor packaging changes neither the source event nor any
moving profiles. The extra exception is a fixed finite union. -/
theorem physicalCoreCount_of_anchor (floor B L c : ℝ)
    (h : AnchorPhysicalCoreCount floor B L c) : PhysicalCoreCount floor B L c := by
  intro Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin
  obtain ⟨meshMax,hm,hall⟩ := h Mmin Mcap smin loss dmin hMmin hMcap hsmin hloss hdmin
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α _ _ M _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  have hanch := fun j : κ=>hall mesh hmesh α M H hH W hW hWs (anchors j) η₀ bΦ hbΦ
  choose E J C hC hcount using hanch
  let extra : Finset FreeRow := Finset.univ.biUnion E
  let Jtotal : ℕ := ∑j,J j
  let Ctotal : ℝ := 1+∑j,C j
  have hCsum : 0 ≤ ∑j,C j := Finset.sum_nonneg (fun j _=>(hC j).le)
  refine ⟨extra,Jtotal,Ctotal,by dsimp [Ctotal]; linarith,?_⟩
  filter_upwards [Filter.eventually_all.mpr hcount,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro j st hchar hp hM hw hQM hQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hs
    b δ T' hb hb1 hδ hT hphase root Y cores hYlower hYupper hcores
  have hj := (hZ j).2 st hchar hp hM hw hQM hQη T θ w σ v t height hw0 hwm hσ0 hσ1 hh hv hs
    b δ T' hb hb1 hδ hT hphase root Y cores hYlower hYupper (by
      intro u hu
      obtain ⟨hn,he,hrest⟩ := hcores u hu
      refine ⟨hn,?_,hrest⟩
      intro hj
      exact he (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩))
  have hJ : J j ≤ Jtotal := Finset.single_le_sum (fun k _=>Nat.zero_le _) (Finset.mem_univ j)
  have hCs : C j ≤ Ctotal := by
    have hc := Finset.single_le_sum (fun k _=>(hC k).le) (Finset.mem_univ j)
    dsimp [Ctotal]
    linarith
  have hYpos : 0<Y := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ1) _).trans_le hYlower
  apply hj.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hYpos.le _)
  exact mul_le_mul hCs (pow_le_pow_right₀ (by linarith : 1 ≤ 1+T') hJ)
    (by positivity) (by dsimp [Ctotal]; linarith)


/-- The physical core provider has no analytic norm, count, supplier or
witness premise beyond the already proved parent GlobalSource. -/
theorem physicalCoreCount_of_globalSource (floor B L c : ℝ)
    (hf : (2/5:ℝ) ≤ floor) (hfhi : floor ≤ 3/4)
    (hBmin : (9/10:ℝ) ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (hparent : GlobalSource B L c)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : PhysicalCoreCount floor B L c :=
  physicalCoreCount_of_anchor floor B L c
    (anchorPhysicalCoreCount_of_globalSource floor B L c hf hfhi hBmin hB hL hc0 hc hparent hβ)

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.physicalCoreCount_of_globalSource
