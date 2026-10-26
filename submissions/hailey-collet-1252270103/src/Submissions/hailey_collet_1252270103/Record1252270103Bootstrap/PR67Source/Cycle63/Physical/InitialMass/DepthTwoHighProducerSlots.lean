import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighProducerRecord
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighProducerHeights
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighPresentation
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineAtState
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The producer of the HIGH given of the second step at the slots of one subset: the records of the two orientations
at the configurations of largest transport and the HIGH given of the parent from them. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT Cycle63Moment
open CenteredMomentAmplificationChildInput
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch HeckeDetectorZeros
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedRayDictionary CenteredMomentSecondInputCapacitySource
open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
open CenteredMomentLogDyadic
attribute [local instance] geometryAffineHighPaymentSumDecidable
attribute [local irreducible] Finset.univ

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
include M H hH in
/-- The producer of the HIGH given at the slots `ι` of one subset: given the transport bound of the top theorem at
the profile set `Sp` and the source gates, there is a degree `dh₀` such that for every larger degree, every profile set
containing `Sp`, every `ε` and every large enough constant `Kh`, the HIGH given holds at all large `Z`. -/
theorem depth_two_high_core {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (bΦ Bmask mesh τlow B lossNeeded μ δ Cs : ℝ)
    (Nbudget : ℕ) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hμ : 0<μ) (hμ1 : μ≤1) (hCs : 1≤Cs) (hgμ : g.μ=μ) (hgδ : g.δ=δ)
    (hδ : δ=geometryAffineHighDictionaryRate μ Nbudget)
    (hbΦ : 2≤bΦ) (_hBmask0 : 0≤Bmask) (hBmask : Bmask≤20) (hmesh0 : 0≤ mesh)
    (hmesh : mesh≤Cycle25.Energy.commonMesh 2 28 1 (μ/8)) (hτlow : 2*g.τ<τlow)
    (hq : Cycle63.Optimization.secondJunction≤Cycle63.AffineLedger.q) (_hN : Fintype.card ι≤Nbudget)
    (hloss : 13/8*μ+(9*(Nbudget:ℝ)+282)*δ≤lossNeeded)
    (Sp : Finset (ℕ×ℕ)) (hSp : (0,0)∈Sp) (K Kt : ℝ) (hKt : 0<Kt)
    (htop : ∀ᶠZ : ℝ in atTop,2≤Z ∧ AffineHighTopInner (ι:=ι) M H hH η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1
      one_ne_zero W hβlo g.e g.τ g.e_pos μ Cs 20 δ Cycle63.AffineLedger.q Nbudget Sp K Kt Q hQM hQ72 Z)
    (hcaps : ∀ᶠZ : ℝ in atTop,AffineSourceGatesAt (ι:=ι) M H hH W hW hWs Cs η₀ Z) :
    ∃dh₀ : ℕ,∀(Ψ : 𝓢(ℝ,ℂ))(SH : Finset (ℕ×ℕ)),Sp⊆SH → ∀dh : ℕ,dh₀≤dh → ∀ε : ℝ,0<ε →
      ∃Kh₀ : ℝ,0≤Kh₀ ∧ ∀Kh : ℝ,Kh₀≤Kh → ∀ᶠZ : ℝ in atTop,
        DepthTwoHighGivenSlots (ι:=ι) M H hH W hW hWs hβlo hβhi g (1/4) (9/4) bΦ Bmask mesh ε τlow B lossNeeded
          (by norm_num) Ψ SH dh (depthTwoHighClassBound g.e μ) Kh η₀ Q hQM hQ72 Z := by
  subst hgμ hgδ
  have hδ0 : 0<g.δ := g.δ_pos
  obtain ⟨cx,Kc,hKc,hcev⟩ : ∃cx Kc : ℝ,0<Kc ∧ ∀ᶠZ : ℝ in atTop,
      MainHighSelectedPhysicalCoarseSpec (α:=ι) (Fintype.card ι) 130 Cs (9/4) (9/4) (Real.log 2) 1 1 (1/4) (9/4) g.δ
        (g.μ/64) 3 cx Kc Z := by
    obtain ⟨K₀,hK₀,h⟩ := actual_main_high_final_all_height_coarse (α:=ι) η₀ 1 (naturalRow η₀ 1 one_ne_zero) 1
      one_ne_zero (Fintype.card ι) rfl (bp:=9/4) 130 (g.μ/8) g.δ g.δ Cs (9/4) (9/4) (Real.log 2) 1 1 (1/4) (g.μ/8)
      g.δ (g.μ/64) 3 (by norm_num) (by positivity) hδ0 hδ0 hCs (by norm_num) (by norm_num)
      (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by positivity) hδ0.le
      (by positivity) (by linarith) (by norm_num)
    exact ⟨_,K₀,hK₀,h⟩
  refine ⟨(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose,?_⟩
  intro Ψ SH hSpSH dh hdh ε hε
  have hmax0 : 0 ≤ max Kt Kc := le_max_of_le_left hKt.le
  refine ⟨(2+4*Real.pi)^(geometry_extend_shifted_height_bound (4+cx) 0 g.τ g.τ_pos 0).choose*max Kt Kc,
    mul_nonneg (by positivity) hmax0,?_⟩
  intro Kh hKh
  have hrecev := depth_two_high_record M H hH (ι:=ι) η₀ Q hQM hQ72 hβlo hβhi g.μ g.e g.τ bΦ
    Cycle63.AffineLedger.q hμ hμ1 g.e_pos g.τ_pos hbΦ hq
  obtain ⟨Z₁,-,hZ₁⟩ := CenteredMomentFirstPhysicalLedger.frequency_loss_eventually 32 (g.μ/64) (by norm_num)
    (by positivity)
  have hgap : 0<τlow-2*g.τ := by linarith
  have hpowev : ∀ᶠZ : ℝ in atTop,3*Z^g.τ*Z^g.τ≤Z^τlow := by
    filter_upwards [(tendsto_rpow_atTop hgap).eventually_ge_atTop 3,eventually_gt_atTop (0:ℝ)] with Z h3 hZ0
    have e : Z^τlow=Z^(τlow-2*g.τ)*(Z^g.τ*Z^g.τ) := by
      rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0]; congr 1; ring
    have hz := Real.rpow_nonneg hZ0.le g.τ
    rw [e]
    nlinarith [mul_nonneg hz hz]
  filter_upwards [htop,hcaps,hcev,hrecev,eventually_ge_atTop Z₁,hpowev] with Z htopZ hcapsZ hcZ hrecZ hZ₁' hpowZ
  intro hZ hT θ w σ freq hσ t height hw hwm hheight hfreq state hmod hwidth p X₁ X₂ hX₁ hX₂ hwin hover v₁ τT Tz
    hτT hpres hvnorm s amp length ampP loss hlen hampP hlossge
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  obtain ⟨hmatch,hfitw,hslot,hplane,hcell⟩ := affine_state_bundle_data (κ:=ι) M H hH W hW.continuous hWs η₀ θ w σ
    freq hσ state p (by norm_num) t X₁ X₂ hX₁ hX₂ hZ hwin
  have hgatesE := hcapsZ.2 θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  obtain ⟨caps,-⟩ := actual_affine_low_source_gates (α:=ι) M H hH η₀ θ W hW.continuous hWs w σ freq hσ state p t
    X₁ X₂ hX₁ hX₂ Cs hZ hw hwin hgatesE
  obtain ⟨P,hvP⟩ := DepthTwoPresented.presentation hpres
  subst hvP
  -- the cell of the parent and its amplifier
  have hcellm := Cycle63.AffineLedger.originalCell_mem hslot
  have hb : Cycle63.AffineLedger.firstCellTop≤Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) ∧ Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))≤Cycle63.AffineLedger.slotTop :=
    Cycle63.AffineLedger.cellUpper_bounds hcellm.1 hcellm.2.1
  have hampe : amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j)))) := by
    show Cycle63.AffineLedger.amp _=_
    rw [hcell]
  have hamp0 : 0≤amp := by rw [hampe]; exact (Cycle63.AffineLedger.amp_pos hb).le
  have hamp1 : amp≤1 := by
    rw [hampe]; linarith [(Cycle63.AffineLedger.amp_bounds hb).2, Cycle63.AffineLedger.amplifierCap_le_one]
  have hamp4 : |amp|≤4 := by rw [abs_of_nonneg hamp0]; linarith
  have hfl0 := frequencyLoss_nonneg Z 32 (g.μ/64) hZ (by norm_num) (by positivity)
  have hfl1 := (hZ₁ Z hZ₁').2
  have homega : |frequencyLoss Z 32 (g.μ/64)+g.μ/8|≤4 := by
    rw [abs_of_nonneg (by positivity)]; linarith [g.μ_cap]
  -- the row width and the slots
  have hrow1 : state.rowWidth≤1 := by
    have := state.character_nonneg
    unfold NaturalState.width at hwidth
    linarith
  have hfit : state.rowWidth+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16 := by
    linarith [g.μ_pos]
  have hRcap : (state.puncture.absNorm:ℝ)≤Z^(20:ℝ) :=
    state.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBmask)
  have hlogs (i : ι) : Real.logb Z (s.P i)=w i := by
    rw [hmatch.scale i]
    exact Real.logb_rpow hZ0 hZ.ne'
  have hsum : (∑i,Real.logb Z (s.P i))=∑i,w i := Finset.sum_congr rfl (fun i _=>hlogs i)
  have hw1 (j : ι) : w j≤1 := by
    have hj:=Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)
    have h2:=hslot.2
    rw [hsum] at h2
    linarith [Cycle63.AffineLedger.slotTop_le_one]
  have hwr (j : ι) : w j/31≤1 := by linarith [hw1 j]
  have hwL (j : ι) : w j≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := (hwm j).trans hmesh
  -- the volume of the parent is at most the length
  have hvol : Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤length := by
    obtain ⟨-,-,-,htot,-⟩ := Cycle63.AffineLedger.normalized_cell_bounds one_pos
      (by simpa only [mul_one] using hslot) (by simpa only [mul_one] using hplane)
    rw [CenteredMomentEnergyInputParentCapacity.input_volume_log]
    have h1 := CenteredMomentEnergyInputParentCapacity.raw_log_le_length Z s.X₁ hZ s.X₁_pos
    have h2 := CenteredMomentEnergyInputParentCapacity.raw_log_le_length Z s.X₂ hZ s.X₂_pos
    have h3 : Cycle63.AffineLedger.totalA (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/1)))≤length := by
      rw [div_one, ← hcell]; exact hlen
    simp only [one_mul] at htot
    linarith
  -- the presented heights
  have hTz : 3*Z^g.τ*Z^g.τ≤Tz :=
    hpowZ.trans ((Real.rpow_le_rpow_of_exponent_le hZ.le hτT).trans hpres.1.1)
  -- the records of the two orientations
  have hrc := fun r : Bool => hrecZ.2 hZ hT s state.puncture 1 state.rowWidth amp caps.endpoints squarefree_one
    state.puncture_ne_zero hRcap caps.zero₁ caps.zero₂ caps.sourceCap
    (caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))) hamp0
    (by rw [abs_of_nonneg state.row_nonneg]; linarith) (caps.volumeLog.trans (by norm_num)) hamp4 homega P B Tz
    (state.rowWidth+3*g.δ+ε)
    (g.μ/4+g.μ/4+(2*(g.μ/8)+g.δ+3*((Nbudget:ℝ)+2)*g.δ+130*g.δ+130*g.δ+3*((Nbudget:ℝ)+2)*(2*g.δ))) hvnorm hTz
    hrow1 r
  choose Rb hRpay hRcls hRval using hrc
  let Hb : (b : Bool)→SecondStepHighCount M H hH (fourFixedDictionary η₀) η₀ Z B Tz b P.mult (P.unit b) :=
    fun b => match b with
      | false => Rb true
      | true => Rb false
  refine ⟨P.unit,Hb,?_,?_,?_⟩
  · -- the payments
    intro b
    have hloss : (frequencyLoss Z 32 (g.μ/64)+g.μ/8)+g.μ/4+
        (g.μ/4+g.μ/4+(2*(g.μ/8)+g.δ+3*((Nbudget:ℝ)+2)*g.δ+130*g.δ+130*g.δ+3*((Nbudget:ℝ)+2)*(2*g.δ))+
          (state.rowWidth+3*g.δ+ε))≤loss+state.rowWidth := by
      have hN : (0:ℝ)≤Nbudget := Nat.cast_nonneg _
      nlinarith [hlossge, hloss]
    cases b
    · exact hRpay true length ampP loss hvol hampP hloss
    · exact hRpay false length ampP loss hvol hampP hloss
  · -- the classes
    intro b
    cases b
    · exact hRcls true
    · exact hRcls false
  · -- the HIGH given of the parent
    have hval : ∑b,(Hb b).value=(Rb false).value+(Rb true).value := by
      rw [Fintype.sum_bool]; rfl
    rw [hval]
    exact depth_two_high_given_of_values M H hH (ι:=ι) W hWs hβlo hβhi g η₀ Q hQM hQ72 g.δ Cs Nbudget
      Cycle63.AffineLedger.q Sp SH K Kt Kc ε Kh cx dh Ψ rfl rfl hSp hSpSH hKt hKc hdh hKh Z hZ hT s p caps θ w σ freq
      hmatch state.puncture state.rowWidth amp state.puncture_ne_zero hRcap state.row_nonneg hrow1 hfit height mesh hw
      hwL hwr hmesh0 hwm hσ hheight hfreq hamp0 hamp4 homega htopZ.2 hcZ
      (fun b => (Rb (!b)).value) (fun b => (Rb (!b)).value_nonneg hZ0.le)
      (fun reflected second bin hbin t χ₀ hP hPN => by
        have h := hRval reflected second bin hbin t χ₀ hP hPN
        cases reflected <;> exact h)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
