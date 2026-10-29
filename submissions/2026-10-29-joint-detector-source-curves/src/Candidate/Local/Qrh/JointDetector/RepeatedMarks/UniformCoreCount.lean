/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceSupportedCount
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateContinuity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

/-! One early physical mesh for the genuine repeated count. The repetition
budget precedes the finite slot type; only constants and scale thresholds
see the eventual number of slots. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorClassBudget
open QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem supported_count_at_loss
    (B L c νmin dmin smin loss : ℝ) (hL : 3/2≤L) (hB0 : 0≤B) (hB : B≤1)
    (hc0 : 0≤c) (hc : c≤1/6) (hνmin : 0<νmin) (hdmin : 0<dmin) (hsmin : 0<smin) (hloss : 0<loss)
    (hsource : GlobalSource B L c) (hβglobal : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃ meshMax β εMax : ℝ,0<meshMax ∧ 0<β ∧ β≤dmin/4 ∧ 0<εMax ∧
    ∀mesh : ℝ,0≤mesh → mesh≤meshMax →
    ∀{Label Slot : Type}[Fintype Label][Nonempty Label][Fintype Slot][DecidableEq Slot],
    ∀(M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
      (Aroot : ℝ),0≤Aroot → ∀(base anchor : Label→Character)(bad : Label→Ideal O),
    (∀j,bad j≤M) → (∀j,internalQ (bad j) (anchor j)≠0) →
    (∀j,internalQ (bad j) (anchor j)≠⊤) →
    (∀j,internalQ (bad j) (anchor j)≤Ideal.span {(72:O)}) →
    ∀(W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W⊆Icc (1:ℝ) 2 →
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
    ∀N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
    (∀s∈N.slots,N.widths s≤mesh) → ∀χ : FreeRow→Label→Character,
    ∀(a ε tstar T allowance : ℝ)(i : ℕ),1/2≤a → 0≤ε → ε≤εMax →
    ∀witness : ∀u,SupportedWitness (χ u) U a ε tstar T allowance i,
    ∀reverse : Label→Bool,(∀u∈N.rows,∀j I,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff (N.family u j) I) else idealCoeff (N.family u j) I) →
    ∀v height : ℝ,νmin≤2*a-1 → 2*a-1≤3/4 → dmin≤v → v≤2*a-1 → 0≤height →
    (∀s∈N.slots,|N.commonHeight+N.relativeHeight s|≤height) →
    smin≤∑s∈N.slots,N.widths s →
    (∀u∈N.rows,U^(v*(∑s∈N.slots,N.widths s))≤∏s∈N.slots,‖N.Q u s‖^2) →
    tstar=max (crossingCut (2*a-1) ((v-β)/(2*(2*a-1))) 2 (2*((v-β)/(2*(2*a-1)))*c))
      (crossingCut (2*a-1) ((v-β)/(2*(2*a-1))) (2-4*((v-β)/(2*(2*a-1)))/L)
        (2*((v-β)/(2*(2*a-1)))*B/L)) →
    1≤tstar → tstar≤3/2 → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
    (N.rows.card:ℝ)≤C*(1+height)^J*U^(rawRepeatedCountRate B L c (2*a-1) v+loss) := by
  obtain ⟨η,hη,hbuffer⟩ := rawRate_buffer (B:=B) (c:=c) hL hνmin (show 0<loss/10 by positivity)
  let β := min (dmin/4) (η/2)
  have hβ : 0<β := lt_min (by positivity) (by positivity)
  have hβd : β≤dmin/4 := min_le_left _ _
  have hβη : β<η := (min_le_right _ _).trans_lt (by linarith)
  let εm := loss/100
  have hεm : 0<εm := by dsimp [εm];positivity
  obtain ⟨parentMesh,hparentMesh,hparent⟩ := hsource (εm/2) (by positivity)
  let meshMax := min parentMesh (loss/100)
  let εMax := min (min (1/1000:ℝ) (νmin/2000)) (loss/1000)
  have hmeshMax : 0<meshMax := lt_min hparentMesh (by positivity)
  have hεMax : 0<εMax := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  let τ := loss/100
  have hτ : 0<τ := by dsimp [τ];positivity
  let lossSlot := β*smin/8
  have hlossSlot : 0<lossSlot := by dsimp [lossSlot];positivity
  let K : ℕ := ⌈1/(β*smin/2)+1⌉₊
  have hK : 1/(β*smin/2)+1≤(K:ℝ) := Nat.le_ceil _
  refine ⟨meshMax,β,εMax,hmeshMax,hβ,hβd,hεMax,?_⟩
  intro mesh hm hmesh Label Slot instL neL instS decS M instM H hH Aroot hAr base anchor bad hQM hQ0 hQt hQ72 W hW hWs
  have hmeshParent : mesh≤parentMesh := hmesh.trans (min_le_left _ _)
  have hmeshLoss : mesh≤loss/100 := hmesh.trans (min_le_right _ _)
  have hsrc : UnitFaceSource (globalFace B L c) mesh (εm/2) := hparent.mono_mesh hmeshParent
  obtain ⟨J,C,hC,hcount⟩ := source_supported_count (Slot:=Slot) M H hH B L c mesh εm Aroot νmin hL hεm hAr
    hB0 hB hc0 hc hνmin hsrc hβglobal base anchor bad hQM hQ0 hQt hQ72 W hW hWs K
  obtain ⟨Ctriv,hCtriv,htriv⟩ := ActualCoreCount.trivial_response_bound W hWs hW.continuous
  let step := lossSlot/((Fintype.card Slot:ℝ)+1)
  have hstep : 0<step := by dsimp [step];positivity
  have hbig : ∀ᶠU : ℝ in atTop,Ctriv≤U^step :=
    (tendsto_rpow_atTop hstep).eventually (eventually_ge_atTop Ctriv)
  obtain ⟨Kd,hKd,hdyadic⟩ := dyadic_cost_eventually (loss/2) (by positivity)
  let Cfinal := (Kd+1)*C*(Fintype.card Label:ℝ)
  have hCard : 0<(Fintype.card Label:ℝ) := by exact_mod_cast Fintype.card_pos
  have hCfinal : 0<Cfinal := by dsimp [Cfinal];positivity
  refine ⟨J,Cfinal,hCfinal,?_⟩
  filter_upwards [hcount,hbig,hdyadic] with U hcount hbig hdyadic
  refine ⟨hcount.1,?_⟩
  intro N hwm χ a ε tstar T allowance i ha hε hεmax witness reverse hχ v height hνlow hνhi hvmin hv hh hphase hS hresponse htstar ht0 ht1 hfreq
  let δ := v-β
  have hδ : 0≤δ := by dsimp [δ];linarith
  have hδν : δ≤2*a-1 := by dsimp [δ];linarith
  have hν : 0<2*a-1 := hνmin.trans_le hνlow
  have herror : (∑s∈N.slots,step)≤lossSlot := by
    rw [Finset.sum_const,nsmul_eq_mul]
    have hc : (N.slots.card:ℝ)≤Fintype.card Slot := by exact_mod_cast Finset.card_le_univ N.slots
    dsimp [step]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<(Fintype.card Slot:ℝ)+1)).mpr
    have hh' := mul_le_mul_of_nonneg_right hc hlossSlot.le
    nlinarith only [hh',hlossSlot.le]
  have hupper : ∀u∈N.rows,∀s∈N.slots,‖N.Q u s‖^2≤U^(N.widths s+step) := by
    intro u hu s hs
    calc _ ≤ Ctriv*U^(N.widths s) := htriv M H hH base anchor bad U Aroot hcount.1 N u hu s hs
      _ ≤ U^step*U^(N.widths s) := mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg (zero_lt_one.trans hcount.1).le _)
      _ = _ := by rw [←Real.rpow_add (zero_lt_one.trans hcount.1)];congr 1;ring
  have hlower : ∀u∈N.rows,U^((δ+β)*(∑s∈N.slots,N.widths s)-lossSlot)≤∏s∈N.slots,‖N.Q u s‖^2 := by
    intro u hu
    apply (Real.rpow_le_rpow_of_exponent_le hcount.1.le ?_).trans (hresponse u hu)
    dsimp [δ]
    linarith
  have hε1 : ε≤1/1000 := hεmax.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεν : ε≤νmin/2000 := hεmax.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεloss : ε≤loss/1000 := hεmax.trans (min_le_right _ _)
  have he := hcount.2 N hwm χ a ε tstar T allowance i ha hε hε1 hεν witness reverse hχ
    δ β smin lossSlot τ height (fun _=>step) hh hphase hνlow hνhi hδ hδν hτ
    (fun _ _=>hstep.le) hβ hsmin hS hupper herror hlower
    (by dsimp [lossSlot];nlinarith [mul_pos hβ hsmin]) hm hK htstar ht0 ht1 hfreq
  have hdom : (2*a-1,v)∈rateDomain νmin := ⟨hνlow,hνhi,hdmin.le.trans hvmin,hv⟩
  have hdomδ : (2*a-1,δ)∈rateDomain νmin := ⟨hνlow,hνhi,hδ,hδν⟩
  have hrate := hbuffer (2*a-1) δ (2*a-1) v hdomδ hdom (by simpa using hη)
    (by simpa [δ,abs_neg,abs_of_pos hβ] using hβη)
  have hrate' : rawRepeatedCountRate B L c (2*a-1) δ≤rawRepeatedCountRate B L c (2*a-1) v+loss/10 := by
    have hh' := (abs_lt.mp hrate).2
    linarith
  have hδτ : δ*τ≤(3/4)*(loss/100) := by
    dsimp [τ]
    exact mul_le_mul_of_nonneg_right (hδν.trans hνhi) (by positivity)
  have hδmesh : δ*mesh≤(3/4)*(loss/100) :=
    mul_le_mul (hδν.trans hνhi) hmeshLoss hm (by norm_num)
  have hexp : rawRepeatedCountRate B L c (2*a-1) δ+200*ε+δ*τ+δ*mesh+εm ≤
      rawRepeatedCountRate B L c (2*a-1) v+loss/2 := by
    dsimp [εm]
    linarith only [hrate',hεloss,hδτ,hδmesh,hloss]
  have hUp : 0<U := zero_lt_one.trans hcount.1
  have hD : C*(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*(1+height)^J ≤
      C*(Fintype.card Label:ℝ)*(Kd*U^(loss/2))*(1+height)^J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdyadic (by positivity)) (by positivity)
  apply he.trans
  calc _ ≤ (C*(Fintype.card Label:ℝ)*(Kd*U^(loss/2))*(1+height)^J)*
      U^(rawRepeatedCountRate B L c (2*a-1) v+loss/2) :=
      mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le hcount.1.le hexp)
        (Real.rpow_nonneg hUp.le _) (by positivity)
    _ = (Kd*C*(Fintype.card Label:ℝ))*(1+height)^J*
        U^(rawRepeatedCountRate B L c (2*a-1) v+loss) := by
      rw [Real.rpow_add hUp (rawRepeatedCountRate B L c (2*a-1) v) loss,
        Real.rpow_add hUp (rawRepeatedCountRate B L c (2*a-1) v) (loss/2),
        show U^loss=U^(loss/2)*U^(loss/2) by rw [←Real.rpow_add hUp];congr 1;ring]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [Cfinal];nlinarith [mul_pos hC hCard]) (by positivity))
      (Real.rpow_nonneg hUp.le _)

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.supported_count_at_loss
