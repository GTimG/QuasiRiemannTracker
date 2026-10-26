import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighGiven
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondStepBody
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.SecondStepState
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoHighRebase
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The second step at the ledger of one grid position, from the generic step and the HIGH given read in the unit of the
state. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeSlot CenteredMomentInductionEnergy

/-- The old moment `Zp^(1+εc)` plus the HIGH term `Chigh*Zp^e*(Kh*(Zp^(-e)*V+1))` of the generic step, with the HIGH
given bounding the HIGH part by `Kh*(Zp^(-e)*V+1)` for the count `V` of the records, is at most `1+Chigh*Kh` times a
bound `Kold` of the old moment plus the count `V`, when `1 ≤ Zp` and `e ≤ 1+εc`. -/
theorem second_step_unit_terms {Zp e εc Chigh Kh V Kold : ℝ} (hZp : 1 ≤ Zp) (he : e ≤ 1 + εc) (hChigh : 0 ≤ Chigh)
    (hKh : 0 ≤ Kh) (hV : 0 ≤ V) (hold : Zp ^ (1 + εc) ≤ Kold) :
    Zp ^ (1 + εc) + Chigh * Zp ^ e * (Kh * (Zp ^ (-e) * V + 1)) ≤ (1 + Chigh * Kh) * (Kold + V) := by
  have hZ0 : 0 < Zp := zero_lt_one.trans_le hZp
  have hcancel : Zp ^ e * Zp ^ (-e) = 1 := by
    rw [← Real.rpow_add hZ0]
    simp
  have hpow : Zp ^ e ≤ Zp ^ (1 + εc) := Real.rpow_le_rpow_of_exponent_le hZp he
  have hA : 0 ≤ Zp ^ (1 + εc) := Real.rpow_nonneg hZ0.le _
  have hCK : 0 ≤ Chigh * Kh := mul_nonneg hChigh hKh
  have hexp : Chigh * Zp ^ e * (Kh * (Zp ^ (-e) * V + 1)) = Chigh * Kh * V + Chigh * Kh * Zp ^ e := by
    calc Chigh * Zp ^ e * (Kh * (Zp ^ (-e) * V + 1))
        = Chigh * Kh * ((Zp ^ e * Zp ^ (-e)) * V) + Chigh * Kh * Zp ^ e := by ring
      _ = _ := by rw [hcancel]; ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left hpow hCK, mul_le_mul_of_nonneg_left hold hCK]

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance secondStepLedgerFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
omit [Fintype α] in
/-- The bound of the second step for the states of a part of the applicable states, at the ledger of the part, from the
generic step at the unit base `Z^width` of the state and the count form of its HIGH part: for all large `Z`, a state of
width `W` between `2/5` and `Mcap` is seen at the base `Z^W`, where its width is one, the generic step bounds its energy
by the old moment plus the HIGH term, the HIGH term is the count form of the records, and the records are read at the
base `Z`. The part `Part` asks of the state the presentation, the window of the ledger and the amplifier and length
of the ledger in the unit `W`. -/
theorem second_step_body_of_given
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)
    (ap bp bΦ Bwide Bmask Bpun Bv L Lslot lo hi Mcap εold εc mesh τT lossFloor B lossNeeded Bnorm Kcl Kh C Chigh : ℝ)
    (hap : 0<ap) (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh degree : ℕ) (S : Finset (ℕ×ℕ))
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop)
    (Part : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hlo : 33/50≤lo) (hhi : hi≤33/50) (hMcap : 0<Mcap) (hεc : 0<εc) (hεold : Mcap*εc≤εold)
    (hBpun : 0≤Bpun) (hBwide : 5/2*Bpun≤Bwide) (hBv0 : 0≤Bv) (hBv : 5/2*Bv≤B-130) (hmeshL : 5/2*Lslot≤ mesh)
    (hτ : 2*g.τ<τT/Mcap) (hB : 0≤B) (hBnorm : Mcap*B≤Bnorm) (hlossNeeded : 0≤lossNeeded)
    (hloss : Mcap*(lossNeeded+εc)≤lossFloor)
    (hC : 0<C) (hChigh : 0≤Chigh) (hKh : 0≤Kh)
    (hPres : ∀ (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O) (T : ℝ), Presented η₀ Z s v₁ T →
      DepthTwoPresented τT η₀ Z s v₁ T ∧ (s.puncture.absNorm : ℝ)≤Z^Bpun ∧
        ((Ideal.span {v₁}).absNorm : ℝ)≤Z^Bv)
    (hPart : ∀ (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O) (x₁ x₂ z Wd T len ampB loss : ℝ),
      Part η₀ Z s v₁ x₁ x₂ z Wd T len ampB loss →
      Wd=s.width ∧ 2/5≤Wd ∧ Presented η₀ Z s v₁ T ∧ lossFloor≤loss ∧
      x₁+x₂+6*Cycle63.Optimization.slotPrice*z-Wd≤7/2500 ∧
      Cycle63.AffineLedger.PlainWindow (x₁/Wd) (x₂/Wd) (z/Wd) ∧
      Cycle63.AffineLedger.totalA (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (z/Wd)))*Wd≤len ∧
      Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (z/Wd)))*Wd≤ampB ∧
      3*g.δ≤Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (z/Wd))))
    (hevAt : ∀ᶠZ : ℝ in atTop,
      GeometryAffineAtState (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bwide mesh εc hap Ψ SH dh degree S C Chigh η₀ Q
        hQM hQ72 Z)
    (hevGiven : ∀ᶠZ : ℝ in atTop,
      DepthTwoHighGivenAt (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bwide mesh εc (τT/Mcap) B lossNeeded hap Ψ SH dh
        Kcl Kh η₀ Q hQM hQ72 Z) :
    ∀ᶠZ : ℝ in atTop,
      SecondStepBody (α:=α) M H hH fourFixedDictionary W 2 ap bp bΦ Bmask L Lslot lo hi Mcap εold Bnorm Part Kcl degree
        S (C*(1+Chigh*Kh)) η₀ Q Z := by
  have hτg : 0<g.τ := g.τ_pos
  have hev : ∀ᶠZ' : ℝ in atTop, 1<Z' ∧ 2<Z'^g.τ ∧
      GeometryAffineAtState (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bwide mesh εc hap Ψ SH dh degree S C Chigh η₀ Q
        hQM hQ72 Z' ∧
      DepthTwoHighGivenAt (α:=α) M H hH W hW hWs hβlo hβhi g ap bp bΦ Bwide mesh εc (τT/Mcap) B lossNeeded hap Ψ SH dh
        Kcl Kh η₀ Q hQM hQ72 Z' :=
    (eventually_gt_atTop (1:ℝ)).and (((tendsto_rpow_atTop hτg).eventually (eventually_gt_atTop (2:ℝ))).and
      (hevAt.and hevGiven))
  filter_upwards [eventually_rpow_ge hev (by norm_num : (0:ℝ)<2/5)] with Z hZ
  obtain ⟨hZ1, hZc⟩ := hZ
  refine ⟨hZ1, ?_⟩
  intro U θ w σ v t height hw0 hwL hσlo hσhi hh hv s hs hsM p X₁ X₂ hX₁ hX₂ hL₁ hL₂ v₁ T Wd len ampB loss happ
  obtain ⟨rfl, h25, hpres, hlossF, hover, hwin, htot, hampB, h3δ⟩ :=
    hPart η₀ Z s v₁ _ _ _ Wd T len ampB loss happ
  obtain ⟨hpresT, hpun, hnv⟩ := hPres η₀ Z s v₁ T hpres
  have hWpos : 0 < s.width := by linarith
  have hZ0 : 0<Z := zero_lt_one.trans hZ1
  have hmask : (s.puncture.absNorm : ℝ)≤(Z^s.width)^Bwide :=
    le_rpow_rpow_of_le_mul hZ1.le hpun
      (by nlinarith [mul_nonneg (sub_nonneg.2 h25) (by linarith : (0:ℝ)≤Bwide)])
  have hnv' : ((Ideal.span {v₁}).absNorm : ℝ)≤(Z^s.width)^(B-130) :=
    le_rpow_rpow_of_le_mul hZ1.le hnv
      (by nlinarith [mul_nonneg (sub_nonneg.2 h25) (by linarith [hBv, hBv0] : (0:ℝ)≤B-130)])
  obtain ⟨hZ', hT', hAtZ, hGivenZ⟩ := hZc s.width h25
  have hu1 : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask).width≤1 := (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState_width s hWpos Bwide hmask).le
  have hurow : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask).rowWidth≤1 := _root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState_rowWidth_le_one s hWpos Bwide hmask
  obtain ⟨w', hw'⟩ : ∃ w' : ↥U→ℝ, ∀ i, w' i=w i/s.width := ⟨fun i => w i/s.width, fun _ => rfl⟩
  have hσ' : ∀ i : ↥U, σ i∈Set.Icc (33/50:ℝ) (33/50) := fun i => ⟨hlo.trans (hσlo i), (hσhi i).trans hhi⟩
  have hw0' : ∀ i : ↥U, 0≤w' i := fun i => by rw [hw']; exact div_nonneg (hw0 i) hWpos.le
  have hwm : ∀ i : ↥U, w' i ≤ mesh := by
    intro i
    have hL0 : 0≤Lslot := (hw0 i).trans (hwL i)
    have hmesh0 : 0 ≤ mesh := by linarith
    rw [hw', div_le_iff₀ hWpos]
    nlinarith [hwL i, mul_le_mul_of_nonneg_left h25 hmesh0]
  have hsum : ∑ i : ↥U, w' i=(∑ i∈U, w i)/s.width := by
    simp only [hw']
    rw [← Finset.sum_div]
    exact congrArg (· / s.width) (Finset.sum_coe_sort U w)
  have hlen : ∀ X : ℝ, length (Z^s.width) X=length Z X/s.width := fun X => length_rpow hZ0 X
  have hwin' : Cycle63.AffineLedger.PlainWindow (length (Z^s.width) X₁) (length (Z^s.width) X₂) (∑ i : ↥U, w' i) := by
    rw [hlen, hlen, hsum]
    exact hwin
  have hover' : length (Z^s.width) X₁+length (Z^s.width) X₂+6*Cycle63.Optimization.slotPrice*(∑ i : ↥U, w' i)≤
      1+7/1000 := by
    rw [hlen, hlen, hsum]
    have hcomb : length Z X₁/s.width+length Z X₂/s.width+6*Cycle63.Optimization.slotPrice*((∑ i∈U, w i)/s.width)=
        (length Z X₁+length Z X₂+6*Cycle63.Optimization.slotPrice*∑ i∈U, w i)/s.width := by ring
    rw [hcomb, div_le_iff₀ hWpos]
    nlinarith [hover, h25]
  have hpres' : DepthTwoPresented (τT/s.width) η₀ (Z^s.width) (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask) v₁ T :=
    hpresT.unitState hWpos Bwide hmask
  have hτT : 0≤τT := by
    have h1 : 0<τT/Mcap := by linarith
    have h2 := mul_pos h1 hMcap
    rw [div_mul_cancel₀ _ hMcap.ne'] at h2
    exact h2.le
  have hτlow : τT/Mcap≤τT/s.width := div_le_div_of_nonneg_left hτT hWpos hsM
  have htot' : Cycle63.AffineLedger.totalA (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑ i : ↥U, w' i)))≤len/s.width := by
    rw [hsum, le_div_iff₀ hWpos]
    exact htot
  have hamp' : Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑ i : ↥U, w' i)))≤ampB/s.width := by
    rw [hsum, le_div_iff₀ hWpos]
    exact hampB
  have hloss' : lossNeeded+εc≤loss/s.width := by
    rw [le_div_iff₀ hWpos]
    nlinarith [mul_le_mul_of_nonneg_left hsM (by linarith : 0≤lossNeeded+εc)]
  obtain ⟨unit, Hb, hpays, hcard, hgiven⟩ := hGivenZ hZ' hT' U (fun i => θ i) w' (fun i => σ i) (fun i => v i) hσ' t
    height hw0' hwm hh (fun i => hv i) (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask) hs hu1 p X₁ X₂ hX₁ hX₂ hwin' hover' v₁
    (τT/s.width) T hτlow hpres' hnv' (len/s.width) (ampB/s.width) (loss/s.width) htot' hamp' hloss'
  have hV0 : 0≤∑ b, (Hb b).value := Finset.sum_nonneg fun b _ => (Hb b).value_nonneg (zero_lt_one.trans hZ').le
  obtain hE := hAtZ hZ' hT' U (fun i => θ i) w' (fun i => σ i) (fun i => v i) hσ' t height hw0' hwm hh
    (fun i => hv i) (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask) hs hu1 p X₁ X₂ hX₁ hX₂ hwin' hover' _
    (by exact mul_nonneg hKh (add_nonneg (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ').le _) hV0) zero_le_one))
    hgiven
  have hpow : ∀ i : ↥U, (Z^s.width)^(w' i)=Z^(w i) := fun i => by
    rw [hw']
    exact rpow_rpow_div hZ0.le hWpos.ne' _
  simp only [hpow] at hE
  have hold : (Z^s.width)^(1+εc)≤Z^(s.width+εold) := by
    rw [← Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by nlinarith [mul_le_mul_of_nonneg_right hsM hεc.le])
  have he : (_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState s hWpos Bwide hmask).rowWidth+3*g.δ-Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑ i : ↥U, w' i)))+εc≤1+εc := by
    have h1 : 3*g.δ≤Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑ i : ↥U, w' i))) := by
      rw [hsum]
      exact h3δ
    linarith
  have hterms := second_step_unit_terms (Zp:=Z^s.width) (Chigh:=Chigh) (Kh:=Kh) (V:=∑ b, (Hb b).value)
    (Kold:=Z^(s.width+εold)) hZ'.le he hChigh hKh hV0 hold
  have hBcap : s.width*B≤Bnorm := (mul_le_mul_of_nonneg_right hsM hB).trans hBnorm
  refine ⟨unit, fun b => (Hb b).rebase hZ1.le hWpos hBcap, fun b => ?_, fun b => hcard b, ?_⟩
  · have h1 := (Hb b).rebase_pays hZ1.le hWpos hBcap (hpays b)
    have hscale : ∀ x : ℝ, s.width*(x/s.width)=x := fun x => by field_simp
    simpa only [_root_.Record1252270103Bootstrap.PR67.OAI.SevenEighths.CenteredMomentEnergyState.NaturalState.unitState_rowWidth s hWpos Bwide hmask, hscale] using h1
  · have hF : 0≤C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree :=
      mul_nonneg (mul_nonneg (mul_nonneg hC.le (diagonalControl_nonneg _)) (sq_nonneg _))
        (pow_nonneg (by linarith [abs_nonneg t]) _)
    calc _ ≤ _ := hE
      _ ≤ C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
          ((1+Chigh*Kh)*(Z^(s.width+εold)+∑ b, (Hb b).value)) := mul_le_mul_of_nonneg_left hterms hF
      _ = C*(1+Chigh*Kh)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
          (Z^(s.width+εold)+∑ b, ((Hb b).rebase hZ1.le hWpos hBcap).value) := by
        simp only [SecondStepHighCount.rebase_value]
        ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
