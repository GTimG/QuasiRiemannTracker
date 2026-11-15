/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The continuum rational line's exact improved count window.
Specializes the frozen FiniteWindow formulas to the new certified source. Adapted from
Sil's PR137 ImprovedWindowQ (copyright (c) 2026 Sil, Apache-2.0), using
ArviFoxy's rational Bernstein engine and Hailey Collet's window contracts
(Apache-2.0). Only the admitted source line is changed. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalFiber
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Tuning.CoverQ
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.CountWidth

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ContinuumQ
noncomputable section
open Qrh.TwoSlot.AnchorContinuum
open Set QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning QRH.ArviReturnTuning
open QRH.Record1252270103Return (plainCurve)
open Qrh.MarkedAnchor.Interface (anchorLeft anchorTop)

/-! ### Real formulas -/

def kI (p : ℝ) : ℝ := 1-p*(1+2*rationalLine.g1)
def aI (p : ℝ) : ℝ := p*(1+2*rationalLine.g0)
def UI (p : ℝ) : ℝ := 1-p*(1+6*rationalLine.g0-4*rationalLine.g1)
def JI (δ p : ℝ) : ℝ := 3*(5/6-δ)+2*δ*kI p
def NI (δ p : ℝ) : ℝ := (1-δ)*JI δ p+(5/6-δ)*δ*UI p
def TI (δ p : ℝ) : ℝ := JI δ p+δ*UI p
def valueI (δ p : ℝ) : ℝ := NI δ p/JI δ p
def cutoffI (δ p : ℝ) : ℝ := TI δ p/JI δ p
def crossingI (δ p : ℝ) : ℝ := 2*TI δ p/(3*JI δ p)
def dUI : ℝ := -(1+6*rationalLine.g0-4*rationalLine.g1)
def dJI (δ : ℝ) : ℝ := -2*δ*(1+2*rationalLine.g1)

theorem JI_pos {δ p : ℝ} (hδ : δ∈Icc (0:ℝ) (3/4)) (hp : p∈Icc (0:ℝ) (1/2)) : 0<JI δ p := by
  have h1 : 0≤δ*p := mul_nonneg hδ.1 hp.1
  have h2 : δ*p≤3/4*(1/2) := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num)
  unfold JI kI rationalLine
  norm_num [Qrh.TwoSlot.AnchorContinuum.RationalSource.g1] at *
  nlinarith [hδ.1, hδ.2, hp.1, hp.2]

/-! ### Rational polynomials -/

def g0Q : ℚ := Qrh.TwoSlot.AnchorContinuum.RationalSource.g0
def g1Q : ℚ := Qrh.TwoSlot.AnchorContinuum.RationalSource.g1
def leftQ : ℚ := 1467/2000
def topQ : ℚ := 311/400

open Q2 in
def kQ : Q2 := sub (C 1) (smul (1+2*g1Q) Y)
open Q2 in
def VQ : Q2 := sub (C (5/6)) X
open Q2 in
def JQ : Q2 := add (smul 3 VQ) (smul 2 (mul X kQ))
open Q2 in
def UQ : Q2 := sub (C 1) (smul (1+6*g0Q-4*g1Q) Y)
open Q2 in
def NQ : Q2 := add (mul (sub (C 1) X) JQ) (mul (mul VQ X) UQ)
open Q2 in
def TQ : Q2 := add JQ (mul X UQ)

open Q2 in
/-- `N - (1 - δ L(p)) J` for an affine `L(p) = c0 + c1 p`. -/
def belowQ (c0 c1 : ℚ) : Q2 := sub NQ (mul (sub (C 1) (mul X (add (C c0) (smul c1 Y)))) JQ)

open Q2 in
def gQ : Fin 10 → Q2 := ![kQ, JQ, sub TQ JQ, sub (smul (12499/10000) JQ) TQ,
  sub (smul 2 TQ) (smul (3*(leftQ+1/1000000)) JQ),
  belowQ topQ (1-topQ),
  belowQ topQ (2*(countBQ-topQ)/countLQ),
  belowQ topQ (2*(countCapQ-1/10000000)),
  sub NQ (mul (sub (sub (C 1) (smul (2*naturalMQ) X)) (smul (2*sMinusQ) (mul X Y))) JQ),
  sub (mul UQ (smul (-2*(1+2*g1Q)) X)) (smul (-(1+6*g0Q-4*g1Q)) JQ)]

theorem cast_g0 : ((g0Q:ℚ):ℝ)=rationalLine.g0 := by norm_num [g0Q,rationalLine]
theorem cast_g1 : ((g1Q:ℚ):ℝ)=rationalLine.g1 := by norm_num [g1Q,rationalLine]
theorem cast_left : ((leftQ:ℚ):ℝ)=anchorLeft := by norm_num [leftQ,anchorLeft]
theorem cast_top : ((topQ:ℚ):ℝ)=anchorTop := by norm_num [topQ,anchorTop]
theorem cast_countB : ((countBQ:ℚ):ℝ)=countCB := by norm_num [countBQ,countCB]
theorem cast_countL : ((countLQ:ℚ):ℝ)=countCL := by norm_num [countLQ,countCL]
theorem cast_countCap : ((countCapQ:ℚ):ℝ)=countCap := by norm_num [countCapQ,countCap]
theorem cast_sMinus : ((sMinusQ:ℚ):ℝ)=sMinus := by norm_num [sMinusQ,sMinus]

section
variable (δ p : ℝ)

theorem ev_kQ : Q2.ev kQ δ p=kI p := by
  simp only [kQ,Q2.ev_sub,Q2.ev_smul,Q2.ev_C,Q2.ev_Y]; push_cast; rw [cast_g1]; unfold kI; ring
theorem ev_VQ : Q2.ev VQ δ p=5/6-δ := by
  simp only [VQ,Q2.ev_sub,Q2.ev_C,Q2.ev_X]; push_cast; ring
theorem ev_JQ : Q2.ev JQ δ p=JI δ p := by
  simp only [JQ,Q2.ev_add,Q2.ev_smul,Q2.ev_mul,Q2.ev_X,ev_VQ,ev_kQ]; push_cast; unfold JI; ring
theorem ev_UQ : Q2.ev UQ δ p=UI p := by
  simp only [UQ,Q2.ev_sub,Q2.ev_smul,Q2.ev_C,Q2.ev_Y]; push_cast; rw [cast_g0,cast_g1]; unfold UI; ring
theorem ev_NQ : Q2.ev NQ δ p=NI δ p := by
  simp only [NQ,Q2.ev_add,Q2.ev_sub,Q2.ev_mul,Q2.ev_C,Q2.ev_X,ev_VQ,ev_JQ,ev_UQ]; push_cast
  unfold NI; ring
theorem ev_TQ : Q2.ev TQ δ p=TI δ p := by
  simp only [TQ,Q2.ev_add,Q2.ev_mul,Q2.ev_X,ev_JQ,ev_UQ]; unfold TI; ring
theorem ev_belowQ (c0 c1 : ℚ) :
    Q2.ev (belowQ c0 c1) δ p=NI δ p-(1-δ*((c0:ℝ)+(c1:ℝ)*p))*JI δ p := by
  simp only [belowQ,Q2.ev_add,Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_C,Q2.ev_X,Q2.ev_Y,ev_NQ,ev_JQ]
  push_cast; ring

end

/-! ### The kernel checks of the ten guards on the window -/

def dloQ : ℚ := 189/512
def dhiQ : ℚ := 15/32
def ploQ : ℚ := 15/32

theorem guards_ok : (List.finRange 10).all (fun j => posBox (gQ j) 0 dloQ dhiQ ploQ (1/2)) = true := by
  decide +kernel

theorem guard_pos (j : Fin 10) {δ p : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) (hp : p∈Icc (15/32:ℝ) (1/2)) :
    0<Q2.ev (gQ j) δ p := by
  have h := guards_ok
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact posBox_sound _ 0 dloQ dhiQ ploQ (1/2) (h j) (by simpa [dloQ] using hδ.1)
    (by simpa [dhiQ] using hδ.2) (by simpa [ploQ] using hp.1) (by simpa using hp.2)

/-! ### The improved window -/

section
variable {δ p : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) (hp : p∈Icc (15/32:ℝ) (1/2))
include hδ hp

theorem hk : 0<kI p := by have := guard_pos 0 hδ hp; rwa [show gQ 0=kQ from rfl,ev_kQ] at this
theorem hJ : 0<JI δ p := by have := guard_pos 1 hδ hp; rwa [show gQ 1=JQ from rfl,ev_JQ] at this
theorem hT1 : JI δ p<TI δ p := by
  have := guard_pos 2 hδ hp
  rw [show gQ 2=Q2.sub TQ JQ from rfl,Q2.ev_sub,ev_TQ,ev_JQ] at this; linarith
theorem hT2 : TI δ p<12499/10000*JI δ p := by
  have := guard_pos 3 hδ hp
  rw [show gQ 3=Q2.sub (Q2.smul (12499/10000) JQ) TQ from rfl,Q2.ev_sub,Q2.ev_smul,ev_TQ,ev_JQ] at this
  push_cast at this; linarith
theorem hcross : (anchorLeft+1/1000000)*(3*JI δ p)<2*TI δ p := by
  have := guard_pos 4 hδ hp
  rw [show gQ 4=Q2.sub (Q2.smul 2 TQ) (Q2.smul (3*(leftQ+1/1000000)) JQ) from rfl,Q2.ev_sub,
    Q2.ev_smul,Q2.ev_smul,ev_TQ,ev_JQ] at this
  push_cast at this; rw [cast_left] at this; linarith
theorem hnat : (1-δ*(p+(1-p)*anchorTop))*JI δ p<NI δ p := by
  have := guard_pos 5 hδ hp
  rw [show gQ 5=belowQ topQ (1-topQ) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top] at this; linarith
theorem hplain1 : (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p<NI δ p := by
  have := guard_pos 6 hδ hp
  rw [show gQ 6=belowQ topQ (2*(countBQ-topQ)/countLQ) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top,cast_countB,cast_countL] at this; linarith
theorem hplain0 : (1-δ*(anchorTop+2*(countCap-1/10000000)*p))*JI δ p<NI δ p := by
  have := guard_pos 7 hδ hp
  rw [show gQ 7=belowQ topQ (2*(countCapQ-1/10000000)) from rfl,ev_belowQ] at this
  push_cast at this; rw [cast_top,cast_countCap] at this; linarith
theorem htail : (1-2*δ*naturalM-2*δ*p*sMinus)*JI δ p<NI δ p := by
  have := guard_pos 8 hδ hp
  rw [show gQ 8=Q2.sub NQ (Q2.mul (Q2.sub (Q2.sub (Q2.C 1) (Q2.smul (2*naturalMQ) Q2.X))
    (Q2.smul (2*sMinusQ) (Q2.mul Q2.X Q2.Y))) JQ) from rfl] at this
  simp only [Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_C,Q2.ev_X,Q2.ev_Y,ev_NQ,ev_JQ] at this
  push_cast at this; rw [cast_naturalMQ,cast_sMinus] at this; linarith
theorem hanti : 0<UI p*dJI δ-dUI*JI δ p := by
  have := guard_pos 9 hδ hp
  rw [show gQ 9=Q2.sub (Q2.mul UQ (Q2.smul (-2*(1+2*g1Q)) Q2.X)) (Q2.smul (-(1+6*g0Q-4*g1Q)) JQ)
    from rfl] at this
  simp only [Q2.ev_sub,Q2.ev_mul,Q2.ev_smul,Q2.ev_X,ev_UQ,ev_JQ] at this
  push_cast at this; rw [cast_g0,cast_g1] at this; unfold dJI dUI; linarith

end

theorem crossing_eq (δ p : ℝ) (hJ : JI δ p≠0) :
    2*(cutoffI δ p-crossingI δ p)=crossingI δ p := by
  unfold cutoffI crossingI; field_simp; ring

theorem inverse_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ*(p*(1+2*rationalLine.g0)+(1-p*(1+2*rationalLine.g1))*crossingI δ p)=valueI δ p := by
  unfold crossingI valueI; field_simp; unfold NI TI JI UI kI; ring

theorem long_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ+(5/6-δ)*(cutoffI δ p-1)=valueI δ p := by
  unfold cutoffI valueI; field_simp; unfold NI TI; ring

theorem UI_hasDerivAt (p : ℝ) : HasDerivAt UI dUI p := by
  have h := ((hasDerivAt_id p).mul_const (1+6*rationalLine.g0-4*rationalLine.g1)).const_sub 1
  convert h using 1
  · funext z; simp only [UI,id]
  · unfold dUI; ring

theorem JI_hasDerivAt (δ p : ℝ) : HasDerivAt (JI δ) (dJI δ) p := by
  have h := ((((hasDerivAt_id p).mul_const (1+2*rationalLine.g1)).const_sub 1).const_mul (2*δ)).const_add
    (3*(5/6-δ))
  convert h using 1
  · funext z; simp only [JI,kI,id]
  · unfold dJI; ring

theorem valueI_ratio {δ p : ℝ} (hj : JI δ p≠0) :
    valueI δ p=1-δ+(5/6-δ)*δ*(UI p/JI δ p) := by
  unfold valueI NI; field_simp; try ring

theorem valueI_hasDerivAt {δ p : ℝ} (hj : JI δ p≠0) :
    HasDerivAt (valueI δ) ((5/6-δ)*δ*(-(UI p*dJI δ-dUI*JI δ p))/(JI δ p)^2) p := by
  have hq := (UI_hasDerivAt p).div (JI_hasDerivAt δ p) hj
  have hn := (JI_hasDerivAt δ p).continuousAt.eventually_ne hj
  have he : valueI δ =ᶠ[nhds p] (fun z=>1-δ+(5/6-δ)*δ*(UI z/JI δ z)) :=
    hn.mono (fun z hz=>valueI_ratio hz)
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hasDerivAt_const p (1-δ)).add (hq.const_mul ((5/6-δ)*δ)) using 1 <;> (try funext z) <;> ring

theorem valueI_antitoneOn {δ : ℝ} (hδ : δ∈Icc (189/512:ℝ) (15/32)) :
    AntitoneOn (valueI δ) (Icc (15/32:ℝ) (1/2)) := by
  have hj (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) : 0<JI δ p := hJ hδ hp
  have hh (p : ℝ) (hp : p∈Icc (15/32:ℝ) (1/2)) := valueI_hasDerivAt (hj p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp; exact (hh p hp).continuousAt.continuousWithinAt
  · intro p hp; exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hh p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [hδ.2]) (by linarith [hδ.1]))
        (neg_nonpos.mpr (hanti hδ (interior_subset hp)).le)
    · exact sq_nonneg _

/-- **The improved window** `[189/512, 15/32] × [15/32, 1/2]` (line `(rationalLine.g0, rationalLine.g1)`, native
plain fallback on the count face `C`). -/
def window : ImprovedWindow rationalLine (naturalK/6) where
  B := countCB
  lam := countCL
  cap := countCap-1/10000000
  sourceCap := countCap
  mHi := naturalM
  lam_gt_one := by norm_num [countCL]
  mHi_lo := natural_join_bounds.1
  mHi_hi := natural_join_bounds.2
  cap_le_source := by linarith
  cap_small := by norm_num [countCap]
  value := valueI
  cutoff := cutoffI
  crossing := crossingI
  deltaLo := 189/512
  deltaHi := 15/32
  pLo := 15/32
  deltaBounds := by norm_num
  pBounds := by norm_num
  cutoff_bounds := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    exact ⟨(le_div_iff₀ hJ').mpr (by linarith [hT1 hd hp]),
      (div_le_iff₀ hJ').mpr (by linarith [hT2 hd hp])⟩
  crossing_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    unfold anchorLeft at this ⊢
    linarith
  plain_left := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    rw [crossing_eq δ p hJ'.ne']
    unfold crossingI
    rw [le_div_iff₀ (by linarith)]
    have := hcross hd hp
    linarith
  slope_nonneg := by intro δ p hd hp; exact (hk hd hp).le
  inverse_crossing := by intro δ p hd hp; exact inverse_identity δ p (hJ hd hp).ne'
  ordinary_crossing := by
    intro δ p hd hp
    rw [crossing_eq δ p (hJ hd hp).ne']
    have e := inverse_identity δ p (hJ hd hp).ne'
    apply le_of_eq
    rw [← e]; ring
  native_top := by
    intro δ p hd hp
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    linarith [hnat hd hp]
  plain_top := by
    intro δ p hd hp
    have hJ' := hJ hd hp
    unfold valueI plainCurve
    apply max_le
    · rw [le_div_iff₀ hJ']
      have h := hplain0 hd hp
      linarith
    · rw [le_div_iff₀ hJ']
      have h := hplain1 hd hp
      have e : (1-2*δ*(anchorTop/2)-2*δ*p*(countCB-2*(anchorTop/2))/countCL)*JI δ p=
          (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p := by ring
      rw [e]; exact h.le
  natural_tail := by
    intro δ p hd hp
    have he : (1-2*naturalM)/(6*(naturalK/6))=sMinus := by norm_num [naturalM,naturalK,sMinus]
    rw [mul_div_assoc,he]
    unfold valueI
    rw [le_div_iff₀ (hJ hd hp)]
    have := htail hd hp
    linarith
  widths := by
    intro ν hν m hm1 hm2
    have hM : naturalM=(1-naturalK*sMinus)/2 := rfl
    apply lt_min
    · unfold countCap; linarith
    · rw [hM] at hm2
      norm_num [naturalK,sMinus] at hm2
      rw [lt_div_iff₀ (by norm_num [countCL])]
      norm_num [countCB,countCL]
      linarith
  long_crossing := by intro δ p hd hp; exact long_identity δ p (hJ hd hp).ne'
  antitone := by intro δ hd; exact valueI_antitoneOn hd


end
end Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ContinuumQ
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ContinuumQ.guard_pos
