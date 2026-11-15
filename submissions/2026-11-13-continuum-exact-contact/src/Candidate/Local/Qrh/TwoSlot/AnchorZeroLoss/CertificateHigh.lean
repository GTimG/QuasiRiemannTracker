/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Continuous HIGH-stage coverage from the authoritative exact rational checks. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.CertificateStage
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Algebra

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData

def highData (s : Stage) (r : ℝ) : High.Stg :=
  ⟨s.R,s.gain,s.cut,s.a0,s.a1,r/s.R⟩

def stageCut (s : Stage) (r ν : ℝ) : ℝ :=
  fg (s.R:ℝ) s.gain s.cut s.a0 s.a1 r ν/fH (s.R:ℝ) r+1/1000000000000

private theorem pos_cast {q : ℚ} {x : ℝ} (h : 0<q) (hx : (q:ℝ)=x) : 0<x := by
  rw [←hx]; exact_mod_cast h

theorem highData_r (s : Stage) (r : ℝ) (hR : (s.R:ℝ)≠0) : (highData s r).r=r := by
  simp only [High.Stg.r,highData]; field_simp

theorem highData_s (s : Stage) (r : ℝ) (hR : (s.R:ℝ)≠0) (hk : (s.cut:ℝ)≠0) :
    (highData s r).s=fs (s.R:ℝ) s.gain s.cut r := by
  simp only [High.Stg.s,High.Stg.u,highData,fs,fS,fY,fu]
  field_simp
  ring

theorem highData_g (s : Stage) (r ν : ℝ) (hR : (s.R:ℝ)≠0) (hk : (s.cut:ℝ)≠0) :
    (highData s r).g ν=fg (s.R:ℝ) s.gain s.cut s.a0 s.a1 r ν := by
  simp only [High.Stg.g,High.Stg.D]
  rw [highData_r s r hR,highData_s s r hR hk]
  rfl

theorem highData_w (s : Stage) (r ν : ℝ) (hR : (s.R:ℝ)≠0) (hk : (s.cut:ℝ)≠0) :
    (highData s r).w ν=stageCut s r ν := by
  unfold High.Stg.w
  rw [highData_g s r ν hR hk]
  rfl

theorem high_endpoint (s : Stage) (r : ℚ) (h : ∀v∈s.gates r,0<v) :
    0<fH (s.R:ℝ) r*fF0 (s.R:ℝ) s.gain s.cut s.a0 s.a1-(highReserve:ℝ) ∧
    0<(r:ℝ)/2-fs (s.R:ℝ) s.gain s.cut r-
      (3/2)*(5/6-(s.cut:ℝ))*(fu (s.R:ℝ) r/((s.cut:ℝ)*s.cut))/(1/2-(s.a1:ℝ))-1/10 ∧
    0<fH (s.R:ℝ) r+fu (s.R:ℝ) r-fH (s.R:ℝ) r/6-1/15-
      (3/4)*(r:ℝ)-fs (s.R:ℝ) s.gain s.cut r-3/100 ∧
    0<stageCut s r s.cut-2/3 ∧ 0<79/100-stageCut s r (3/4) := by
  have h1 := h (fH s.R r*fF0 s.R s.gain s.cut s.a0 s.a1-highReserve) (by simp [Stage.gates])
  have h9 := h (r/2-fs s.R s.gain s.cut r-(3/2)*(5/6-s.cut)*
    (fu s.R r/(s.cut*s.cut))/(1/2-s.a1)-1/10) (by simp [Stage.gates])
  have h10 := h (fH s.R r+fu s.R r-fH s.R r/6-1/15-(3/4)*r-fs s.R s.gain s.cut r-3/100)
    (by simp [Stage.gates])
  have h11 := h (s.w r s.cut-2/3) (by simp [Stage.gates])
  have h12 := h (79/100-s.w r (3/4)) (by simp [Stage.gates])
  refine ⟨pos_cast h1 ?_,pos_cast h9 ?_,pos_cast h10 ?_,pos_cast h11 ?_,pos_cast h12 ?_⟩ <;>
    (simp only [stageCut,Stage.w,witnessPad,fg,fH,fs,fS,fY,fu,fF0,fwb]; push_cast; norm_num)

/-- Fractional-affine cutoffs retain either strict endpoint inequality across
an interval of positive relative radii. -/
theorem cutoff_between (s : Stage) {a b r ν c sign : ℝ}
    (hR : 0<(s.R:ℝ)) (ha : 0<a) (hab : a<b) (hlo : a≤r) (hhi : r≤b)
    (hca : 0<sign*(c-stageCut s a ν)) (hcb : 0<sign*(c-stageCut s b ν)) :
    0<sign*(c-stageCut s r ν) := by
  have hiff (x : ℝ) (hx : 0<x) :
      0<sign*(c-stageCut s x ν) ↔
        0<sign*(fH (s.R:ℝ) x*(c-1/1000000000000)-fg (s.R:ℝ) s.gain s.cut s.a0 s.a1 x ν) := by
    have hH : 0<fH (s.R:ℝ) x := div_pos hx hR
    have heq : fH (s.R:ℝ) x*(sign*(c-stageCut s x ν)) =
        sign*(fH (s.R:ℝ) x*(c-1/1000000000000)-fg (s.R:ℝ) s.gain s.cut s.a0 s.a1 x ν) := by
      unfold stageCut
      field_simp [hH.ne']
      ring
    rw [←heq]
    exact (mul_pos_iff_of_pos_left hH).symm
  apply (hiff r (ha.trans_le hlo)).mpr
  exact Qrh.MarkedAnchor.Price.pos_affine
    (f:=fun x=>sign*(fH (s.R:ℝ) x*(c-1/1000000000000)-fg (s.R:ℝ) s.gain s.cut s.a0 s.a1 x ν))
    (fun x=>by simp only [fg,fH,fs,fS,fY,fu]; ring) hab hlo hhi
    ((hiff a ha).mp hca) ((hiff b (ha.trans hab)).mp hcb)

/-- The exact HIGH hypotheses hold at every real width of a checked stage. -/
theorem high_hyp (s : Stage) (hok : s.ok=true) (r : ℝ)
    (hlo : (s.left:ℝ)≤r) (hhi : r≤s.R) : (highData s r).Hyp := by
  have hS := ordinary_hyp s hok r hlo hhi
  obtain ⟨hb,hL,hR⟩ := Stage.ok_sound hok
  obtain ⟨g1L,g9L,g10L,g11L,g12L⟩ := high_endpoint s s.left hL
  obtain ⟨g1R,g9R,g10R,g11R,g12R⟩ := high_endpoint s s.R hR
  have hbasic := hb
  rcases hb with ⟨hR0,hR1,hleft,hlt,hk0,hk1,hz,ha1,ha1hi,huL,hwble,hline,hlgain,hrest⟩
  have hRp : 0<(s.R:ℝ) := hS.R_pos
  have hkp : 0<(s.cut:ℝ) := hS.k_pos
  have hleftp : 0<(s.left:ℝ) := by
    have h : (((1467/2000:ℚ):ℝ)≤(s.left:ℝ)) := Rat.cast_le.mpr hleft
    norm_num at h; linarith
  have hltr : (s.left:ℝ)<s.R := by exact_mod_cast hlt
  have hrp : 0<r := hleftp.trans_le hlo
  have hapos : 0≤(s.a1:ℝ) := Rat.cast_nonneg.mpr ha1
  have hahi : (s.a1:ℝ)≤2/5 := by
    have h : (s.a1:ℝ)<((2/5:ℚ):ℝ) := Rat.cast_lt.mpr ha1hi
    norm_num at h; linarith
  have hlinegain : (s.a0:ℝ)-(s.a1:ℝ)*s.R≤s.gain := by
    have h : ((s.line s.R:ℚ):ℝ)≤(s.gain:ℝ) := Rat.cast_le.mpr hlgain
    simpa only [Stage.line,fline,Rat.cast_sub,Rat.cast_mul] using h
  have hHpos : 0<(highData s r).H := div_pos hrp hRp
  have es := highData_s s r hRp.ne' hkp.ne'
  have er := highData_r s r hRp.ne'
  have eu : (highData s r).u=fu (s.R:ℝ) r := rfl
  have eH : (highData s r).H=fH (s.R:ℝ) r := rfl
  refine ⟨hRp,hHpos,?_,by change (1/6:ℝ)≤s.cut; linarith [hS.hk.1],
    by change (s.cut:ℝ)≤3/4; linarith [hS.hk.2],hapos,hahi,hlinegain,?_,?_,?_,?_,?_,?_⟩
  · rw [eH]; exact hS.H_le_one
  · change 0≤(1-(s.R:ℝ))/2+s.gain
    linarith [hS.hR.2,hS.hz]
  · have hg := Qrh.MarkedAnchor.Price.pos_affine
      (f:=fun x=>fH (s.R:ℝ) x*fF0 (s.R:ℝ) s.gain s.cut s.a0 s.a1-(highReserve:ℝ))
      (fun x=>by simp only [fH]; ring) hltr hlo hhi g1L g1R
    change (3/100000000000:ℝ)<fH (s.R:ℝ) r*fF0 (s.R:ℝ) s.gain s.cut s.a0 s.a1
    norm_num [highReserve] at hg
    linarith
  · have hg := Qrh.MarkedAnchor.Price.pos_affine
      (f:=fun x=>x/2-fs (s.R:ℝ) s.gain s.cut x-(3/2)*(5/6-(s.cut:ℝ))*
        (fu (s.R:ℝ) x/((s.cut:ℝ)*s.cut))/(1/2-(s.a1:ℝ))-1/10)
      (fun x=>by simp only [fs,fS,fY,fu]; ring) hltr hlo hhi g9L g9R
    unfold High.Stg.gate9 High.Stg.D
    rw [er,es,eu]
    change 0≤r/2-fs (s.R:ℝ) s.gain s.cut r-(3/2)*(5/6-(s.cut:ℝ))*
      (fu (s.R:ℝ) r/((s.cut:ℝ)*s.cut))/(1/2-(s.a1:ℝ))
    linarith
  · have hg := Qrh.MarkedAnchor.Price.pos_affine
      (f:=fun x=>fH (s.R:ℝ) x+fu (s.R:ℝ) x-fH (s.R:ℝ) x/6-1/15-(3/4)*x-
        fs (s.R:ℝ) s.gain s.cut x-3/100)
      (fun x=>by simp only [fH,fs,fS,fY,fu]; ring) hltr hlo hhi g10L g10R
    rw [er,es,eu,eH]
    linarith
  · have hg := cutoff_between s hRp hleftp hltr hlo hhi
      (ν:=(s.cut:ℝ)) (c:=2/3) (sign:=-1) (by linarith) (by linarith)
    change High.cutLo≤(highData s r).w (s.cut:ℝ)
    rw [highData_w s r s.cut hRp.ne' hkp.ne']
    unfold High.cutLo
    linarith
  · have hg := cutoff_between s hRp hleftp hltr hlo hhi
      (ν:=3/4) (c:=79/100) (sign:=1) (by linarith) (by linarith)
    rw [highData_w s r (3/4) hRp.ne' hkp.ne']
    unfold High.cutHi
    linarith

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.high_hyp
