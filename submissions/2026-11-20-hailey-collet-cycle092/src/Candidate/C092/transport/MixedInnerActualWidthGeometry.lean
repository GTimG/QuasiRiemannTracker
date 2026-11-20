/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Closed pointwise crossing enclosure, with the original directed contacts.
This encloses t0/3 and never identifies it with the actual ordinary length. -/
import Candidate.C092.transport.MixedInnerActualWidthCore
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.MixedInnerActualWidth
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.Cycle092.ActualMixedPrice QRH.Cycle092.RawTicket

 theorem crossing_contact_order {d p a0 a1 b0 b1 : ℝ}
    (hd : 0≤ d) (hd' : d≤1/2) (hp : 0≤ p) (hp' : p≤1/2)
    (ha0 : 0≤ a0) (ha0' : a0≤3/50) (hb0 : 0≤ b0) (hb0' : b0≤3/50)
    (ha1 : 7/100≤ a1) (ha1' : a1≤2/25) (hb1 : 7/100≤ b1) (hb1' : b1≤2/25)
    (h0 : b0≤ a0) (h1 : a1≤ b1) :
    pairedCrossing d p a0 a1≤ pairedCrossing d p b0 b1 := by
  have ha:=QRH.Cycle092.Physical.admitted hd hd' hp hp' ha0 ha0' ha1 ha1'
  have hb:=QRH.Cycle092.Physical.admitted hd hd' hp hp' hb0 hb0' ha1 ha1'
  have hc:=QRH.Cycle092.Physical.admitted hd hd' hp hp' hb0 hb0' hb1 hb1'
  have hcount:=(pairedCount_antitone_g₀ hd (by linarith) hp h0 ha.2.1).trans
    (pairedCount_monotone_g₁ hd (by linarith) hp h1 hb.1 hb.2.1 hc.2.1)
  rw [pairedCount_eq ha.2.1.ne',pairedCount_eq hc.2.1.ne'] at hcount
  have hv : 0< pairedV d:=by dsimp [pairedV];linarith
  nlinarith only [hcount,hv]

 theorem crossing_rectangle {a b f e d p g0 g1 : ℝ}
    (ha : 0≤ a) (hab : a≤ b) (hb : b≤1/2)
    (hf : 0≤ f) (hfe : f≤ e) (he : e≤1/2)
    (hd : a≤ d ∧ d≤ b) (hp : f≤ p ∧ p≤ e)
    (hg0 : 0≤ g0 ∧ g0≤3/50) (hg1 : 7/100≤ g1 ∧ g1≤2/25)
    (hC0 : 1≤1+6*g0-4*g1) :
    pairedCrossing a e g0 g1≤ pairedCrossing d p g0 g1 ∧
    pairedCrossing d p g0 g1≤ pairedCrossing b f g0 g1 := by
  have hd0 : 0≤ d:=ha.trans hd.1
  have hd1 : d≤1/2:=hd.2.trans hb
  have hp0 : 0≤ p:=hf.trans hp.1
  have hp1 : p≤1/2:=hp.2.trans he
  have hadm (x y : ℝ) (hx : 0≤ x) (hx' : x≤1/2) (hy : 0≤ y) (hy' : y≤1/2):=
    QRH.Cycle092.Physical.admitted hx hx' hy hy' hg0.1 hg0.2 hg1.1 hg1.2
  have hC (x : ℝ) (hx : 0≤ x) (hx' : x≤1/2) :
      0≤(5/2-x)*(1+6*g0-4*g1)-2*x*(1+2*g1):=by
    have hA:=mul_nonneg (sub_nonneg.mpr hC0) (show 0≤5/2-x by linarith only [hx'])
    have hB:=mul_le_mul_of_nonneg_right (show 2*x≤1 by linarith only [hx'])
      (show 0≤1+2*g1 by linarith only [hg1.1])
    nlinarith only [hA,hB,hg1.2,hx']
  constructor
  · have h0:=crossing_antitone_p hp.2 ha (hC a ha (hab.trans hb))
      (hadm a p ha (hab.trans hb) hp0 hp1).2.1
      (hadm a e ha (hab.trans hb) (hf.trans hfe) he).2.1
    have h1:=crossing_monotone_d hd.1 (hadm a p ha (hab.trans hb) hp0 hp1).1
      (hadm a p ha (hab.trans hb) hp0 hp1).2.1 (hadm d p hd0 hd1 hp0 hp1).2.1
    exact h0.trans h1
  · have h0:=crossing_monotone_d hd.2 (hadm d p hd0 hd1 hp0 hp1).1
      (hadm d p hd0 hd1 hp0 hp1).2.1 (hadm b p (ha.trans hab) hb hp0 hp1).2.1
    have h1:=crossing_antitone_p hp.1 (ha.trans hab) (hC b (ha.trans hab) hb)
      (hadm b f (ha.trans hab) hb hf (hfe.trans he)).2.1
      (hadm b p (ha.trans hab) hb hp0 hp1).2.1
    exact h0.trans h1

 theorem actual_crossing_interval {r : Row} (hr : r∈rows) {d p g0 g1 : ℝ}
    (hp : r.box.Contains (d,p))
    (hg0 : 5805911/100000000≤ g0 ∧ g0≤5805913/100000000)
    (hg1 : 3799809/50000000≤ g1 ∧ g1≤379981/5000000) :
    (lowerM r.box:ℝ)≤ pairedCrossing d p g0 g1/3 ∧
    pairedCrossing d p g0 g1/3≤(upperM r.box:ℝ) := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have hs:=QRH.Cycle092.Top.shape_of_check (List.all_eq_true.mp QRH.Cycle092.Top.all_rows_checked r hr)
  have hab : (r.box.uLo:ℝ)≤(r.box.uHi:ℝ):=by exact_mod_cast hs.2.2.1.le
  have hfe : (r.box.vLo:ℝ)≤(r.box.vHi:ℝ):=by exact_mod_cast hs.2.2.2.2.2.1.le
  have ha0 : 0≤(r.box.uLo:ℝ):=by norm_num [dLo] at ha;linarith only [ha.1]
  have hb1 : (r.box.uHi:ℝ)≤1/2:=by norm_num [dHi] at hb;linarith only [hb.2]
  have hf0 : 0≤(r.box.vLo:ℝ):=by norm_num [pLo] at hf;linarith only [hf.1]
  have he1 : (r.box.vHi:ℝ)≤1/2:=by norm_num [pHi] at he;exact he.2
  have hd0:=ha0.trans hp.1
  have hd1:=hp.2.1.trans hb1
  have hp0:=hf0.trans hp.2.2.1
  have hp1:=hp.2.2.2.trans he1
  have hlo:=crossing_rectangle ha0 hab hb1 hf0 hfe he1 ⟨hp.1,hp.2.1⟩ ⟨hp.2.2.1,hp.2.2.2⟩
    (show (0:ℝ)≤5805913/100000000 ∧ (5805913/100000000:ℝ)≤3/50 by norm_num)
    (show (7/100:ℝ)≤3799809/50000000 ∧ (3799809/50000000:ℝ)≤2/25 by norm_num) (by norm_num)
  have hhi:=crossing_rectangle ha0 hab hb1 hf0 hfe he1 ⟨hp.1,hp.2.1⟩ ⟨hp.2.2.1,hp.2.2.2⟩
    (show (0:ℝ)≤5805911/100000000 ∧ (5805911/100000000:ℝ)≤3/50 by norm_num)
    (show (7/100:ℝ)≤379981/5000000 ∧ (379981/5000000:ℝ)≤2/25 by norm_num) (by norm_num)
  have hc0:=crossing_contact_order hd0 hd1 hp0 hp1
    (show (0:ℝ)≤5805913/100000000 by norm_num) (by norm_num)
    (by linarith only [hg0.1] : 0≤ g0) (by linarith only [hg0.2] : g0≤3/50)
    (by norm_num) (by norm_num) (by linarith only [hg1.1]) (by linarith only [hg1.2]) hg0.2 hg1.1
  have hc1:=crossing_contact_order hd0 hd1 hp0 hp1
    (by linarith only [hg0.1] : 0≤ g0) (by linarith only [hg0.2] : g0≤3/50)
    (show (0:ℝ)≤5805911/100000000 by norm_num) (by norm_num)
    (by linarith only [hg1.1]) (by linarith only [hg1.2]) (by norm_num) (by norm_num) hg0.1 hg1.2
  have helo : (lowerM r.box:ℝ)=pairedCrossing (r.box.uLo:ℝ) r.box.vHi (5805913/100000000) (3799809/50000000)/3:=by
    unfold lowerM pairedCrossing pairedU pairedJ pairedV pairedK
    push_cast
    congr 2 <;> ring
  have hehi : (upperM r.box:ℝ)=pairedCrossing (r.box.uHi:ℝ) r.box.vLo (5805911/100000000) (379981/5000000)/3:=by
    unfold upperM pairedCrossing pairedU pairedJ pairedV pairedK
    push_cast
    congr 2 <;> ring
  rw [helo,hehi]
  constructor <;> linarith only [hlo.1,hhi.2,hc0,hc1]
end
end QRH.Cycle092.MixedInnerActualWidth
#print axioms QRH.Cycle092.MixedInnerActualWidth.actual_crossing_interval
