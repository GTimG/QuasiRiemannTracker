/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual E49 admission window. Original finite-window algebra adapted from Joseph
Bebel and Sil, retaining original Apache-2.0 notices and count contracts. -/
import Candidate.C092.transport.PacketJoinE49Scheme
import Candidate.C092.transport.DirectPairedAdmission
import Candidate.C092.transport.TangentExtensionSource
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.CountWidth
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.PacketJoinE49.Return
noncomputable section
open Set QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning QRH.ArviReturnTuning
open QRH.Record1252270103Return (plainCurve)
abbrev line := Qrh.TwoSlot.AnchorContinuum.Contact.exactLine

instance line_capacity : CapacityBounds line where
  bounds := by
    intro w hw hw'
    have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
    have hw0 : 0 ≤ w := by dsimp [anchorLeft] at hw;linarith
    have hm0 := mul_le_mul_of_nonneg_right hc.2.2.1.le hw0
    have hm1 := mul_le_mul_of_nonneg_right hc.2.2.2.le hw0
    unfold markCap
    have hc0 := hc.1
    have hc1 := hc.2.1
    change _ < line.g0 at hc0
    change line.g0 < _ at hc1
    change _ ≤ line.g1*w at hm0
    change line.g1*w ≤ _ at hm1
    norm_num [anchorLeft,anchorTop] at hw hw'
    constructor <;> nlinarith [hc0,hc1]

def kI (p : ℝ) : ℝ := 1-p*(1+2*line.g1)
def aI (p : ℝ) : ℝ := p*(1+2*line.g0)
def UI (p : ℝ) : ℝ := 1-p*(1+6*line.g0-4*line.g1)
def JI (δ p : ℝ) : ℝ := 3*(5/6-δ)+2*δ*kI p
def NI (δ p : ℝ) : ℝ := (1-δ)*JI δ p+(5/6-δ)*δ*UI p
def TI (δ p : ℝ) : ℝ := JI δ p+δ*UI p
def valueI (δ p : ℝ) : ℝ := NI δ p/JI δ p
def cutoffI (δ p : ℝ) : ℝ := TI δ p/JI δ p
def crossingI (δ p : ℝ) : ℝ := 2*TI δ p/(3*JI δ p)
def dUI : ℝ := -(1+6*line.g0-4*line.g1)
def dJI (δ : ℝ) : ℝ := -2*δ*(1+2*line.g1)


lemma guard_pos (j : Fin 10) {δ p : ℝ}
    (hδ : δ∈Icc (45/128:ℝ) (15/32)) (hp : p∈Icc (7/16:ℝ) (1/2)) :
    0 < Direct.pairedGuard j δ p line.g0 line.g1 := by
  have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  apply lt_of_lt_of_le (by norm_num : (0:ℝ)<1/1000)
  apply Direct.paired_admission_real (point := (δ,p)) ?_ hc.1.le hc.2.1.le hc.2.2.1.le hc.2.2.2.le
  simpa [Direct.pairedAdmissionBox,QRH.Coverage.Box.Contains] using And.intro hδ.1 (And.intro hδ.2 (And.intro hp.1 hp.2))

section
variable {δ p : ℝ} (hδ : δ∈Icc (45/128:ℝ) (15/32)) (hp : p∈Icc (7/16:ℝ) (1/2))
include hδ hp

theorem hk : 0<kI p := by
  have h := guard_pos 0 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hJ : 0<JI δ p := by
  have h := guard_pos 1 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hT1 : JI δ p<TI δ p := by
  have h := guard_pos 2 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hT2 : TI δ p<12499/10000*JI δ p := by
  have h := guard_pos 3 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hcross : (anchorLeft+1/1000000)*(3*JI δ p)<2*TI δ p := by
  have h := guard_pos 4 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hnat : (1-δ*(p+(1-p)*anchorTop))*JI δ p<NI δ p := by
  have h := guard_pos 5 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hplain1 : (1-δ*(anchorTop+2*(countCB-anchorTop)/countCL*p))*JI δ p<NI δ p := by
  have h := guard_pos 6 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hplain0 : (1-δ*(anchorTop+2*(countCap-1/10000000)*p))*JI δ p<NI δ p := by
  have h := guard_pos 7 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem htail : (1-2*δ*naturalM-2*δ*p*sMinus)*JI δ p<NI δ p := by
  have h := guard_pos 8 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

theorem hanti : 0<UI p*dJI δ-dUI*JI δ p := by
  have h := guard_pos 9 hδ hp
  norm_num [Direct.pairedGuard,kI,JI,UI,NI,TI,dJI,dUI,anchorLeft,anchorTop,
    countCB,countCL,countCap,naturalM,naturalK,sMinus] at h ⊢
  linarith

end
theorem crossing_eq (δ p : ℝ) (hJ : JI δ p≠0) :
    2*(cutoffI δ p-crossingI δ p)=crossingI δ p := by
  unfold cutoffI crossingI; field_simp; ring

theorem inverse_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ*(p*(1+2*line.g0)+(1-p*(1+2*line.g1))*crossingI δ p)=valueI δ p := by
  unfold crossingI valueI; field_simp; unfold NI TI JI UI kI; ring

theorem long_identity (δ p : ℝ) (hJ : JI δ p≠0) :
    1-δ+(5/6-δ)*(cutoffI δ p-1)=valueI δ p := by
  unfold cutoffI valueI; field_simp; unfold NI TI; ring

theorem UI_hasDerivAt (p : ℝ) : HasDerivAt UI dUI p := by
  have h := ((hasDerivAt_id p).mul_const (1+6*line.g0-4*line.g1)).const_sub 1
  convert h using 1
  · funext z; simp only [UI,id]
  · unfold dUI; ring

theorem JI_hasDerivAt (δ p : ℝ) : HasDerivAt (JI δ) (dJI δ) p := by
  have h := ((((hasDerivAt_id p).mul_const (1+2*line.g1)).const_sub 1).const_mul (2*δ)).const_add
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

theorem valueI_antitoneOn {δ : ℝ} (hδ : δ∈Icc (45/128:ℝ) (15/32)) :
    AntitoneOn (valueI δ) (Icc (7/16:ℝ) (1/2)) := by
  have hj (p : ℝ) (hp : p∈Icc (7/16:ℝ) (1/2)) : 0<JI δ p := hJ hδ hp
  have hh (p : ℝ) (hp : p∈Icc (7/16:ℝ) (1/2)) := valueI_hasDerivAt (hj p hp).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro p hp; exact (hh p hp).continuousAt.continuousWithinAt
  · intro p hp; exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [(hh p (interior_subset hp)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [hδ.2]) (by linarith [hδ.1]))
        (neg_nonpos.mpr (hanti hδ (interior_subset hp)).le)
    · exact sq_nonneg _

/-- **The improved window** `[189/512, 15/32] × [15/32, 1/2]` (line `(line.g0, line.g1)`, native
plain fallback on the count face `C`). -/
def window : ImprovedWindow line (naturalK/6) where
  B := countCB
  lam := countCL
  cap := countCap-1/10000000
  sourceCap := countCap-1/10000000
  mHi := naturalM
  lam_gt_one := by norm_num [countCL]
  mHi_lo := natural_join_bounds.1
  mHi_hi := natural_join_bounds.2
  cap_le_source := by linarith
  cap_small := by norm_num [countCap]
  value := valueI
  cutoff := cutoffI
  crossing := crossingI
  deltaLo := 45/128
  deltaHi := 15/32
  pLo := 7/16
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
end QRH.Cycle092.PacketJoinE49.Return
#print axioms QRH.Cycle092.PacketJoinE49.Return.window
