/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine fixed interior detector. Its short and long alternatives remain
separate throughout the authentic same-supported-witness count. -/
import Candidate.C092.transport.PacketJoinFixedScheme
import Candidate.C092.transport.PacketJoinE49Window
import Candidate.C092.transport.DirectFixed
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.Cycle092.PacketJoinFixed.Return
noncomputable section
open QRH.Cycle092.PacketJoinE49
open Set QRH.PositiveGap.Return QRH.PositiveGap.ReturnTuning QRH.ArviReturnTuning
open QRH.Record1252270103Return (plainCurve)
abbrev line := Qrh.TwoSlot.AnchorContinuum.Contact.exactLine
def fixedR : ℝ := 360001/500000
def cutoff : ℝ := 3*fixedR/2
def bracket (p : ℝ) : ℝ := p*(1+2*line.g0)+(1-p*(1+2*line.g1))*fixedR
def short (δ p : ℝ) : ℝ := 1-δ*bracket p
def long (δ : ℝ) : ℝ := 1/6+(5/6-δ)*cutoff
def value (δ p : ℝ) : ℝ := max (short δ p) (long δ)

lemma continuations {p : ℝ} (hp : 0≤p) (hp' : p≤1/2) :
    bracket p≤anchorTop+(1-anchorTop)*p ∧
    bracket p≤anchorTop+2*p*(countCap-1/10000000) ∧
    bracket p≤anchorTop+2*p*(countCB-anchorTop)/countCL ∧
    bracket p≤2*naturalM+2*p*sMinus ∧ bracket p<9/10 := by
  have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have hm0 := mul_le_mul_of_nonneg_left hc.2.1.le hp
  have hm1 := mul_le_mul_of_nonneg_left hc.2.2.1.le hp
  have hb : bracket p≤fixedR+(287/1000)*p := by
    unfold bracket fixedR
    change p*line.g0≤p*(5805913/100000000) at hm0
    change p*(3799809/50000000)≤p*line.g1 at hm1
    nlinarith
  norm_num [anchorTop,countCB,countCL,countCap,naturalM,naturalK,sMinus,fixedR] at hb ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Constant early cutoff, not an optimized paired crossing. -/
def window : FixedWindow line (naturalK/6) where
  B := countCB
  lam := countCL
  cap := countCap-1/10000000
  sourceCap := countCap-1/10000000
  mHi := naturalM
  lam_gt_one := by norm_num [countCL]
  mHi_lo := natural_join_bounds.1
  mHi_hi := natural_join_bounds.2
  cap_le_source := le_rfl
  cap_small := by norm_num [countCap]
  value := short
  cutoff := fun _ _=>cutoff
  crossing := fun _ _=>fixedR
  deltaLo := 0
  deltaHi := 3/4
  pLo := 0
  deltaBounds := by norm_num
  pBounds := by norm_num
  cutoff_bounds := by intro δ p hd hp;norm_num [cutoff,fixedR]
  crossing_left := by intro δ p hd hp;norm_num [anchorLeft,fixedR]
  plain_left := by intro δ p hd hp;norm_num [anchorLeft,fixedR,cutoff]
  slope_nonneg := by
    intro δ p hd hp
    have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
    have h1 := mul_le_mul_of_nonneg_left hc.2.2.2.le hp.1
    change p*line.g1≤p*(379981/5000000) at h1
    nlinarith [hp.1,hp.2]
  inverse_crossing := by intro δ p hd hp;unfold short bracket;ring
  ordinary_crossing := by intro δ p hd hp;unfold short bracket cutoff;ring_nf;exact le_rfl
  native_top := by
    intro δ p hd hp
    have h := (continuations hp.1 hp.2).1
    have hm := mul_le_mul_of_nonneg_left h hd.1
    unfold short
    nlinarith
  plain_top := by
    intro δ p hd hp
    have h := continuations hp.1 hp.2
    have h0 := mul_le_mul_of_nonneg_left h.2.1 hd.1
    have h1 := mul_le_mul_of_nonneg_left h.2.2.1 hd.1
    unfold plainCurve short
    apply max_le <;> norm_num [countCL] at h0 h1 ⊢ <;> nlinarith
  natural_tail := by
    intro δ p hd hp
    have he : (1-2*naturalM)/(6*(naturalK/6))=sMinus := by norm_num [naturalM,naturalK,sMinus]
    rw [mul_div_assoc,he]
    have h := (continuations hp.1 hp.2).2.2.2.1
    have hm := mul_le_mul_of_nonneg_left h hd.1
    unfold short
    nlinarith
  widths := by
    intro ν hν m hm1 hm2
    have hM : naturalM=(1-naturalK*sMinus)/2 := rfl
    apply lt_min
    · unfold countCap;linarith
    · rw [hM] at hm2
      norm_num [naturalK,sMinus] at hm2
      rw [lt_div_iff₀ (by norm_num [countCL])]
      norm_num [countCB,countCL]
      linarith

lemma window_available {δ p : ℝ} (hd : 0≤δ) (hd' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) : window.Available δ p := ⟨⟨hd,hd'⟩,hp,hp'⟩
lemma cutoff_range : 1≤cutoff ∧ cutoff≤3/2 := by norm_num [cutoff,fixedR]
lemma value_eq (δ p : ℝ) :
    value δ p=max (window.value δ p) (1-δ+(5/6-δ)*(window.cutoff δ p-1)) := by
  change max (short δ p) (long δ)=max (short δ p) (1-δ+(5/6-δ)*(cutoff-1))
  congr 1
  unfold long
  ring

def pricedValue (δ p : ℝ) : ℝ :=
  max (Direct.countN .fixedS Cycle090.sourceCost Direct.kap δ p)
    (Direct.countN .fixedA Cycle090.sourceCost Direct.kap δ p)
lemma value_le_priced {δ p : ℝ} (hd : 0≤δ) (hp : 0≤p) : value δ p≤pricedValue δ p := by
  have hc := Qrh.TwoSlot.AnchorContinuum.Contact.tangent_coefficient_bounds
  have hm0 := mul_le_mul_of_nonneg_left hc.1.le hp
  have hm1 := mul_le_mul_of_nonneg_left hc.2.2.2.le hp
  have hb : Direct.fixedBracket p≤bracket p := by
    unfold Direct.fixedBracket bracket fixedR
    change p*(5805911/100000000)≤p*line.g0 at hm0
    change p*line.g1≤p*(379981/5000000) at hm1
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb hd
  unfold value pricedValue
  apply max_le_max
  · norm_num [Direct.countN,short,Direct.fixedBracket] at *
    linarith
  · norm_num [Direct.countN,long,cutoff,fixedR]
end
end QRH.Cycle092.PacketJoinFixed.Return
#print axioms QRH.Cycle092.PacketJoinFixed.Return.window
