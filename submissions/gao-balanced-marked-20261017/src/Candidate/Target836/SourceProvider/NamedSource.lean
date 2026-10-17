import Candidate.Target836.SourceProvider.HighPayment
import Candidate.Target836.SourceProvider.AcceptedIncumbent

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Target874836.SourceProvider.Named
noncomputable section
open OAI OAI.SevenEighths

def q : ℝ := 839/1250
def lam : ℝ := 19793/5000
def B : ℝ := 987047/1000000
def kappa : ℝ := incumbentKappa
def lowReserve : ℝ := 1/4000000
def highReserve : ℝ := 1/1000000
def loss : ℝ := 1/20000
def mesh : ℝ := 1/100000
def discard : ℝ := 1/1000
def omega : ℝ := 1/1000
def tau : ℝ := 13/400
def core : ℝ := 122/125
def K : ℝ := q/(6*(kappa-q))
def extra : ℝ := lowReserve/(1-q/kappa)
def gap (b : ℝ) : ℝ := B-1+(6*kappa-lam)*b
def amp (b : ℝ) : ℝ := K*gap b+extra
def total (b : ℝ) : ℝ := B-(lam-1)*(b-mesh)
def supplied (b : ℝ) : ℝ := b-mesh-discard
def frequency (b : ℝ) : ℝ := core*(1-6*amp b-omega)
def rho (delta : ℝ) : ℝ := LocalMoment.unmarkedDensity delta
def gamma (delta : ℝ) : ℝ := commonRate (rho delta) delta
def rate (delta : ℝ) : ℝ := (32/39)*delta*(5-6*delta)/(5-2*delta)
def tail (delta : ℝ) : ℝ := (6*rho delta-1)/250
def high (b delta : ℝ) : ℝ := 1-rho delta-delta*total b-amp b*(5-6*rho delta)

theorem low_exact (b : ℝ) :
    amp b-q/(6*kappa)*(gap b+6*amp b) = lowReserve := by
  norm_num [amp, K, extra, lowReserve, q, kappa, incumbentKappa]
  <;> ring

theorem basic_bounds (b : ℝ) (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    0 ≤ amp b ∧ amp b ≤ 1/75 ∧ 0 ≤ supplied b ∧ supplied b ≤ 1/25 ∧
    0 ≤ frequency b ∧ frequency b ≤ 1 ∧ total b+9*amp b ≤ 1 := by
  norm_num [amp, K, extra, lowReserve, q, kappa, incumbentKappa, gap, B, lam,
    supplied, mesh, discard, frequency, core, omega, total] at *
  rcases hb with ⟨hb0,hb1⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem channel_at_q (b : ℝ) (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) :
    highReserve ≤ high b q+gamma q*supplied b-loss ∧
    highReserve ≤ high b q+rate q*supplied b-loss ∧
    highReserve ≤ high b q+rate q*tau*frequency b-loss ∧
    highReserve ≤ high b q+tail q*frequency b-loss := by
  norm_num [highReserve, high, rho, LocalMoment.unmarkedDensity, gamma, commonRate,
    rate, tail, supplied, mesh, discard, loss, frequency, core, omega,
    amp, K, extra, lowReserve, q, kappa, incumbentKappa, gap, B, lam, total, tau] at *
  rcases hb with ⟨hb0,hb1⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rho_difference (lo delta : ℝ) (hlo : 0 < 5-2*lo) (hd : 0 < 5-2*delta) :
    rho lo-rho delta = 50*(delta-lo)/(3*(5-2*lo)*(5-2*delta)) := by
  unfold rho LocalMoment.unmarkedDensity
  field_simp [show 5-lo*2 ≠ 0 by linarith, show 5-delta*2 ≠ 0 by linarith]
  <;> ring

theorem rho_antitone {lo delta : ℝ} (hle : lo ≤ delta) (hd : delta ≤ 3/4) :
    rho delta ≤ rho lo := by
  have hlo : 0 < 5-2*lo := by linarith
  have hdp : 0 < 5-2*delta := by linarith
  have hh := rho_difference lo delta hlo hdp
  have hn : 0 ≤ 50*(delta-lo)/(3*(5-2*lo)*(5-2*delta)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

theorem rho_bounds {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    1/4 ≤ rho delta ∧ rho delta ≤ 2/5 := by
  have hu := rho_antitone hd.1 (show delta ≤ 3/4 by linarith [hd.2])
  have hl := rho_antitone hd.2 (by norm_num : (7/10 : ℝ) ≤ 3/4)
  norm_num [rho, LocalMoment.unmarkedDensity, q] at hu hl ⊢
  constructor <;> linarith

theorem rho_bounds_full {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 3/4) :
    1/4 ≤ rho delta ∧ rho delta ≤ 2/5 := by
  have hu := rho_antitone hd.1 hd.2
  have hl := rho_antitone hd.2 (le_refl (3/4 : ℝ))
  norm_num [rho, LocalMoment.unmarkedDensity, q] at hu hl ⊢
  constructor <;> linarith

theorem gamma_bounds_full {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 3/4) :
    0 ≤ gamma delta ∧ gamma delta ≤ delta := by
  have hr := rho_antitone hd.1 hd.2
  have hm : max (4*rho delta-1) ((2+22*rho delta)/21) ≤
      max (4*rho q-1) ((2+22*rho q)/21) :=
    max_le_max (by linarith) (by linarith)
  have hg : gamma q ≤ gamma delta := by unfold gamma commonRate; linarith [hd.1]
  have hq : 0 ≤ gamma q := by norm_num [gamma, commonRate, rho, LocalMoment.unmarkedDensity, q]
  have hz : 0 ≤ max (4*rho delta-1) ((2+22*rho delta)/21) :=
    le_trans (by linarith [(rho_bounds_full hd).1]) (le_max_left _ _)
  exact ⟨hq.trans hg, by unfold gamma commonRate; linarith⟩

theorem gamma_bounds {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    1/10 ≤ gamma delta ∧ gamma q ≤ gamma delta ∧ gamma delta ≤ delta := by
  have hr := rho_antitone hd.1 (show delta ≤ 3/4 by linarith [hd.2])
  have hm : max (4*rho delta-1) ((2+22*rho delta)/21) ≤
      max (4*rho q-1) ((2+22*rho q)/21) :=
    max_le_max (by linarith) (by linarith)
  have hg : gamma q ≤ gamma delta := by unfold gamma commonRate; linarith [hd.1]
  have hq : 1/10 ≤ gamma q := by norm_num [gamma, commonRate, rho, LocalMoment.unmarkedDensity, q]
  have hz : 0 ≤ max (4*rho delta-1) ((2+22*rho delta)/21) :=
    le_trans (by linarith [(rho_bounds hd).1]) (le_max_left _ _)
  exact ⟨hq.trans hg, hg, by unfold gamma commonRate; linarith⟩

theorem rate_bounds {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    0 ≤ rate delta ∧ rate delta ≤ 1 := by
  have hden : 0 < 5-2*delta := by linarith [hd.2]
  have hd0 : 0 ≤ delta := by norm_num [q] at hd; linarith [hd.1]
  have hlin : 0 ≤ 5-6*delta := by linarith [hd.2]
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd0) hlin) hden.le
  · unfold rate
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg delta]

theorem tail_bounds {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    0 ≤ tail delta ∧ tail delta ≤ 1/100 := by
  have hr := rho_bounds hd
  unfold tail
  constructor <;> linarith

/-- The main HIGH reserve grows faster than any marked/tail coefficient can
decrease on this compact range. This keeps the full delta interval. -/
theorem high_increase (b lo delta : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (hlo : 2/3 ≤ lo) (hle : lo ≤ delta) (hd : delta ≤ 3/4) :
    high b lo+(delta-lo)/5 ≤ high b delta := by
  obtain ⟨ha0, ha1, hs0, hs1, hf0, hf1, hA⟩ := basic_bounds b hb
  have hlop : 0 < 5-2*lo := by linarith
  have hdp : 0 < 5-2*delta := by linarith
  have hden : 0 < 3*(5-2*lo)*(5-2*delta) := by positivity
  have hprod : 3*(5-2*lo)*(5-2*delta) ≤ 121/3 := by
    have hh := mul_le_mul (show 5-2*lo ≤ 11/3 by linarith)
      (show 5-2*delta ≤ 11/3 by linarith) hdp.le (by norm_num : (0 : ℝ) ≤ 11/3)
    nlinarith
  have hnon : 0 ≤ 1-6*amp b := by linarith
  have hfrac : (6/5)*(1-6*amp b) ≤
      50*(1-6*amp b)/(3*(5-2*lo)*(5-2*delta)) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg hnon (sub_nonneg.mpr hprod)]
  have hbracket : 1/5 ≤ 50*(1-6*amp b)/(3*(5-2*lo)*(5-2*delta))-total b := by
    linarith
  have hid : high b delta-high b lo = (delta-lo)*
      (50*(1-6*amp b)/(3*(5-2*lo)*(5-2*delta))-total b) := by
    unfold high
    rw [show rho delta = rho lo-50*(delta-lo)/(3*(5-2*lo)*(5-2*delta)) by
      linarith [rho_difference lo delta hlop hdp]]
    ring
  have hh := mul_le_mul_of_nonneg_left hbracket (sub_nonneg.mpr hle)
  linarith

theorem high_upper (b delta : ℝ) (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (hd : 7/10 ≤ delta ∧ delta ≤ 3/4) : highReserve ≤ high b delta := by
  have hbase : highReserve ≤ high b (7/10) := by
    norm_num [highReserve, high, rho, LocalMoment.unmarkedDensity, total, B, lam, mesh,
      amp, K, extra, lowReserve, q, kappa, incumbentKappa, gap] at *
    rcases hb with ⟨hb0,hb1⟩
    linarith
  have hh := high_increase b (7/10) delta hb (by norm_num) hd.1 hd.2
  linarith [hd.1]

theorem rate_lipschitz {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    rate q-rate delta ≤ delta-q := by
  have hq : 0 < 5-2*q := by norm_num [q]
  have hdp : 0 < 5-2*delta := by linarith [hd.2]
  have hden : 0 < (5-2*q)*(5-2*delta) := by positivity
  have hnum : (32/39)*(30*delta+30*q-12*delta*q-25) ≤ (5-2*q)*(5-2*delta) := by
    norm_num [q] at *
    linarith [hd.2]
  have hratio : (32/39)*(30*delta+30*q-12*delta*q-25)/((5-2*q)*(5-2*delta)) ≤ 1 := by
    exact (div_le_iff₀ hden).mpr (by simpa using hnum)
  have hid : rate q-rate delta = (delta-q)*
      ((32/39)*(30*delta+30*q-12*delta*q-25)/((5-2*q)*(5-2*delta))) := by
    unfold rate
    field_simp [show 5-q*2 ≠ 0 by linarith, show 5-delta*2 ≠ 0 by linarith]
    <;> ring
  rw [hid]
  simpa using mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hd.1)

theorem tail_lipschitz {delta : ℝ} (hd : q ≤ delta ∧ delta ≤ 7/10) :
    tail q-tail delta ≤ (delta-q)/20 := by
  have hq : 0 < 5-2*q := by norm_num [q]
  have hdp : 0 < 5-2*delta := by linarith [hd.2]
  have hden : 0 < (5-2*q)*(5-2*delta) := by positivity
  have hprod : 8 ≤ (5-2*q)*(5-2*delta) := by norm_num [q] at *; linarith [hd.2]
  have hratio : (2/5)/((5-2*q)*(5-2*delta)) ≤ 1/20 := by
    rw [div_le_iff₀ hden]
    linarith
  have hid : tail q-tail delta = (delta-q)*((2/5)/((5-2*q)*(5-2*delta))) := by
    unfold tail
    rw [show rho delta = rho q-50*(delta-q)/(3*(5-2*q)*(5-2*delta)) by
      linarith [rho_difference q delta hq hdp]]
    field_simp
    <;> ring
  rw [hid]
  have hh := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hd.1)
  linarith

theorem channel_reserves (b delta : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q ≤ delta ∧ delta ≤ 7/10) :
    highReserve ≤ high b delta+gamma delta*supplied b-loss ∧
    highReserve ≤ high b delta+rate delta*supplied b-loss ∧
    highReserve ≤ high b delta+rate delta*tau*frequency b-loss ∧
    highReserve ≤ high b delta+tail delta*frequency b-loss := by
  obtain ⟨hc, hm, hcap, ht⟩ := channel_at_q b hb
  obtain ⟨ha0, ha1, hs0, hs1, hf0, hf1, hA⟩ := basic_bounds b hb
  have hh := high_increase b q delta hb (by norm_num [q]) hd.1 (by linarith [hd.2])
  have hg := mul_le_mul_of_nonneg_right (gamma_bounds hd).2.1 hs0
  have hr := mul_le_mul_of_nonneg_right (rate_lipschitz hd) hs0
  have hrcap := mul_le_mul_of_nonneg_right (rate_lipschitz hd)
    (show 0 ≤ tau*frequency b by unfold tau; positivity)
  have htail := mul_le_mul_of_nonneg_right (tail_lipschitz hd) hf0
  have hcap0 : 0 ≤ tau*frequency b := by unfold tau; positivity
  have hcap1 : tau*frequency b ≤ 1/25 := by unfold tau; linarith
  constructor
  · linarith [hd.1]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd.1) (show 0 ≤ 1/5-supplied b by linarith)]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd.1) (show 0 ≤ 1/5-tau*frequency b by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd.1) (show 0 ≤ 1-frequency b by linarith)]

theorem geometry_marked_payment (b delta E target removed live freq analyticLoss : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q ≤ delta ∧ delta ≤ 7/10)
    (hE : E ≤ target-high b delta-gamma delta*removed)
    (hu : 0 ≤ removed) (hlive : 0 ≤ live) (hsupply : supplied b ≤ removed+live)
    (hfrequency : frequency b-2*removed ≤ freq) (hloss : analyticLoss ≤ loss) :
    E-rate delta*min live (tau*freq)+analyticLoss ≤ target-highReserve := by
  obtain ⟨hc, hm, hcap, ht⟩ := channel_reserves b delta hb hd
  have hg := gamma_bounds hd
  have hr := rate_bounds hd
  have hslope : 2*rate delta*tau ≤ gamma delta := by unfold tau; nlinarith [hr.2]
  have hpaid := marked_width_payment (gamma delta) delta (rate delta) tau
    (frequency b) (supplied b) removed 0 live freq (highReserve+loss-high b delta)
    (by linarith [hg.1]) hg.2.2 hr.1 (by norm_num [tau]) hu (by norm_num) hlive
    (by simpa using hsupply) hfrequency hslope (by linarith) (by linarith) (by linarith)
  simp only [mul_zero, add_zero] at hpaid
  linarith

theorem geometry_tail_payment (b delta E target removed freq analyticLoss : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q ≤ delta ∧ delta ≤ 7/10)
    (hE : E ≤ target-high b delta-gamma delta*removed)
    (hu : 0 ≤ removed) (hfrequency : frequency b-2*removed ≤ freq)
    (hloss : analyticLoss ≤ loss) :
    E-tail delta*freq+analyticLoss ≤ target-highReserve := by
  have ht := (channel_reserves b delta hb hd).2.2.2
  have hg := gamma_bounds hd
  have htail := tail_bounds hd
  have hslope : 2*tail delta ≤ gamma delta := by linarith [htail.2,hg.1]
  have hpaid := tail_width_payment (gamma delta) delta (tail delta) (frequency b)
    removed 0 freq (highReserve+loss-high b delta)
    (by norm_num [q] at hd; linarith [hd.1]) htail.1 hu (by norm_num)
    hfrequency hslope (by linarith)
  simp only [mul_zero, add_zero] at hpaid
  linarith

/-- Homogeneous paid ledger, so callers need not divide by the source scale. -/
theorem geometry_marked_payment_scaled (b delta D E target removed live freq analyticLoss : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q ≤ delta ∧ delta ≤ 7/10) (hD : 0≤D)
    (hE : E ≤ target-D*high b delta-gamma delta*removed)
    (hu : 0 ≤ removed) (hlive : 0 ≤ live) (hsupply : D*supplied b ≤ removed+live)
    (hfrequency : D*frequency b-2*removed ≤ freq) (hloss : analyticLoss ≤ D*loss) :
    E-rate delta*min live (tau*freq)+analyticLoss ≤ target-D*highReserve := by
  obtain ⟨hc, hm, hcap, ht⟩ := channel_reserves b delta hb hd
  have hcD := mul_le_mul_of_nonneg_left hc hD
  have hmD := mul_le_mul_of_nonneg_left hm hD
  have hcapD := mul_le_mul_of_nonneg_left hcap hD
  have hg := gamma_bounds hd
  have hr := rate_bounds hd
  have hslope : 2*rate delta*tau ≤ gamma delta := by unfold tau; nlinarith [hr.2]
  have hpaid := marked_width_payment (gamma delta) delta (rate delta) tau
    (D*frequency b) (D*supplied b) removed 0 live freq (D*(highReserve+loss-high b delta))
    (by linarith [hg.1]) hg.2.2 hr.1 (by norm_num [tau]) hu (by norm_num) hlive
    (by simpa using hsupply) hfrequency hslope (by nlinarith) (by nlinarith) (by nlinarith)
  simp only [mul_zero, add_zero] at hpaid
  nlinarith

theorem geometry_tail_payment_scaled (b delta D E target removed freq analyticLoss : ℝ)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q ≤ delta ∧ delta ≤ 7/10) (hD : 0≤D)
    (hE : E ≤ target-D*high b delta-gamma delta*removed)
    (hu : 0 ≤ removed) (hfrequency : D*frequency b-2*removed ≤ freq)
    (hloss : analyticLoss ≤ D*loss) :
    E-tail delta*freq+analyticLoss ≤ target-D*highReserve := by
  have ht := (channel_reserves b delta hb hd).2.2.2
  have htD := mul_le_mul_of_nonneg_left ht hD
  have hg := gamma_bounds hd
  have htail := tail_bounds hd
  have hslope : 2*tail delta ≤ gamma delta := by linarith [htail.2,hg.1]
  have hpaid := tail_width_payment (gamma delta) delta (tail delta) (D*frequency b)
    removed 0 freq (D*(highReserve+loss-high b delta))
    (by norm_num [q] at hd; linarith [hd.1]) htail.1 hu (by norm_num)
    hfrequency hslope (by nlinarith)
  simp only [mul_zero, add_zero] at hpaid
  nlinarith

end
end Target874836.SourceProvider.Named

#print axioms Target874836.SourceProvider.Named.low_exact
#print axioms Target874836.SourceProvider.Named.channel_reserves
#print axioms Target874836.SourceProvider.Named.geometry_marked_payment
#print axioms Target874836.SourceProvider.Named.geometry_tail_payment

#print axioms Target874836.SourceProvider.Named.geometry_marked_payment_scaled
#print axioms Target874836.SourceProvider.Named.geometry_tail_payment_scaled
