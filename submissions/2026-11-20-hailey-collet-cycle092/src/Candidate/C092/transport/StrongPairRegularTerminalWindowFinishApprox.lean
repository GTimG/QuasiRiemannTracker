/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual ordinary P4 debit, both height factors and whole-slot complement. -/
import Candidate.C092.transport.StrongPairRegularTerminalWindowApprox
import Candidate.C092.transport.StrongPairOrdinaryNearFinish
import Candidate.C092.transport.StrongPairOrdinaryErase
import Candidate.C092.transport.StrongPairOrdinaryHeight

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.WholeSlot
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness

theorem terminal_window_p4_finish_approx {Row Slot Label : Type*}
    [Fintype Row] [Fintype Slot] [DecidableEq Slot]
    {χ : Row→Label→Character}
    {U a ε allowance n y e el νlower step price V d dmax cap radius decrement rounding collar Cslot buffer τ εsource
      tMark tLong height K m r : ℝ} {i I degree J : ℕ}
    (c : Cutoff) (ws : ∀ z,SupportedWitness (χ z) (U^d) a ε (totalCutoff c) (U^τ) allowance i)
    (hm : ∀ z,(ws z).m=m) (hr : ∀ z,(ws z).r < (c.inverse:ℝ))
    (hy0 : sourceY0 ≤ y) (hy : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (hel0 : 0 ≤ el) (hel1 : el ≤ (responseUpper:ℝ))
    (hνlo : el ≤ νlower) (hνhi : νlower ≤ 3/4)
    (hνactual0 : νlower ≤ 2*a-1+price) (hνactual1 : 2*a-1 ≤ νlower+step)
    (heu : e ≤ el+step) (hstep : 0 ≤ step) (hprice : 0 ≤ price) (hνpos : 0 ≤ 2*a-1)
    {b : ℚ} (hg : CutoffGuard b c)
    (hc : y/(H:ℝ) ≤ (c.ordinary:ℝ)) (hc0 : sourceY0 ≤ (c.ordinary:ℝ))
    (hp : PaidWithBand y el νlower c) (hε : 0 ≤ ε)
    (hV : (98/100:ℝ) ≤ V) (hdV : V ≤ d) (hdc : d ≤ V+collar)
    (hradius : (98/100:ℝ) ≤ radius) (hradiusd : radius ≤ min d (H:ℝ))
    (hcap : collaredOrdinaryCap c m ≤ cap) (hdec : 0 ≤ decrement) (hround : 0 ≤ rounding)
    (hL : sourceWidth n y-(u:ℝ) ≤ 1)
    (hquota : 0 ≤ nearOrdinaryQuota n cap radius-decrement) (hround1 : rounding ≤ 1)
    (hfees : collar+(15/4)*d*ε+
      el*(d*((5/4:ℝ)*(min d (H:ℝ)-radius)+(3/4:ℝ)*(cap-collaredOrdinaryCap c m))+d*decrement+rounding)+
        (d*εsource+buffer*((Finset.univ\(∅:Finset Slot)).card:ℝ)+τ*((degree+2*J+1:ℕ):ℝ))+3*step+price*d*m ≤ (3/4)*(rho:ℝ))
    (F : Finset Slot) (weight : Row→ℝ) (A B : Row→ℂ) (mark : Slot→Row→ℂ) (w : Slot→ℝ)
    (hU : 1 < U) (heK : 0 ≤ Cslot) (hK : 0 ≤ K) (hbuffer : 0 ≤ buffer)
    (hw : ∀ z,0 ≤ weight z) (hwidth : (∑ k,w k) ≤ sourceWidth n y-(u:ℝ))
    (hdelete : (∑ k∈Finset.univ\F,w k) ≤
      max 0 ((∑ k,w k)-d*(nearOrdinaryQuota n cap radius-decrement)+rounding))
    (hmark : ∀ z,∀ k∈Finset.univ\F,‖mark k z‖^2 ≤ (Cslot*U^buffer)*U^(e*w k))
    (hshort : d*r ≤ y) (hdmax : d ≤ dmax) (hdmax0 : 0 < dmax) (hτ : 0 ≤ τ) (hi : i ≤ I)
    (hheight : 0 ≤ height) (hsmall : |tMark|+|tLong|+height ≤ U^τ)
    (hp4 : (∑ z,weight z*‖A z*B z*(∏ k∈F,mark k z)‖^2) ≤
      K*(1+|tLong|+(|tMark|+|tLong|+height))^degree*
        (1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ))^(2*J+1)*
          U^((2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource))) :
    (∑ z,weight z*‖A z*B z*(∏ k,mark k z)‖^2) ≤
      (Cslot^(Finset.univ\F).card*K*(4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
        U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  have hUp : 0 < U := zero_lt_one.trans hU
  have hν0 : 0 ≤ 2*a-1 := hνpos
  let D : ℕ := degree+2*J+1
  let extra : ℝ := d*εsource+buffer*((Finset.univ\F).card:ℝ)+τ*(D:ℝ)
  have hcount : (Finset.univ\F).card ≤ (Finset.univ\(∅:Finset Slot)).card := by
    simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ\F))
  have hcountR : ((Finset.univ\F).card:ℝ) ≤ ((Finset.univ\(∅:Finset Slot)).card:ℝ) := by exact_mod_cast hcount
  have hfees' : collar+(15/4)*d*ε+
      el*(d*((5/4:ℝ)*(min d (H:ℝ)-radius)+(3/4:ℝ)*(cap-collaredOrdinaryCap c m))+d*decrement+rounding)+extra+3*step+price*d*m ≤ (3/4)*(rho:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hcountR hbuffer
    dsimp [extra,D]
    linarith
  have hh := ordinary_height_payment degree J I i hU hdmax hdmax0 hτ hi hheight hsmall
  let Kpaid : ℝ := K*(4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1)
  have hKpaid : 0 ≤ Kpaid := by dsimp [Kpaid]; positivity
  have hp4' : (∑ z,weight z*‖A z*B z*(∏ k∈F,mark k z)‖^2) ≤
      Kpaid*U^(d+(2*a-1)*(y-d*m)+3*d*ε+extra-buffer*((Finset.univ\F).card:ℝ)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hU.le
      (show (2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource) ≤
        (2*a-1)*(y-d*m)+3*d*ε+d*(1+εsource) from by nlinarith [mul_le_mul_of_nonneg_left hshort hν0])
    calc
      _ ≤ K*(1+|tLong|+(|tMark|+|tLong|+height))^degree*
          (1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ))^(2*J+1)*
          U^((2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource)) := hp4
      _ ≤ Kpaid*U^(τ*(D:ℝ))*U^((2*a-1)*(y-d*m)+3*d*ε+d*(1+εsource)) := by
        have hbase := mul_le_mul_of_nonneg_left hh hK
        dsimp [Kpaid,D]
        have hsrc0 : 0 ≤ 1+|tLong|+(|tMark|+|tLong|+height) := by positivity
        calc
          _ ≤ (K*((4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
              U^(τ*((degree+2*J+1:ℕ):ℝ)))*
              U^((2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource)) := by
                have hm := mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hUp.le ((2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource)))
                convert hm using 1 <;> ring
          _ ≤ _ := by
            have hh := mul_le_mul_of_nonneg_left hpow
              (show 0 ≤ (K*((4:ℝ)^degree*(1+2*Real.pi+(3*I:ℕ))^(2*J+1)))*U^(τ*((degree+2*J+1:ℕ):ℝ)) by positivity)
            convert hh using 1 <;> ring
      _ = _ := by
        rw [mul_assoc,←Real.rpow_add hUp]
        dsimp [extra]
        congr 1
        congr 1
        ring
  cases isEmpty_or_nonempty Row with
  | inl hempty =>
      letI := hempty
      simp only [Finset.univ_eq_empty,Finset.sum_empty]
      positivity
  | inr hrow =>
      letI := hrow
      let z : Row := Classical.choice hrow
      have hpaid := terminal_ordinary_window_paid_approx c (ws z) hy0 hy hyn hn hel0 hel1 hνlo hνhi hg hc hc0 hp hε (hr z)
        hV hdV hdc hradius hradiusd (by simpa only [hm z] using hcap) hdec hround
        hνactual0 hνactual1 heu hstep hprice hL hquota hround1
        (by simpa only [hm z] using hfees')
      rw [hm z] at hpaid
      have hf := weighted_near_paid F weight A B mark w hU.le he0 heK hKpaid hw hwidth hdelete hmark hp4' hpaid.le
      convert hf using 1 <;> dsimp [Kpaid] <;> ring

#print axioms terminal_window_p4_finish_approx
end
end QRH.Cycle092.StrongPair
