/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual per-terminal raw-ticket admission, with true primal/dual ratios and
original reciprocal cutoffs. All closed mixed leaves retain their own boxes. -/
import Candidate.C092.transport.RawTicketInner
import Candidate.C092.transport.RawTicketNeed
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.ContactCertificate

/-- No refined B substitutes for the original coarse-band debit. The original
primal norm-bin interval is compared to the genuine continuous witness width. -/
theorem every_primal_dual_ratio {r : Row} (hr : r∈rows) (sep : ℝ) {ξ n : ℝ}
    (hξ : 0≤ξ ∧ ξ≤(rowGamma r.box r.B:ℝ))
    (hn : let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
      let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
      primalLo D≤n ∧ n≤primalHi (funded debit (D*(r.box.uLo:ℝ)/4))) :
    let y:=offsetWidth (rowM r.box) (1/10^(13:ℕ)) ((rowGamma r.box r.B:ℝ)/65536)
      (rowV r.box) r.box.uHi (rowKUpper r.box) ξ
    0<y ∧ 1≤n/y ∧ n/y≤23/20 := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have hadm:=every_original_band hr sep
  have hv:=(original_thresholds_uniform hadm.1 hadm.2.1 ha.1 hb.2 he.2).1
  have hn':=original_primal_band hadm.2.1 hv
  have hnHull : nLo≤n ∧ n≤nHi := ⟨hn'.1.trans hn.1,hn.2.trans hn'.2⟩
  exact primal_dual_ratio hnHull (every_inner_width hr hξ)

theorem actual_crossing_bounds {r : Row} (hr : r∈rows)
    {point : QRH.Coverage.Point} (hp : r.box.Contains point) {contact : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval contact) :
    tLo≤pairedCrossing point.1 point.2 (g0 (wValue contact)) (g1 (wValue contact)) ∧
    pairedCrossing point.1 point.2 (g0 (wValue contact)) (g1 (wValue contact))≤tHi := by
  have h:=row_endpoint_hull hr
  have hd : dLo≤point.1 ∧ point.1≤dHi := ⟨h.1.1.trans hp.1,hp.2.1.trans h.2.1.2⟩
  have hv : pLo≤point.2 ∧ point.2≤pHi := ⟨h.2.2.1.1.trans hp.2.2.1,hp.2.2.2.trans h.2.2.2.2⟩
  have h₀:=g0_receipt_sound hx
  have h₁:=g1_receipt_sound hx
  have hg:=receipt_original_bounds
  have hc:=crossing_bounds hd hv
    ⟨hg.1.trans h₀.1,h₀.2.trans hg.2.2.2.1⟩
    ⟨hg.2.2.2.2.1.trans h₁.1,h₁.2.trans hg.2.2.2.2.2.2.2⟩
  rw [crossing_eq_paired] at hc
  exact hc.2

theorem every_inner_gamma_bound {r : Row} (hr : r∈rows) :
    (rowGamma r.box r.B:ℝ)≤ innerGammaMax := by
  rcases row_inner_parameters hr with ⟨hm,hv,hd,hk,hb,hg0,hg⟩
  exact (inner_width_bounds hm hv hd hk hb hg0 hg ⟨le_rfl,hg0⟩).1

/-- The ORIGINAL physical reciprocal lies beyond EVERY retained bank cutoff.
This keeps the reciprocal norm variable independent of the witness cutoff. -/
theorem every_bank_cutoff {r : Row} (hr : r∈rows) (sep : ℝ)
    {point : QRH.Coverage.Point} (hp : r.box.Contains point) {contact ξ reciprocal : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval contact)
    (hξ : 0≤ξ ∧ ξ≤(rowGamma r.box r.B:ℝ))
    (hrec : let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
      let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
      1/(hUpper+rowPad)-funded debit (D/10)≤reciprocal) :
    let cut:=pairedCrossing point.1 point.2 (g0 (wValue contact)) (g1 (wValue contact))-ξ
    1<cut ∧ cut<3/2 ∧ cut<reciprocal := by
  have hc:=actual_crossing_bounds hr hp hx
  have hg:=every_inner_gamma_bound hr
  have hxi : ξ≤ innerGammaMax := hξ.2.trans hg
  have hlow : 1<tLo-innerGammaMax := by norm_num [tLo,innerGammaMax]
  have hhigh : tHi<3/2 := by norm_num [tHi]
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have hadm:=every_original_band hr sep
  have hdn:=(original_thresholds_uniform hadm.1 hadm.2.1 ha.1 hb.2 he.2).2.1
  have hrecip:=original_reciprocal_order hdn
  dsimp only
  constructor
  · linarith only [hc.1,hxi,hlow]
  constructor
  · linarith only [hc.2,hξ.1,hhigh]
  · linarith only [hc.2,hξ.1,hrecip,hrec]

/-- The top endpoint used by the ORIGINAL six continuation fees. -/
def oldTop (r : Row) : ℝ := crossing r.box.uHi r.box.vLo
  (5805911/100000000) (379981/5000000)

theorem old_top_bounds {r : Row} (hr : r∈rows) : 0≤oldTop r ∧ oldTop r≤tHi := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have ht:=crossing_bounds hb hf (by norm_num : (5805911/100000000:ℝ)≤5805911/100000000 ∧ (5805911/100000000:ℝ)≤5805913/100000000)
    (by norm_num : (3799809/50000000:ℝ)≤379981/5000000 ∧ (379981/5000000:ℝ)≤379981/5000000)
  exact ⟨(by norm_num [tLo] : (0:ℝ)≤tLo).trans ht.2.1,ht.2.2⟩

theorem every_original_six {r : Row} (hr : r∈rows) (sep : ℝ) :
    let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    ∀ gap∈continuationGaps r.box.vLo r.box.vHi (oldTop r),
      8*oldFee<3*D*(r.box.uLo:ℝ)*gap/4-debit :=
  every_original_continuation hr sep (oldTop r) (old_top_bounds hr)

/-- The ninth original reserve (middle width) is also funded at the original
1e−9 fee; the smaller refined witness fee is not used here. -/
theorem every_original_middle {r : Row} (hr : r∈rows) (sep γ : ℝ) :
    let debit:=oldDebit r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    let D:=Dlow r.box.uLo r.box.uHi r.box.vLo r.box.vHi sep
    8*oldFee<D*(r.box.uLo:ℝ)*((r.box.vLo:ℝ)*originalNeed debit D r.box.uLo r.box.vLo r.box.vHi γ-
      (1-(r.box.vLo:ℝ)*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2-(r.box.vHi:ℝ)*oldAnn/2)-debit := by
  rcases row_endpoint_hull hr with ⟨ha,hb,hf,he⟩
  have hD:=(every_original_band hr sep).2.1
  exact original_need_paid
    (lt_of_lt_of_le (by norm_num [Dmin]) hD)
    (lt_of_lt_of_le (by norm_num [dLo]) ha.1)
    (lt_of_lt_of_le (by norm_num [pLo]) hf.1)

/-- The literal positive source/padding cost is paid after the original fees. -/
theorem original_fee_after_padding {reserve : ℝ} (hr : 8*oldFee<reserve) :
    3*oldFee<reserve-paddingDebit := by
  have hp : rowPad≤1/10^(20:ℕ) := by
    change 1/(10:ℝ)^258≤1/(10:ℝ)^20
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hs : sourceCost≤1/10^(20:ℕ) := by
    change 1/(10:ℝ)^260≤1/(10:ℝ)^20
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  dsimp [paddingDebit,oldFee] at *
  linarith only [hp,hs,hr]

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.every_primal_dual_ratio
#print axioms QRH.Cycle092.RawTicket.actual_crossing_bounds
#print axioms QRH.Cycle092.RawTicket.every_bank_cutoff

#print axioms QRH.Cycle092.RawTicket.every_original_six
#print axioms QRH.Cycle092.RawTicket.every_original_middle

#print axioms QRH.Cycle092.RawTicket.original_fee_after_padding
