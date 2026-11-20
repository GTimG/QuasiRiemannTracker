/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite actual reference/ordinary caps are fixed BEFORE U. Earlier P.1
supplies one common mesh; native finite-bank metadata precede live labels. -/
import Candidate.C092.transport.RawTicketMiddleSourceWindow
import Candidate.C092.transport.StrongPairOrdinarySupplier
import Candidate.C092.transport.StrongPairLowBank
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.Cycle092.Mixed QRH.Cycle092.StrongPair

/-- The genuine joined source loses at most two cap mesh widths when BOTH
ordered labels are rounded upward inside the actual closed Q corridor. -/
theorem true_width_cap_loss {n N z Y step : ℝ}
    (hz : widthLo≤ z) (hY : Y≤ widthHi) (hnN : n≤ N) (hzY : z≤ Y)
    (hN : N-n< step) (hy : Y-z< step) :
    QRH.Cycle090.sourceWidth n z-2*step< QRH.Cycle090.sourceWidth N Y := by
  have hb:=(beta_comparison hz hzY hY).2
  have hbs : betaSlope≤1/4 := by norm_num [betaSlope,QRH.ContactCertificate.g1Receipt]
  have hmul:=mul_le_mul_of_nonneg_right hbs (sub_nonneg.mpr hzY)
  dsimp [beta] at hb
  dsimp [QRH.Cycle090.sourceWidth]
  linarith only [hb,hmul,hnN,hzY,hN,hy]

/-- A finite bank of genuine P.1 sources, chosen before any live U or dyad.
Its caps dominate the live labels while losing less than decrement of quota. -/
theorem actual_reference_cap_bank (hP1 : EarlierP1) {decrement : ℝ}
    (hd : 0< decrement ∧ decrement≤1/1000) :
    ∃ bank : Finset (ℝ×ℝ),∃ quota : (ℝ×ℝ)→ℝ,
      (∀ B∈bank,nLo≤ B.1 ∧ B.1≤ nHi ∧ widthLo≤ B.2 ∧ B.2≤ widthHi ∧
        0≤ quota B ∧ quota B< QRH.Cycle090.sourceWidth B.1 B.2 ∧ quota B≤7/37 ∧
        PairUniformBox B.1 B.2 (quota B)) ∧
      ∀ n z : ℝ,nLo≤ n → n≤ nHi → widthLo≤ z → z≤ widthHi →
        ∃ B∈bank,n≤ B.1 ∧ z≤ B.2 ∧ QRH.Cycle090.sourceWidth n z-decrement≤ quota B := by
  obtain ⟨ns,hns,hnnet⟩:=finite_upper_cap_bank (by norm_num [nLo,nHi] : nLo≤ nHi)
    (show 0< decrement/4 by linarith only [hd.1])
  obtain ⟨ys,hys,hynet⟩:=finite_upper_cap_bank (by norm_num [widthLo,widthHi] : widthLo≤ widthHi)
    (show 0< decrement/4 by linarith only [hd.1])
  let bank:=ns.product ys
  let quota:=fun B : ℝ×ℝ=> QRH.Cycle090.sourceWidth B.1 B.2-decrement/4
  have hdec : 0< decrement/4 ∧ decrement/4≤1/1000 := by constructor <;> linarith only [hd.1,hd.2]
  refine ⟨bank,quota,?_,?_⟩
  · intro B hB
    obtain ⟨hBn,hBy⟩:=Finset.mem_product.mp hB
    have hn:=hns B.1 hBn
    have hy:=hys B.2 hBy
    have hq:=true_source_quota hn hy hdec
    have hdom:=true_source_ordered_domain hn hy
    exact ⟨hn.1,hn.2,hy.1,hy.2,hq.1,hq.2.1,hq.2.2,
      hP1 _ _ hdom.1 hdom.2.1 hdom.2.2.1 hdom.2.2.2 _ hq.1 hq.2.1⟩
  · intro n z hn0 hn1 hz0 hz1
    obtain ⟨N,hN,hnN,hNgap⟩:=hnnet n hn0 hn1
    obtain ⟨Y,hY,hzY,hYgap⟩:=hynet z hz0 hz1
    have hloss:=true_width_cap_loss hz0 (hys Y hY).2 hnN hzY hNgap hYgap
    refine ⟨(N,Y),Finset.mem_product.mpr ⟨hN,hY⟩,hnN,hzY,?_⟩
    dsimp [quota]
    linarith only [hloss,hd.1]

/-- The cap bank and all source quotas precede one common early mesh.
Use the existing pair_finite_bank_metadata on this finite bank to choose
common degree/controls/C and the radius threshold before U. -/
theorem actual_reference_bank_mesh (hP1 : EarlierP1) {decrement epsilon : ℝ}
    (hd : 0< decrement ∧ decrement≤1/1000) (he : 0< epsilon) :
    ∃ bank : Finset (ℝ×ℝ),∃ quota : (ℝ×ℝ)→ℝ,∃ mesh : ℝ,0< mesh ∧
      (∀ B∈bank,0≤ quota B ∧ quota B< QRH.Cycle090.sourceWidth B.1 B.2 ∧ quota B≤7/37 ∧
        PairUnitBox B.1 B.2 (quota B) mesh epsilon) ∧
      ∀ n z : ℝ,nLo≤ n → n≤ nHi → widthLo≤ z → z≤ widthHi →
        ∃ B∈bank,n≤ B.1 ∧ z≤ B.2 ∧ QRH.Cycle090.sourceWidth n z-decrement≤ quota B := by
  obtain ⟨bank,quota,hbank,hnet⟩:=actual_reference_cap_bank hP1 hd
  obtain ⟨mesh,hm,hsource⟩:=pair_finite_bank_mesh bank Prod.fst Prod.snd quota
    (fun B hB=>(hbank B hB).2.2.2.2.2.2.2) he
  exact ⟨bank,quota,mesh,hm,fun B hB=>⟨(hbank B hB).2.2.2.2.1,
    (hbank B hB).2.2.2.2.2.1,(hbank B hB).2.2.2.2.2.2.1,hsource B hB⟩,hnet⟩

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.actual_reference_cap_bank
#print axioms QRH.Cycle092.RawTicket.actual_reference_bank_mesh
