/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One explicit fee schedule for the restored original frame, its occupied
fixed rows, its filled regular group and its exhausted unmarked group. -/
import Candidate.C092.transport.FirstGroupBudget
import Candidate.C092.transport.RegularFramePriceLoss
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter QRH.SourceCertificate QRH.Cycle092.PackedPrice
namespace QRH.Cycle092.FixedFramePacking

theorem early_constants (N:ℕ) (δ:ℝ) (hδ:0<δ) :
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ Real.logb Z 2  ≤  δ ∧
      ∀j ≤ N,Real.logb Z (64*((2:ℝ)^j)^4)  ≤  δ ∧ Real.logb Z ((2:ℝ)^j)  ≤  δ := by
  filter_upwards [early_dyad_cost (N+1) δ hδ] with Z h
  refine ⟨h.1,?_,fun j hj=>h.2 j (by omega)⟩
  simpa only [pow_one] using (h.2 1 (by omega)).2

theorem hit_fees {Z mesh δ κ α cFee k aRoot u' M c minLog:ℝ}
    (hd:0<δ) (hρ:δ  ≤  (rho:ℝ)/10000) (hZ:1<Z) (hm:0 ≤ mesh) (hm':mesh ≤ δ)
    (hκ:0 ≤ κ) (hkκ:κ ≤ δ) (hconst:0 ≤ α) (hα:α ≤ δ) (hcf:cFee ≤ δ)
    (h2:Real.logb Z 2 ≤ δ) (hA:aRoot ≤ 9179599/10000000)
    (hu:u' ≤ (u:ℝ)) (hu₀:0 ≤ u') (hcol:k ≤ aRoot-c-u'+cFee)
    (hmin:max 0 (115/1000-c) ≤ minLog)
    (hlo:1-6*u'+mesh-(α+3/2*κ) ≤ M) (hhi:M ≤ 2*aRoot+2*cFee+mesh) :
    let err:=3*δ
    (k ≤ 9179599/10000000-c-u'+err) ∧ (1-6*u' ≤ M+err) ∧
    (max 0 (115/1000-c) ≤ minLog+err) ∧ 0 ≤ M ∧ M ≤ 19/10 ∧
    (δ+3*mesh+Real.logb Z 2+(17/6)*err+δ/8 ≤ 3036/100000) ∧
    (∀ w p s, (u:ℝ)-mesh ≤ u' →
      (regular terminalReserve terminalReserve_le).f w p s M+δ+δ  ≤  u'+10*δ) ∧
    (∀ p s,(withLoss exhausted δ hd.le).f u' p s M+δ+δ  ≤  u'+10*δ) := by
  have hδs:δ ≤ 1/10000:=by norm_num [rho] at hρ ⊢;linarith
  have hp:mesh+(α+3/2*κ) ≤ terminalReserve := by
    unfold terminalReserve
    linarith [show 0  ≤  (rho:ℝ) by norm_num [rho]]
  have hcollar:0 ≤ α+3/2*κ:=by linarith
  obtain ⟨h0,h19,hfull,hex⟩:=paid_group_prices hm hlo hu hu₀ hhi hA (by linarith) (by linarith) hcollar hp
  dsimp only
  refine ⟨by linarith,by linarith,by linarith,h0,h19,by linarith,?_,?_⟩
  · intro w p s hfilled;linarith [hfull w p s hfilled]
  · intro p s
    have he:=exhausted_window (ε:=δ) hd.le hcollar (by linarith : 1-6*u' ≤ M+(α+3/2*κ)) p s
    linarith

/-- Finite-class costs convert back to the exact source volume and selected
product without ever using vol≥1. The second vol factor in the actual label
budget is supplied by the physical kernel outside this comparison. -/
theorem frame_price_product {Z V K price u' loss extra:ℝ} (hZ:1<Z) (hv:0<V) (hk:0<K)
    (hpaid:price+extra ≤ u'+loss) :
    Z^(Real.logb Z V+Real.logb Z K+price+extra)  ≤  V*K*Z^u'*Z^loss := by
  have h0:=zero_lt_one.trans hZ
  calc
    _  ≤  Z^(Real.logb Z V+Real.logb Z K+u'+loss) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = _ := by rw [Real.rpow_add h0,Real.rpow_add h0,Real.rpow_add h0,Real.rpow_logb h0 hZ.ne' hv,
      Real.rpow_logb h0 hZ.ne' hk]

#print axioms hit_fees
#print axioms frame_price_product
end QRH.Cycle092.FixedFramePacking
