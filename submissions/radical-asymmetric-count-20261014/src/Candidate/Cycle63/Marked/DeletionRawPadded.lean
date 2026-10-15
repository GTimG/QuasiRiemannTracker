import Candidate.Cycle63.Marked.DeletionSmallRoot

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- A small positive enlargement of the core window absorbs the fixed
natural conductor constant while preserving each physical slot scale. -/
theorem core_window_scale_padded (U N κ pad : ℝ) (hU : 1< U) (hN : 1≤ N)
    (hκ : κ<1/6) (hcap : N≤ U^κ) (hpad : 0≤ pad) :
    ∃d : ℝ,0< d ∧ 1-6*κ+pad≤ d ∧ d≤1+pad ∧
      U^d=(U/N^6)*U^pad ∧ ∀w : ℝ,(U^d)^(w/d)=U^w := by
  obtain ⟨q,hq,hq0,hq1,hbase,hscale⟩ := core_window_scale U N κ hU hN hκ hcap
  have hd : 0< q+pad := add_pos_of_pos_of_nonneg hq hpad
  refine ⟨q+pad,hd,by linarith,by linarith,?_,?_⟩
  · rw [Real.rpow_add (zero_lt_one.trans hU),hbase]
  · intro w
    rw [←Real.rpow_mul (zero_lt_one.trans hU).le,mul_div_cancel₀ _ hd.ne']

/-- Conductor padding has exactly the additional density cost pad*ρ;
normalization retains the full physical amplitude and width saving. -/
theorem rescaled_marked_power_padded (U Y d d₀ dmax pad ρ δ S g cap loss : ℝ)
    (hU : 1≤ U) (hY : 0< Y) (hd : 0< d) (hd₀ : d₀≤ d) (hdmax : d≤ dmax)
    (hbase : U^d=Y*U^pad) (hg : 0≤ g) (hcap : 0≤ cap) (hloss : 0≤ loss) :
    (U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss) ≤
      U^(δ*S-g*min S (cap*d₀)+dmax*loss+pad*ρ)*Y^ρ := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hmin : d*min (S/d) cap = min S (cap*d) := by
    rw [mul_min_of_nonneg _ _ hd.le,mul_div_cancel₀ _ hd.ne',mul_comm d cap]
  have hminmono : min S (cap*d₀)≤ min S (cap*d) :=
    min_le_min_left S (mul_le_mul_of_nonneg_left hd₀ hcap)
  have hcore : (U^d)^ρ=Y^ρ*U^(pad*ρ) := by
    rw [hbase,Real.mul_rpow hY.le (Real.rpow_nonneg hUp.le _),←Real.rpow_mul hUp.le]
  calc
    _ ≤ U^(δ*S-g*min S (cap*d₀)+dmax*loss)*(U^d)^ρ := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
      apply Real.rpow_le_rpow_of_exponent_le hU
      have he : d*(δ*(S/d))=δ*S := by field_simp
      have heq : d*(ρ+δ*(S/d)-g*min (S/d) cap+loss)=
          d*ρ+δ*S-g*(d*min (S/d) cap)+d*loss := by rw [←he];ring
      rw [heq,hmin]
      nlinarith [mul_le_mul_of_nonneg_left hminmono hg,
        mul_le_mul_of_nonneg_right hdmax hloss]
    _ = _ := by rw [hcore];simp only [Real.rpow_add hUp];ring

/-- Max-product version of the actual small-root lift, with the fixed
conductor enlargement made explicit. Finite omitted cores are paid from
the same pointwise raw envelope. -/
theorem small_root_max_fiber_from_padded_core {Slot : Type*}
    (R : Finset NonzeroFrequency) (B : NZIdeal) (E : Finset FreeRow)
    (slots : Finset Slot) (Qraw : NonzeroFrequency→Slot→ℂ) (Qcore : FreeRow→Slot→ℂ)
    (U C κ pad ρ δ S g cap loss : ℝ)
    (hU : 1< U) (hC : 0≤ C) (hκ : κ<1/6) (hpad : 0≤ pad)
    (hB : (B.val.absNorm : ℝ)≤ U^κ) (hg : 0≤ g) (hcap : 0≤ cap)
    (hloss : 0≤ loss) (hρ : g*cap≤ρ) (hρ0 : 0≤ρ)
    (hpoint : ∀u∈sixthFreeFiber R B,
      (∏s∈slots,max 1 ‖Qraw (sixthFrequencyEquiv (u,B)) s‖)^2≤
        U^(δ*S+(1+pad)*loss+pad*ρ))
    (hclose : ∀u∈sixthFreeFiber R B,u∉E → ∀s∈slots,
      ‖Qraw (sixthFrequencyEquiv (u,B)) s-Qcore u s‖≤1/2)
    (hcore : ∀d : ℝ,0< d → 1-6*κ+pad≤ d → d≤1+pad →
      U^d=(U/(B.val.absNorm : ℝ)^6)*U^pad →
      (∑u∈(sixthFreeFiber R B).filter (fun u=>u∉E),
        (∏s∈slots,max 1 ‖Qcore u s‖)^2) ≤
        C*(U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss)) :
    (∑u∈sixthFreeFiber R B,(∏s∈slots,max 1 ‖Qraw (sixthFrequencyEquiv (u,B)) s‖)^2) ≤
      ((4:ℝ)^slots.card*C+(E.card:ℝ))*
        (U^(δ*S+(1+pad)*loss+pad*ρ-g*min S (cap*(1-6*κ)))*
          (U/(B.val.absNorm : ℝ)^6)^ρ) := by
  have hBN : 1≤(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hUp : 0< U := zero_lt_one.trans hU
  have hBp : 0<(B.val.absNorm : ℝ) := zero_lt_one.trans_le hBN
  obtain ⟨d,hd,hd₀,hd1,hbase,hscale⟩ := core_window_scale_padded U _ κ pad hU hBN hκ hB hpad
  have hpow := rescaled_marked_power_padded U (U/(B.val.absNorm : ℝ)^6)
    d (1-6*κ) (1+pad) pad ρ δ S g cap loss hU.le (by positivity) hd
    (by linarith) hd1 hbase hg hcap hloss
  have hgain : g*min S (cap*(1-6*κ))≤(1-6*κ)*ρ := by
    have h1 := mul_le_mul_of_nonneg_left (min_le_right S (cap*(1-6*κ))) hg
    have h2 := mul_le_mul_of_nonneg_right hρ (show 0≤1-6*κ by linarith)
    nlinarith
  have henv := small_root_exception_envelope U (B.val.absNorm : ℝ) κ ρ
    (δ*S+(1+pad)*loss+pad*ρ) (g*min S (cap*(1-6*κ))) hU hBN hB hρ0 hgain
  apply finite_exception_weighted_extension (sixthFreeFiber R B) E
    (fun u=>(∏s∈slots,max 1 ‖Qraw (sixthFrequencyEquiv (u,B)) s‖)^2)
    ((4:ℝ)^slots.card*C) (U^(δ*S+(1+pad)*loss+pad*ρ)) _ (by positivity) henv hpoint
  calc
    _ ≤ (4:ℝ)^slots.card * ∑u∈(sixthFreeFiber R B).filter (fun u=>u∉E),
          (∏s∈slots,max 1 ‖Qcore u s‖)^2 := by
      rw [Finset.mul_sum]
      have hh := Finset.sum_le_sum (s := (sixthFreeFiber R B).filter (fun u=>u∉E))
        (fun u hu=>max_slot_product_comparison slots
          (Qraw (sixthFrequencyEquiv (u,B))) (Qcore u)
          (hclose u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2))
      convert hh using 1
      congr 1
      ext u
      simp
    _ ≤ (4:ℝ)^slots.card*(C*(U^d)^(ρ+δ*(S/d)-g*min (S/d) cap+loss)) :=
      mul_le_mul_of_nonneg_left (hcore d hd hd₀ hd1 hbase) (by positivity)
    _ ≤ (4:ℝ)^slots.card*(C*(U^(δ*S-g*min S (cap*(1-6*κ))+(1+pad)*loss+pad*ρ)*
          (U/(B.val.absNorm : ℝ)^6)^ρ)) := by gcongr
    _ = _ := by
      rw [show δ*S-g*min S (cap*(1-6*κ))+(1+pad)*loss+pad*ρ =
        δ*S+(1+pad)*loss+pad*ρ-g*min S (cap*(1-6*κ)) by ring]
      ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.core_window_scale_padded
#print axioms OAI.SevenEighths.Deletion26.rescaled_marked_power_padded
#print axioms OAI.SevenEighths.Deletion26.small_root_max_fiber_from_padded_core
