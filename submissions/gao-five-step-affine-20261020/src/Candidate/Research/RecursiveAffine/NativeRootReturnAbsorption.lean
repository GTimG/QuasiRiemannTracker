/- Final actual ROOT count absorbs the fixed analytic return coefficient.
Original native-count assembly and strengthening (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootUniformCountConstants
import Candidate.Research.RecursiveAffine.NativeGlobalDyadBox

set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Filter Cycle153SourceReturn Cycle153JointCount Cycle153SourceSchedule

private theorem constant_box_product_bound
    (Z cb eps : ℝ)(box : Finset (Fin 4→ℤ))(n : ℕ)
    (hZ : 1 ≤ Z)(hcb : 0 ≤ cb)(heps : 0 ≤ eps)(hn : n ≤ 4)
    (hc : (box.card:ℝ) ≤ cb*Z^eps) :
    (∏_k∈Finset.range n,((box.card:ℝ)+1)) ≤ (cb+1)^4*Z^(4*eps) := by
  have hp : 1 ≤ Z^eps:=Real.one_le_rpow hZ heps
  have h1 : (box.card:ℝ)+1 ≤ (cb+1)*Z^eps := by nlinarith only [hc,hp]
  have hbase : 0 ≤ (box.card:ℝ)+1:=by positivity
  have hpow:=pow_le_pow_left₀ hbase h1 n
  simp only [Finset.prod_const,Finset.card_range] at hpow ⊢
  have hcpow : (cb+1)^n ≤ (cb+1)^4:=pow_le_pow_right₀ (by linarith only [hcb]) hn
  have heq : (Z^eps)^n=Z^((n:ℝ)*eps) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ)]
    congr 1
    ring
  rw [mul_pow,heq] at hpow
  have hnR : (n:ℝ) ≤ 4:=by exact_mod_cast hn
  have hZpow : Z^((n:ℝ)*eps) ≤ Z^(4*eps):=
    Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hnR heps)
  exact hpow.trans (mul_le_mul hcpow hZpow (Real.rpow_nonneg (zero_le_one.trans hZ) _) (by positivity))

/-- The original zero-height exponent is chosen from the native density
degrees before any moving source. An extra cap pays the final finite
height union even if a later primitive loss schedule is changed. -/
private theorem finite_height_payment (J : SuffixDepth 4→ℕ)(cap : ℝ)(hcap : 0<cap) :
    ∃tau : ℝ,0<tau ∧ tau ≤ cap ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧∀d,(1+Z^tau)^(J d) ≤ Z^(1/1000000000:ℝ) := by
  let cap':=min cap ((1/1000000000:ℝ)/(2*((Finset.univ.sup J:ℕ)+1:ℝ)))
  have hc' : 0<cap':=lt_min hcap (div_pos (by norm_num) (by positivity))
  let tau:=rootZeroExponent J cap'
  have ht : 0<tau:=rootZeroExponent_pos J hc'
  have htcap : tau ≤ cap':=(rootZeroExponent_density J hc' (none:SuffixDepth 4)).1
  have hsmall : tau ≤ (1/1000000000:ℝ)/(2*((Finset.univ.sup J:ℕ)+1:ℝ)):=
    htcap.trans (min_le_right _ _)
  refine ⟨tau,ht,htcap.trans (min_le_left _ _),?_⟩
  filter_upwards [(tendsto_rpow_atTop ht).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hx hZ
  refine ⟨hZ,?_⟩
  intro d
  have hJ : (J d:ℝ) ≤ (Finset.univ.sup J:ℕ):=by exact_mod_cast Finset.le_sup (Finset.mem_univ d)
  have hbudget : 2*tau*(J d:ℝ) ≤ 1/1000000000 := by
    have hden : 0<2*((Finset.univ.sup J:ℕ)+1:ℝ):=by positivity
    have hb:=(le_div_iff₀ hden).mp hsmall
    have hm:=mul_le_mul_of_nonneg_left hJ ht.le
    nlinarith only [hb,hm,ht]
  have hquad : 1+Z^tau ≤ (Z^tau)^2:=by nlinarith only [hx]
  calc
    _ ≤ ((Z^tau)^2)^(J d):=pow_le_pow_left₀ (by positivity) hquad _
    _=Z^(2*tau*(J d:ℝ)):=by
      rw [←pow_mul,←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hZ).le]
      congr 1
      push_cast
      ring
    _ ≤ _:=Real.rpow_le_rpow_of_exponent_le hZ.le hbudget

/-- The height exponent is chosen before the actual HIGH class cap and
the analytic return coefficient.
After one real root forest is constructed, all finite reflection,
depth, absolute-dyad and zero-height factors are absorbed at a fixed
threshold. Native density constants and the height exponent precede Z
and every moving source. The ONLY substantive source input is an actual
energy-free NativeRootForestReceipt; no root moment, energy, weighted
class or arbitrary source-cardinality bound is assumed. -/
theorem actual_root_forest_scaled_threshold_absorption
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M ≤ H)
    (eta : Character)(Bsrc Bnorm cap : ℝ)(N : ℕ)
    (hBsrc : 0 ≤ Bsrc)(hBnorm : 0 ≤ Bnorm)(hcap : 0<cap)
    (hbudget : ∀d : SuffixDepth 4,(rootHistoryDepth d:ℝ)*Bsrc ≤ Bnorm) :
    ∃tau : ℝ,0<tau ∧ tau ≤ cap ∧
    ∀(Kclass : ℝ),0≤Kclass→∀(Kreturn : ℝ),0≤Kreturn→∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{α : Type}[Fintype α][DecidableEq α](C : SourceContext (α:=α) M H),
      C.globalBase=Z → C.etaSeed=eta → C.Bnorm=Bnorm → C.highClassCap=Kclass → 0 ≤ C.Tz → C.Tz ≤ Z^tau →
      ∀F : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc (fun _=>rootNativeDyadBox Z N),
        Kreturn*F.family.value ≤ Z := by
  let native:=fun d : SuffixDepth 4=>root_fixed_component_count_constants M H hH eta Bsrc Bnorm
    (1/1000000000) hBsrc hBnorm (by norm_num) d (hbudget d)
  let J:=fun d=>Classical.choose (native d)
  let Cd:=fun d=>Classical.choose (Classical.choose_spec (native d))
  have hCd : ∀d,0<Cd d:=fun d=>(Classical.choose_spec (Classical.choose_spec (native d))).1
  obtain ⟨tau,ht,hcapTau,hheight⟩:=finite_height_payment J cap hcap
  obtain ⟨Cb,hCb,hbox⟩:=root_native_dyad_subpower N (1/1000000000) (by norm_num)
  have hexponent : (1:ℝ)-1/10000000+1/10000000000+1/1000000000+
      4*(1/1000000000)+1/1000000000+1/100000000 ≤ 1:=by norm_num
  refine ⟨tau,ht,hcapTau,?_⟩
  intro Kclass hKclass Kreturn hKreturn
  let totalConstant:ℝ:=∑d : SuffixDepth 4,16*Cd d*(Cb+1)^4*Kclass
  have hconstant:= (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100000000)).eventually
    (eventually_ge_atTop (totalConstant*Kreturn))
  filter_upwards [hheight,hbox,hconstant,eventually_ge_atTop (2:ℝ)] with Z hh hb hK hZ2
  have hZ:=hh.1
  have hz:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro α _ _ C hbase heta hnorm hclass hTpos hT F
  have hcomponent (d : SuffixDepth 4) :
      (∑p,F.family.weight d p*(F.family.part d p).value) ≤ (16*Cd d*(Cb+1)^4*Kclass)*Z^((1:ℝ)-1/10000000+1/10000000000+
          1/1000000000+4*(1/1000000000)+1/1000000000) := by
    have hf:=(Classical.choose_spec (Classical.choose_spec (native d))).2 C heta hnorm
      (by rw [hbase];exact hZ2) hTpos (fun _=>rootNativeDyadBox Z N) F
    conv at hf => rhs;rw [hbase,hclass]
    have hn : rootHistoryDepth d ≤ 4:=by have hd:=suffixOffset_lt 4 d;unfold rootHistoryDepth;omega
    have hp:=constant_box_product_bound Z Cb (1/1000000000) (rootNativeDyadBox Z N)
      (rootHistoryDepth d) hZ.le hCb.le (by norm_num) hn hb.2
    have hheightd : (1+C.Tz)^(J d) ≤ Z^(1/1000000000:ℝ) := by
      apply le_trans (pow_le_pow_left₀ (by linarith only [hTpos])
        (show 1+C.Tz ≤ 1+Z^tau by linarith only [hT]) (J d))
      exact hh.2 d
    have hcd:=hCd d
    calc
      _ ≤ 16*Cd d*((Cb+1)^4*Z^(4*(1/1000000000:ℝ)))*Z^(1/1000000000:ℝ)*Kclass*
        Z^((1:ℝ)-1/10000000+1/10000000000+1/1000000000):=by
          apply hf.trans
          gcongr
          all_goals positivity
      _=(16*Cd d*(Cb+1)^4*Kclass)*
        (Z^((1:ℝ)-1/10000000+1/10000000000+1/1000000000)*
          Z^(4*(1/1000000000:ℝ))*Z^(1/1000000000:ℝ)):=by ring
      _=_:=by rw [←Real.rpow_add hz,←Real.rpow_add hz]
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun d _=>hcomponent d)
  rw [←Finset.sum_mul] at hsum
  have hraw : F.family.value ≤ totalConstant*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=hsum
  calc
    _ ≤ Kreturn*(totalConstant*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000)):=mul_le_mul_of_nonneg_left hraw hKreturn
    _ = (totalConstant*Kreturn)*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=by ring
    _ ≤ Z^(1/100000000:ℝ)*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hz.le _)
    _ ≤ Z:=by
      rw [←Real.rpow_add hz]
      calc
        _ ≤ Z^(1:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hexponent])
        _=Z:=Real.rpow_one Z

/-- The same genuine native paid count chooses the height exponent even
before the original dyad-box budget. The budget and both later analytic
constants may affect the eventual cutoff, and never the chosen height. -/
theorem actual_root_forest_scaled_threshold_absorption_all_budgets
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M ≤ H)
    (eta : Character)(Bsrc Bnorm cap : ℝ)
    (hBsrc : 0 ≤ Bsrc)(hBnorm : 0 ≤ Bnorm)(hcap : 0<cap)
    (hbudget : ∀d : SuffixDepth 4,(rootHistoryDepth d:ℝ)*Bsrc ≤ Bnorm) :
    ∃tau : ℝ,0<tau ∧ tau ≤ cap ∧
    ∀N : ℕ,∀(Kclass : ℝ),0≤Kclass→∀(Kreturn : ℝ),0≤Kreturn→∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{α : Type}[Fintype α][DecidableEq α](C : SourceContext (α:=α) M H),
      C.globalBase=Z → C.etaSeed=eta → C.Bnorm=Bnorm → C.highClassCap=Kclass → 0 ≤ C.Tz → C.Tz ≤ Z^tau →
      ∀F : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc (fun _=>rootNativeDyadBox Z N),
        Kreturn*F.family.value ≤ Z := by
  let native:=fun d : SuffixDepth 4=>root_fixed_component_count_constants M H hH eta Bsrc Bnorm
    (1/1000000000) hBsrc hBnorm (by norm_num) d (hbudget d)
  let J:=fun d=>Classical.choose (native d)
  let Cd:=fun d=>Classical.choose (Classical.choose_spec (native d))
  have hCd : ∀d,0<Cd d:=fun d=>(Classical.choose_spec (Classical.choose_spec (native d))).1
  obtain ⟨tau,ht,hcapTau,hheight⟩:=finite_height_payment J cap hcap
  have hexponent : (1:ℝ)-1/10000000+1/10000000000+1/1000000000+
      4*(1/1000000000)+1/1000000000+1/100000000 ≤ 1:=by norm_num
  refine ⟨tau,ht,hcapTau,?_⟩
  intro N Kclass hKclass Kreturn hKreturn
  obtain ⟨Cb,hCb,hbox⟩:=root_native_dyad_subpower N (1/1000000000) (by norm_num)
  let totalConstant:ℝ:=∑d : SuffixDepth 4,16*Cd d*(Cb+1)^4*Kclass
  have hconstant:= (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100000000)).eventually
    (eventually_ge_atTop (totalConstant*Kreturn))
  filter_upwards [hheight,hbox,hconstant,eventually_ge_atTop (2:ℝ)] with Z hh hb hK hZ2
  have hZ:=hh.1
  have hz:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro α _ _ C hbase heta hnorm hclass hTpos hT F
  have hcomponent (d : SuffixDepth 4) :
      (∑p,F.family.weight d p*(F.family.part d p).value) ≤ (16*Cd d*(Cb+1)^4*Kclass)*Z^((1:ℝ)-1/10000000+1/10000000000+
          1/1000000000+4*(1/1000000000)+1/1000000000) := by
    have hf:=(Classical.choose_spec (Classical.choose_spec (native d))).2 C heta hnorm
      (by rw [hbase];exact hZ2) hTpos (fun _=>rootNativeDyadBox Z N) F
    conv at hf => rhs;rw [hbase,hclass]
    have hn : rootHistoryDepth d ≤ 4:=by have hd:=suffixOffset_lt 4 d;unfold rootHistoryDepth;omega
    have hp:=constant_box_product_bound Z Cb (1/1000000000) (rootNativeDyadBox Z N)
      (rootHistoryDepth d) hZ.le hCb.le (by norm_num) hn hb.2
    have hheightd : (1+C.Tz)^(J d) ≤ Z^(1/1000000000:ℝ) := by
      apply le_trans (pow_le_pow_left₀ (by linarith only [hTpos])
        (show 1+C.Tz ≤ 1+Z^tau by linarith only [hT]) (J d))
      exact hh.2 d
    have hcd:=hCd d
    calc
      _ ≤ 16*Cd d*((Cb+1)^4*Z^(4*(1/1000000000:ℝ)))*Z^(1/1000000000:ℝ)*Kclass*
        Z^((1:ℝ)-1/10000000+1/10000000000+1/1000000000):=by
          apply hf.trans
          gcongr
          all_goals positivity
      _=(16*Cd d*(Cb+1)^4*Kclass)*
        (Z^((1:ℝ)-1/10000000+1/10000000000+1/1000000000)*
          Z^(4*(1/1000000000:ℝ))*Z^(1/1000000000:ℝ)):=by ring
      _=_:=by rw [←Real.rpow_add hz,←Real.rpow_add hz]
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun d _=>hcomponent d)
  rw [←Finset.sum_mul] at hsum
  have hraw : F.family.value ≤ totalConstant*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=hsum
  calc
    _ ≤ Kreturn*(totalConstant*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000)):=mul_le_mul_of_nonneg_left hraw hKreturn
    _ = (totalConstant*Kreturn)*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=by ring
    _ ≤ Z^(1/100000000:ℝ)*Z^((1:ℝ)-1/10000000+1/10000000000+
      1/1000000000+4*(1/1000000000)+1/1000000000):=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hz.le _)
    _ ≤ Z:=by
      rw [←Real.rpow_add hz]
      calc
        _ ≤ Z^(1:ℝ):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hexponent])
        _=Z:=Real.rpow_one Z

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_forest_scaled_threshold_absorption

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_forest_scaled_threshold_absorption_all_budgets
