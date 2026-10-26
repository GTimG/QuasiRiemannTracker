/- Exact scalar cancellation after the actual native physical LOW source. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section

/-- Pay only the genuine OLD term and cancel the literal inverse outer
factor from the returned term. This identity adds no source estimate. -/
theorem native_small_physical_paid
    {Z outer fee cost old Cu pref A Cg fixed physical value target : ℝ}
    (hZ : 0<Z)(hCu : 0≤Cu)(hpref : 0≤pref)(hA : 0≤A)
    (hfixed : 0≤fixed)(hphysical : 0≤physical)
    (hsource : cost≤pref*(max 0 old*(Cu*Z^fee)+2*(Cu*(Z^(-outer)*(Cg*fixed*physical)))*value))
    (hpaid : Z^outer*Z^fee*old≤A*fixed*physical*Z^(outer+target)) :
    Z^outer*cost≤(pref*Cu*A)*fixed*physical*Z^(outer+target)+
      (pref*(2*(Cu*Cg)))*fixed*physical*value:=by
  have hz : 0≤Z^outer:=Real.rpow_nonneg hZ.le _
  have hK : 0≤A*fixed*physical*Z^(outer+target):=by positivity
  have hmax : Z^outer*Z^fee*max 0 old≤A*fixed*physical*Z^(outer+target):=by
    by_cases ho : 0≤old
    · simpa only [max_eq_right ho] using hpaid
    · have ho' : old≤0:=le_of_not_ge ho
      simpa only [max_eq_left ho',mul_zero] using hK
  have hown:=mul_le_mul_of_nonneg_left hmax (mul_nonneg hpref hCu)
  have hraw:=mul_le_mul_of_nonneg_left hsource hz
  have hcancel : Z^outer*Z^(-outer)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  calc
    Z^outer*cost≤Z^outer*(pref*(max 0 old*(Cu*Z^fee)+2*(Cu*(Z^(-outer)*(Cg*fixed*physical)))*value)):=hraw
    _=(pref*Cu)*(Z^outer*Z^fee*max 0 old)+
        (pref*(2*(Cu*Cg)))*fixed*physical*value:=by
      calc
        _=(pref*Cu)*(Z^outer*Z^fee*max 0 old)+
            (pref*(2*(Cu*Cg)))*fixed*physical*value*(Z^outer*Z^(-outer)):=by ring
        _=_:=by rw [hcancel,mul_one]
    _≤(pref*Cu)*(A*fixed*physical*Z^(outer+target))+
        (pref*(2*(Cu*Cg)))*fixed*physical*value:=add_le_add hown le_rfl
    _=_:=by ring

/-- The SAME shifted source height fits the combined small-height
polynomial, before the single final three-height splice. -/
theorem native_small_source_height_control
    (second : Bool)(firstHeight height t0 u : ℝ)(hheight : 0≤height)(degree : ℕ) :
    (1+|firstHeight+2*Real.pi*(u-(if second then -t0 else t0))|+height)^degree≤
      (2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|)))^degree:=by
  have hshift : |u-(if second then -t0 else t0)|≤|u|+|t0|:=by
    cases second
    · simpa using abs_sub_le u 0 t0
    · simpa using abs_sub_le u 0 (-t0)
  have hmul : |2*Real.pi*(u-(if second then -t0 else t0))|≤2*Real.pi*(|u|+|t0|):=by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hshift (by positivity)
  have hs:=(abs_add_le firstHeight (2*Real.pi*(u-(if second then -t0 else t0)))).trans
    (add_le_add (le_refl |firstHeight|) hmul)
  have hbase : 1+|firstHeight+2*Real.pi*(u-(if second then -t0 else t0))|+height≤
      2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|)):=by
    have hp : 0≤2*Real.pi*(|t0|+|u|):=by positivity
    nlinarith only [hs,hheight,abs_nonneg firstHeight,hp]
  exact pow_le_pow_left₀ (by positivity) hbase degree
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.native_small_physical_paid
#print axioms OAI.SevenEighths.Cycle153ActualColumn.native_small_source_height_control
