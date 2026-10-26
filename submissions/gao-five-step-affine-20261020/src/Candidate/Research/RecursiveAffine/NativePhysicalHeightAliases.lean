/- Literal native datum time and physical height controls. Apache-2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
variable {alpha : Type*}[Fintype alpha][DecidableEq alpha]

/-- The physical second datum keeps the actual first-Mellin height.
This is proved before substituting any selected row or source package. -/
theorem native_second_datum_time
    (reflected : Bool)(s : Input alpha)(R seed : Ideal O)
    (Z Mrow amp xi reserve b firstHeight : ℝ)(N : ℕ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key q) :
    (geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key q hz1 hz2 n).input.t=
      firstHeight :=by rfl

def nativePhysicalSourceHeight (second : Bool)(firstHeight t0 u : ℝ) : ℝ :=
  firstHeight+2*Real.pi*(u-(if second then -t0 else t0))

/-- One actual shifted source height is controlled by the same three
physical Mellin heights, independently of rows, rays and buffers. -/
theorem native_physical_source_height_control
    (second : Bool)(firstHeight height t0 u : ℝ)(hheight : 0≤height)(degree : ℕ) :
    (1+|nativePhysicalSourceHeight second firstHeight t0 u|+height)^degree≤
      (2+4*Real.pi)^degree*(1+|firstHeight|+height)^degree*(1+|t0|)^degree*(1+|u|)^degree :=by
  have hshift : |u-(if second then -t0 else t0)|≤|u|+|t0|:=by
    cases second
    · simpa using abs_sub_le u 0 t0
    · simpa using abs_sub_le u 0 (-t0)
  have hmul : |2*Real.pi*(u-(if second then -t0 else t0))|≤2*Real.pi*(|u|+|t0|):=by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hshift (by positivity)
  have hs:=(abs_add_le firstHeight (2*Real.pi*(u-(if second then -t0 else t0)))).trans
    (add_le_add (le_refl |firstHeight|) hmul)
  have hbase : 1+|nativePhysicalSourceHeight second firstHeight t0 u|+height≤
      2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|)):=by
    dsimp only [nativePhysicalSourceHeight]
    have hp : 0≤2*Real.pi*(|t0|+|u|):=by positivity
    nlinarith only [hs,hheight,abs_nonneg firstHeight,hp]
  have hh:=hbase.trans (geometry_shifted_height_product firstHeight height t0 u hheight)
  have hpow:=pow_le_pow_left₀ (by positivity : 0≤1+|nativePhysicalSourceHeight second firstHeight t0 u|+height) hh degree
  simpa only [mul_pow,mul_assoc] using hpow

/-- The actual small physical branch supplies the canonical source's
occupied-buffer height premise for either orientation. -/
theorem native_physical_small_height
    (second : Bool)(firstHeight height t0 u T : ℝ)(hT : 0≤T)
    (hsmall : 2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|))≤T) :
    |nativePhysicalSourceHeight second firstHeight t0 u|+height+T/2≤5*T :=
  main_low_payment_shifted_height_envelope second firstHeight height t0 u T hT hsmall
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_second_datum_time
#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_physical_source_height_control
