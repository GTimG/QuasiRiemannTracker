/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite true-dilation decomposition of the complete original label series. -/
import Candidate.C092.transport.MixedMiddleReturnOriginal
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor CenteredMomentReflectionWeightedEnergy
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

/-- One original physical label series, restricted only by the actual cutoff
and its true max-one dilation box. -/
def originalBoxPacket (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi : ℝ) (n j : ℕ) : ℂ :=
  (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex F.S u (fun k : J=>sourcePrimePool F Z k.val),
    labelPacketCoefficient F.S F.exclusions η u (fun k : J=>sourcePrimePool F Z k.val)
      (fun k=>source_prime_pool_outside F Z k.val)
      (fun k P=>physicalSlotWeight P.val F.W (Z^(D.length k.val)) z) x z e*
      (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℂ)^(-(1/2:ℂ))*
      (if (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)≤2*Y ∧
        dilationBox U xi n (max 1 (data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)*
          (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)))=j
       then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime u) false F.W
          (Y/(labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)) 0 0 else 0)

/-- Exact reconstruction, with no coefficient, cutoff or dilation tail. -/
theorem original_packet_boxes (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi : ℝ) (n : ℕ) (hY : 0<Y)
    (hrow : (rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+4*D.e≤x.re+1/2) :
    errorPacket D F J η u Z x z Y=
      ∑j∈Finset.range (n+1),originalBoxPacket D F J η u Z x z data Y U xi n j := by
  classical
  let T := fun k : J=>sourcePrimePool F Z k.val
  let A := labelPacketCoefficient F.S F.exclusions η u T
    (fun k=>source_prime_pool_outside F Z k.val)
    (fun k P=>physicalSlotWeight P.val F.W (Z^(D.length k.val)) z) x z
  let N := fun e : LabelPacketIndex F.S u T=>(labelPacketScale F.S u T e:ℝ)
  let L := data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)
  let P := fun e : LabelPacketIndex F.S u T=>HeckeDyadic.polynomial
    (rowCharacter F.S F.exclusions.prime u) false F.W (Y/N e) 0 0
  let t := fun e=>max 1 (L*N e)
  let f := fun e=>A e*(N e:ℂ)^(-(1/2:ℂ))*P e
  have hs : Summable (fun e=>‖f e‖) := actual_label_series_norm_summable F.S F.exclusions
    (4*D.e) F.first η u hrow T (fun k=>source_prime_pool_outside F Z k.val) _ x z hx hz
    hmargin F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤) Y hY
  have he (j : ℕ) (e : LabelPacketIndex F.S u T) :
      boxSeriesTerm U xi n j t f e=A e*(N e:ℂ)^(-(1/2:ℂ))*
        (if N e≤2*Y ∧ dilationBox U xi n (t e)=j then P e else 0) := by
    by_cases hcut : N e≤2*Y
    · by_cases hj : dilationBox U xi n (t e)=j <;> simp [boxSeriesTerm,hcut,hj,f]
    · have hzero : f e=0 := actual_label_term_zero_of_cutoff F.S F.exclusions η u T
        (fun k=>source_prime_pool_outside F Z k.val) _ x z F.W 1 2 Y hY F.complex_support e
        (lt_of_not_ge hcut)
      simp [boxSeriesTerm,hcut,hzero]
  have hh := tsum_box_decomposition U xi n t f hs
  unfold errorPacket labelPolynomialPacket originalBoxPacket
  rw [←Finset.mul_sum]
  congr 1
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j hj
  apply tsum_congr
  intro e
  exact (he j e).symm

#print axioms original_packet_boxes
end
end QRH.Cycle092.MixedMiddleReturn
