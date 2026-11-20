/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original small-label packet, retaining its strict old dilation cutoff. -/
import Candidate.C092.transport.MixedMiddleReturnDecomposition
import Candidate.C092.transport.MixedTicketTailsLargeSplit
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

/-- Every complete original coefficient remains in this series. The only
restrictions are the original polynomial cutoff, strict OLD small dilation
cutoff, and true dilation box. -/
def originalSmallBoxPacket (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi vcut : ℝ) (n j : ℕ) : ℂ :=
  (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex F.S u (fun k : J=>sourcePrimePool F Z k.val),
    labelPacketCoefficient F.S F.exclusions η u (fun k : J=>sourcePrimePool F Z k.val)
      (fun k=>source_prime_pool_outside F Z k.val)
      (fun k P=>physicalSlotWeight P.val F.W (Z^(D.length k.val)) z) x z e*
      (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℂ)^(-(1/2:ℂ))*
      (if (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)≤2*Y ∧
        max 1 (data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)*
          (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ))<U^vcut ∧
        dilationBox U xi n (max 1 (data.combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm u)*
          (labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)))=j
       then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime u) false F.W
          (Y/(labelPacketScale F.S u (fun k : J=>sourcePrimePool F Z k.val) e:ℝ)) 0 0 else 0)

/-- Exact finite reconstruction of the original SMALL label packet. Its
strict cutoff is unchanged, and absolute convergence follows from the full
original coefficient series before either cutoff or box is selected. -/
theorem small_packet_boxes (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u)
    (Y U xi vcut : ℝ) (n : ℕ) (hY : 0<Y)
    (hrow : (rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+4*D.e≤x.re+1/2) :
    MixedTicketTails.smallLabelPolynomialPacket F.S F.exclusions η u
      (fun k : J=>sourcePrimePool F Z k.val) (fun k=>source_prime_pool_outside F Z k.val)
      (fun _=>F.W) (fun k=>Z^(D.length k.val)) x z F.W Y data.combinedConductor
      (fixedConductorConstant F.S) U vcut=
      ∑j∈Finset.range (n+1),originalSmallBoxPacket D F J η u Z x z data Y U xi vcut n j := by
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
  let full := fun e=>A e*(N e:ℂ)^(-(1/2:ℂ))*P e
  let f := fun e=>A e*(N e:ℂ)^(-(1/2:ℂ))*(if U^vcut≤t e then 0 else P e)
  have hsFull : Summable (fun e=>‖full e‖) := actual_label_series_norm_summable F.S F.exclusions
    (4*D.e) F.first η u hrow T (fun k=>source_prime_pool_outside F Z k.val) _ x z hx hz
    hmargin F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤) Y hY
  have hs : Summable (fun e=>‖f e‖) := by
    apply hsFull.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro e
    dsimp only [f]
    split_ifs
    · simp only [mul_zero,norm_zero];exact norm_nonneg _
    · exact le_rfl
  have he (j : ℕ) (e : LabelPacketIndex F.S u T) :
      boxSeriesTerm U xi n j t f e=A e*(N e:ℂ)^(-(1/2:ℂ))*
        (if N e≤2*Y ∧ t e<U^vcut ∧ dilationBox U xi n (t e)=j then P e else 0) := by
    have hzero (hcut : ¬N e≤2*Y) : full e=0 := actual_label_term_zero_of_cutoff F.S F.exclusions η u T
      (fun k=>source_prime_pool_outside F Z k.val) _ x z F.W 1 2 Y hY F.complex_support e
      (lt_of_not_ge hcut)
    by_cases hsmall : U^vcut≤t e
    · simp [boxSeriesTerm,f,hsmall,not_lt_of_ge hsmall]
    · have hlt : t e<U^vcut := lt_of_not_ge hsmall
      by_cases hcut : N e≤2*Y
      · by_cases hj : dilationBox U xi n (t e)=j <;> simp [boxSeriesTerm,f,hsmall,hlt,hcut,hj]
      · have hz0 := hzero hcut
        change A e*(N e:ℂ)^(-(1/2:ℂ))*P e=0 at hz0
        simp only [boxSeriesTerm,hcut,false_and,ite_false,mul_zero]
        split_ifs
        · simpa only [f,hsmall,ite_false] using hz0
        · rfl
  have hh := tsum_box_decomposition U xi n t f hs
  unfold MixedTicketTails.smallLabelPolynomialPacket originalSmallBoxPacket
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j hj
  apply tsum_congr
  intro e
  exact (he j e).symm

/-- Strict OLD small dilation also gives the actual retained box endpoint.
Only vcut is used to size the finite bank; no full-Y cutoff is substituted. -/
theorem small_true_box_bounds {U xi vcut t : ℝ} {n j : ℕ}
    (hU : 1<U) (hxi : 0 ≤ xi) (hcover : vcut ≤ (n:ℝ)*xi)
    (ht : 1 ≤ t) (hsmall : t<U^vcut) (hbox : dilationBox U xi n t=j) :
    U^((j:ℝ)*xi) ≤ t ∧ t ≤ U^(((j:ℝ)+1)*xi) ∧ (j:ℝ)*xi<vcut := by
  have hupper : t ≤ U^((n:ℝ)*xi) := hsmall.le.trans
    (Real.rpow_le_rpow_of_exponent_le hU.le hcover)
  have hh := dilationBox_spec U xi hU.le hxi n t ht hupper
  rw [hbox] at hh
  exact ⟨hh.1,hh.2,(Real.rpow_lt_rpow_left_iff hU).mp (hh.1.trans_lt hsmall)⟩

#print axioms small_packet_boxes
#print axioms small_true_box_bounds
end
end QRH.Cycle092.MixedMiddleReturn
