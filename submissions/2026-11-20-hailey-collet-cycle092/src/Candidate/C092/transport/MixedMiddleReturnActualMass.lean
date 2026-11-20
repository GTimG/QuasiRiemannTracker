/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The complete original P15 mass, with its prime damping outside Cauchy. -/
import Candidate.C092.transport.MixedMiddleReturnSaturated
import Candidate.C092.transport.SelectedNonfloorMass
import Candidate.C092.transport.SelectedFloorEstimateHeight

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Cycle092.SelectedNonfloor
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
local notation "O" => HeckeFamily.O
variable [Geometry.Parameters]

/-- No coefficient-mass assumption: P15 supplies the full countable original
label tuple, uniformly over the live finite family. Its favorable prime
factor stays in the mass, and is therefore linear after packet Cauchy. -/
theorem original_packet_mass (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (massEps : ℝ) (he : 0 < massEps) :
    ∃ C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      (∀j : Fin D.N,(sourcePrimePool F Z j).Nonempty) ∧
      ∀(U : ℝ) (rows : Finset FreeRow)
        (data : ∀u : rows,PhysicalReflectionData F.S F.exclusions.prime u.val)
        (a : ℝ) (x z : ℂ),
        0 < U → (∀u∈rows,rowNorm u≤U) → 51/100≤a → a≤7/8 →
        x.re=a+16*D.e → z.re=17/50 →
      let Mass := C*U^massEps*(∏j : J,(Z^(D.length j.val))^(-(4/25:ℝ)))
      0 < Mass ∧ ∀u : rows,
        Summable (massTerm D F J η u.val Z x z (data u) ((2*a-1)/2)) ∧
        (∑'e,massTerm D F J η u.val Z x z (data u) ((2*a-1)/2) e)≤Mass := by
  obtain ⟨C,hC,hm⟩ := actual_packet_mass D F J massEps he
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hm η,SelectedFloorEstimate.source_pools_nonempty D F,
    eventually_gt_atTop (0:ℝ)] with Z hm hpool hZ
  refine ⟨hpool,?_⟩
  intro U rows data a x z hU hrow ha ha' hx hz
  dsimp only
  have hprod : 0 < (∏j : J,(Z^(D.length j.val))^(-(4/25:ℝ))) := by
    apply Finset.prod_pos
    intro j _
    exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZ _) _
  refine ⟨by positivity,?_⟩
  intro u
  have hh := hm u.val (data u) a x z ha ha' hx hz
  have hpow := Real.rpow_le_rpow (zero_le_one.trans (rowNorm_ge_one u.val)) (hrow u.val u.property) he.le
  have hmass := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hprod.le
  constructor
  · convert hh.1 using 1 <;> congr 2 <;> ring
  · convert hh.2.trans hmass using 1 <;> congr 2 <;> ring

#print axioms original_packet_mass
end
end QRH.Cycle092.MixedMiddleReturn
