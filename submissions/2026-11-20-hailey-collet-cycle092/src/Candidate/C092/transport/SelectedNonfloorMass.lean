/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual P15 mass, using Levy's complete label coefficient theorem and the
retained original primitive reflection data. Inherited credits are in imports. -/
import Candidate.C092.transport.SelectedNonfloorFront

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor Cycle25.Weighted.Numerator Cycle25.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

/-- Full P15 mass at the actual marked prime pools. The scale is the original
entire error tuple and its own primitive combined conductor. -/
def massTerm (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (η : Character) (u : FreeRow) (Z : ℝ) (x z : ℂ)
    (data : PhysicalReflectionData F.S F.exclusions.prime u) (rho : ℝ)
    (e : LabelPacketIndex F.S u (fun j : J => sourcePrimePool F Z j.val)) : ℝ :=
  let T := fun j : J => sourcePrimePool F Z j.val
  let weight : ∀ j, T j → ℂ := fun j P => physicalSlotWeight P.val F.W (Z^(D.length j.val)) z
  let N : ℝ := labelPacketScale F.S u T e
  let L : ℝ := data.combinedConductor/((fixedConductorConstant F.S : ℝ)*rowNorm u)
  ‖labelPacketCoefficient F.S F.exclusions η u T
    (fun j => source_prime_pool_outside F Z j.val) weight x z e‖ * N^(-(1/2:ℝ)) * max 1 (L*N)^rho

/-- Every physical error coefficient and reciprocal weight is summed before
any amplitude division. The same statement covers empty and full error masks.
There is no `errorProductSize` premise and no discarded coefficient tail. -/
theorem actual_packet_mass (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (massEps : ℝ) (hmassEps : 0 < massEps) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ (u : FreeRow) (data : PhysicalReflectionData F.S F.exclusions.prime u)
        (alpha : ℝ) (x z : ℂ),
      51/100 ≤ alpha → alpha ≤ 7/8 → x.re = alpha+16*D.e → z.re = 17/50 →
      Summable (massTerm D F J η u Z x z data (alpha-1/2)) ∧
      (∑' e, massTerm D F J η u Z x z data (alpha-1/2) e) ≤
        C*(rowNorm u)^massEps*(∏ j : J, (Z^(D.length j.val))^(-(4/25:ℝ))) := by
  obtain ⟨C, hC, hm⟩ := actual_physical_label_mass (ι:=J) massEps 1 2 1 hmassEps
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro η
  filter_upwards [source_prime_reconstruction_geometry F η, eventually_ge_atTop (1:ℝ)] with Z hg hZ
  intro u data alpha x z ha hatop hx hz
  have he := D.e_pos
  have he' := D.e_small
  have hW (y : ℝ) : ‖F.W y‖ ≤ 1 := by
    rw [F.complex_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.bounded y).1]
    exact (F.bounded y).2
  have hCcond : 0 < (fixedConductorConstant F.S : ℝ) := by
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hh := hm F.S F.exclusions (4*D.e) F.first η u
    (fun j : J => sourcePrimePool F Z j.val) (fun j => source_prime_pool_outside F Z j.val)
    (hg.2.1 J) (fun j => hg.2.2.2.1 j.val) (fun _ => F.W)
    (fun j => Z^(D.length j.val))
    (fun j => Real.one_le_rpow hZ (D.slots_pos j.val).le)
    (fun _ => F.complex_support) (fun _ => hW) x z alpha D.e (alpha-1/2)
    (fixedConductorConstant F.S) data.combinedConductor ha (by linarith) he he'.le hx hz
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    hCcond data.combined_pos.le data.combined_le_radical
  exact hh

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.actual_packet_mass
