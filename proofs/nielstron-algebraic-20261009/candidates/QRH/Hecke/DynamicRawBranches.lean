import QRH.NumericFacts
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import QRH.Geometry
/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Dynamic plain capacity with actual inverse/plain detector witnesses and physical coefficients. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorPlainFiberCount HeckeDetectorNoSlotPlainCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.plain_marked_count_optimized (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F (Δ+(QRH.kappa0-3/4)/2) c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hΔ : 0≤Δ) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*(QRH.kappa0+2*Δ)*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm)  := by
  have hk0 := QRH.NumericFacts.kappa_lower
  have heq : (3/4:ℝ)+2*(Δ+(QRH.kappa0-3/4)/2)=QRH.kappa0+2*Δ := by ring

  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z (QRH.kappa0+2*Δ) εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin (by linarith) hC hh hf hcap (by simpa only [heq, Fiber.m, Fiber.physicalProduct] using moments.plain_marked)

end SevenEighths.HeckeDetectorRawFiber
end
end OAI
