/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.Transport.ProbeDefinition
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.Transport.PrincipalRemainderNormalized
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.Transport.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction

set_option autoImplicit false

namespace OAI
noncomputable section
variable [QRH.RH20261023Return.Geometry.Parameters] [QRH.RH20261023Return.Geometry.Bounds]
open scoped Classical BigOperators
namespace SevenEighths.RH20261023Return.TransportHighTransport
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeRaySlots CompletedGauss CanonicalQuadraticSieve
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem principal_shift_is_common :
    RH20261023Return.Transport.Transport.PrincipalSignal.signalShift = RH20261023Return.Transport.Assembly.signalShift :=
  RH20261023Return.Transport.Transport.signalShift_eq

/-- The exact principal, finite central, and tail partition of the shared
normalized probe at the new physical lengths. -/
theorem normalizedProbe_partition {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (slotEll : Fin K→ℝ) (a b ζ Z : ℝ)
    (hζ : 0 ≤ ζ) (hZ : 1 ≤ Z) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (η : Character) :
    let Yp := fun j=>Z^(slotEll j)
    let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
    let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
    let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z RH20261023Return.Transport.Arithmetic.ell
        (slotMass T (residueWeights W Yp)) : ℂ)
    RH20261023TransportLow.normalizedProbe M H S hmax slotEll a b W W0 W1 η Z =
      principalPhysicalPool η S T WC Yp W0 W1
        (Z^RH20261023Return.Transport.Arithmetic.x) (Z^RH20261023Return.Transport.Arithmetic.y) Z/normer +
      ((∑n∈smallDyadicIndices (Z^(1/100:ℝ)),
          finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n) T WC Yp W0 W1
            (Z^RH20261023Return.Transport.Arithmetic.x) (Z^RH20261023Return.Transport.Arithmetic.y) Z)+
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^(RH20261023Return.Transport.Arithmetic.h+ζ)))
          T WC Yp W0 W1 (Z^RH20261023Return.Transport.Arithmetic.x) (Z^RH20261023Return.Transport.Arithmetic.y) Z+
        (∑'n : ℕ, finitePhysicalRows S hmax η (dyadicRows (Z^(RH20261023Return.Transport.Arithmetic.h+ζ)) n)
          T WC Yp W0 W1 (Z^RH20261023Return.Transport.Arithmetic.x) (Z^RH20261023Return.Transport.Arithmetic.y) Z))/normer := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hT : ∀i P,P∈T i → Supported P.val := by
    intro i P hP
    exact outside_prime_supported S hS.bad P ((mem_pool _ S a b (Yp i) P).mp hP).2.2.2
  have hp := canonical_physical_probe_partition S hS hmax η T hT WC Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z^RH20261023Return.Transport.Arithmetic.x) (Z^RH20261023Return.Transport.Arithmetic.y) Z
    (Z^(1/100:ℝ)) (Z^(RH20261023Return.Transport.Arithmetic.h+ζ))
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num))
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [RH20261023Return.Transport.Transport.h_interval.1]))
  dsimp only
  change _ = principalPhysicalPool η S T WC Yp W0 W1 _ _ _ / _ + _
  unfold RH20261023TransportLow.normalizedProbe
  dsimp only
  rw [hp]
  exact add_div _ _ _

#print axioms normalizedProbe_partition
end SevenEighths.RH20261023Return.TransportHighTransport
end
end OAI

#print axioms OAI.SevenEighths.RH20261023Return.TransportHighTransport.principal_shift_is_common
#print axioms OAI.SevenEighths.RH20261023Return.TransportHighTransport.normalizedProbe_partition
