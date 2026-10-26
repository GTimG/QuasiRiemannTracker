import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionAnnular
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.RawSixthDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily HeckePrimeAnnular
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- The maximum-with-one convention makes comparison stable even when a
slot falls below the amplitude threshold after deleting primes. -/
theorem max_slot_product_comparison {ι : Type*} (S : Finset ι) (Q Q₀ : ι → ℂ)
    (hclose : ∀i∈S,‖Q i-Q₀ i‖≤1/2) :
    (∏i∈S,max 1 ‖Q i‖)^2 ≤ (4:ℝ)^S.card*(∏i∈S,max 1 ‖Q₀ i‖)^2 := by
  have hp : (∏i∈S,max 1 ‖Q i‖) ≤ (2:ℝ)^S.card*(∏i∈S,max 1 ‖Q₀ i‖) := by
    calc
      _ ≤ ∏i∈S,2*max 1 ‖Q₀ i‖ := Finset.prod_le_prod₀
        (fun i _=>(zero_le_one.trans (le_max_left _ _)))
        (fun i hi=>max_amplitude_of_deletion_error (hclose i hi))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]
  have hpow := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _))) hp 2
  rw [mul_pow,←pow_mul] at hpow
  have he : ((2:ℝ)^S.card)^2=(4:ℝ)^S.card := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [←pow_mul] at he
  rwa [he] at hpow

end
end OAI.SevenEighths.Deletion26

end Record1252270103Bootstrap.PR67
