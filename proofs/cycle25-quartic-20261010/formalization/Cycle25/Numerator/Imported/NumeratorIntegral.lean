import Cycle25.Numerator.Imported.NumeratorPacketMellin

/-! The actual complete-w error numerator, bounded after reconstructing its
Dirichlet polynomial.  No pointwise bound on L along the central line is used. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def errorNumeratorIntegral (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
    (Y : ℂ)^(((1 / 2 : ℂ) + t * I) - 1) * mellin W ((1 / 2 : ℂ) + t * I) *
    HeckeOrigin.continued (rowCharacter S hS.prime u) ((1 / 2 : ℂ) + t * I) *
    ((∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x ((1 / 2 : ℂ) + t * I) z) *
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T)
        η u x ((1 / 2 : ℂ) + t * I) z))

theorem actual_error_numerator_bound (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho L : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho))
    (hL : 0 ≤ L) (hcap : L * errorProductDeficit u T ≤ 1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y M : ℝ) (hY : 0 < Y) (hM : 0 ≤ M)
    (hpoly : ∀ N : ℝ, 1 ≤ N → N ≤ b * Y →
      ‖HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W (Y / N) 0 0‖ ≤
        M * max 1 (L * N)^rho) :
    ‖errorNumeratorIntegral S hS η u T hT x z W Y‖ ≤
      Y^(-(1 / 2 : ℝ)) * (M * (2 *
        (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2) * errorProductSize u T))) := by
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  have hmarginc : 1 + firsteps ≤ x.re + 1 / 2 := by linarith
  have he := actual_error_packet_mellin S hS firsteps hfirst η u hrow T hT hη x z hQ
    hx' hz.ge hmarginc W a b ha hsupp hW Y hY
  change ‖_‖ ≤ _
  rw [show errorNumeratorIntegral S hS η u T hT x z W Y = _ from he]
  obtain ⟨hmass,hmb⟩ := error_packet_damped_mass S hS firsteps hfirst η u T hT hη x z
    alpha eps rho L hQ halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hL hcap
  apply reconstructed_numerator_bound (rowCharacter S hS.prime u) W a b Y L rho M _
    hsupp hY hM (errorPacketCoefficient S hS η u T hT x z)
    (fun e => (errorPacketScale S u T e : ℝ))
    (fun e => lt_of_lt_of_le zero_lt_one (by exact_mod_cast errorPacketScale_one_le S u T e)) hmass hmb
  intro e hecut
  exact hpoly _ (by exact_mod_cast errorPacketScale_one_le S u T e) hecut

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
