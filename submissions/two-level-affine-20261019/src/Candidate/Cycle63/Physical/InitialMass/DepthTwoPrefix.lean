/- The child prefix of a first-level row: its dictionary row is the child multiplier times the residual frequency, the
multiplier has norm at most that of the row, and for a row of a selected first column the prefix has supported common
ideals with equal prime supports. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryNaturalDictionary
import Candidate.Cycle63.Moment.DepthTwoCount

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit IdealMobiusDivisorSum
open CenteredMomentCommonRadialData

/-- The child prefix of a second-stage row: the first-source label of its block, and the second common pair and
inactive set of the block. -/
def secondRowPrefix {Label : Type*} [Fintype Label] (s : Label → SecondBlockSource) (first : Label → FirstSourceLabel)
    (r : secondLiveRows s) : ChildPrefix :=
  ⟨first r.val.1, ((s r.val.1).C, (s r.val.1).D), (s r.val.1).inactive⟩

/-- The dictionary row of a second-stage row is the child multiplier of its prefix times its residual frequency. -/
theorem joint_row_eq_prefix_multiplier {Label : Type*} [Fintype Label] (s : Label → SecondBlockSource)
    (first : Label → FirstSourceLabel) (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O) :
    jointSourceRow left u₀ unit (secondEncodedRow s first r) =
      childMultiplier left u₀ unit (secondRowPrefix s first r)*r.val.2.2.2.val := by
  dsimp only [jointSourceRow, secondEncodedRow, childMultiplier, secondRowPrefix, effectiveRow]
  ring

/-- The child multiplier of a prefix has norm at most that of the dictionary row of the second-stage row, also after
multiplying both by any ideal. -/
theorem prefix_multiplier_norm_le {Label : Type*} [Fintype Label] (s : Label → SecondBlockSource)
    (first : Label → FirstSourceLabel) (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (hrow : jointSourceRow left u₀ unit (secondEncodedRow s first r) ≠ 0) (J : Ideal O) :
    ((Ideal.span {childMultiplier left u₀ unit (secondRowPrefix s first r)}*J).absNorm : ℝ) ≤
      ((Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow s first r)}*J).absNorm : ℝ) := by
  have hdvd : Ideal.span {childMultiplier left u₀ unit (secondRowPrefix s first r)}*J ∣
      Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow s first r)}*J := by
    apply mul_dvd_mul_right
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd, joint_row_eq_prefix_multiplier]
    exact dvd_mul_right _ _
  by_cases hJ : J = 0
  · rw [hJ, mul_zero, mul_zero]
  · have hne : Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow s first r)}*J ≠ 0 :=
      mul_ne_zero (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hrow) hJ
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hne))
      (map_dvd Ideal.absNorm hdvd)

/-- The child prefix of a row whose block belongs to a selected first column has supported common ideals at both
stages, with equal prime supports. -/
theorem geometry_row_prefix_support {ι α Label : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0 < K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (datum : Label → SecondInputDatum α) (first : Label → FirstSourceLabel)
    (r : secondLiveRows (fun l => (datum l).block))
    (hfirst : first r.val.1 = geometryFirstLabel s R seed K Z ξ hK bin j) :
    (Supported (secondRowPrefix (fun l => (datum l).block) first r).1.1.1 ∧
      (secondRowPrefix (fun l => (datum l).block) first r).1.1.2 ≠ 0 ∧
      Supported (secondRowPrefix (fun l => (datum l).block) first r).2.1.1 ∧
      (secondRowPrefix (fun l => (datum l).block) first r).2.1.2 ≠ 0) ∧
    (primeSupport (secondRowPrefix (fun l => (datum l).block) first r).1.1.1 =
        primeSupport (secondRowPrefix (fun l => (datum l).block) first r).1.1.2 ∧
      primeSupport (secondRowPrefix (fun l => (datum l).block) first r).2.1.1 =
        primeSupport (secondRowPrefix (fun l => (datum l).block) first r).2.1.2) := by
  have h₁ : (secondRowPrefix (fun l => (datum l).block) first r).1 = geometryFirstLabel s R seed K Z ξ hK bin j :=
    hfirst
  rw [h₁]
  exact ⟨⟨(geometryFirstSource s R seed K Z ξ hK bin j.1).hC, (geometryFirstSource s R seed K Z ξ hK bin j.1).hD.1,
      (datum r.val.1).hC, (datum r.val.1).hD.1⟩,
    ⟨(geometryFirstSource s R seed K Z ξ hK bin j.1).sameSupport, (datum r.val.1).sameSupport⟩⟩

end
end OAI.SevenEighths.Cycle63InitialMass
