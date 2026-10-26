/- Coarse bounds derived from literal native source gates. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativePaidPathNode
import Candidate.Cycle63.Physical.InitialMass.SecondHighBox

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstScale CenteredMomentSectorLocalization Cycle63HighGeometry

namespace NativePaidPathNode
variable {Z : ℝ} (p : NativePaidPathNode Z)

/-- Primitive actual source gates, obtained at the same first/second
labels, width, bin and schedule as the live physical source. The first
cap3 and own-second cap130 are source caps, independent of returned counts. -/
structure SourceGates : Prop where
  unit_le_one : p.unit≤1
  row_nonneg : 0≤p.rowWidth
  row_le_one : p.rowWidth≤1
  length_nonneg : 0≤p.length
  length_le_four : p.length≤4
  amp_nonneg : 0≤p.amp
  amp_le_one : p.amp≤1
  loss_nonneg : 0≤frequencyLoss (Z^p.unit) 32 p.xi+p.reserve
  loss_le_quarter : frequencyLoss (Z^p.unit) 32 p.xi+p.reserve≤1/4
  eps_nonneg : 0≤p.eps
  eps_le_quarter : p.eps≤1/4
  side_le_quarter : p.sideError≤1/4
  first_cap : (p.first.1.1.absNorm:ℝ)≤(Z^p.unit)^(3:ℝ) ∧
    (p.first.1.2.absNorm:ℝ)≤(Z^p.unit)^(3:ℝ)
  own_second_cap : ((if p.second then p.D else p.C).absNorm:ℝ)≤(Z^p.unit)^(130:ℝ)

/-- Actual uniform schedule at the SAME live source. These primitive
small errors survive whole-source choice and do not assert final payment. -/
structure FineSourceGates : Prop where
  loss_le : frequencyLoss (Z^p.unit) 32 p.xi+p.reserve≤1/1000000000000000
  eps_le : p.eps≤1/1000000000000000
  side_le : p.sideError≤1/1000000000000000

/-- Arithmetic output of the native source gates. These are not bounds
on a forest's cardinality, weight or energy. -/
structure CoarseSource : Prop where
  scale_nonneg : 0≤p.scale
  scale_le_one : p.scale≤1
  length_le_four : p.volumeLength≤4
  amp_le_four : p.amplification≤4
  small_le_one : p.small (3/4)≤1
  missing_nonneg : 0≤p.coordinate 1
  frequency_lower : -(149:ℝ)≤p.coordinate 2
  volume_lower : -(149:ℝ)≤p.coordinate 3
  common_nonneg : 0≤p.commonLog

/-- Derive the coarse source envelope from the actual source norms and
small-error schedule. In particular the lower coordinate bounds do not
come from an assumed count or row multiplicity. -/
theorem SourceGates.coarse (h : p.SourceGates) : p.CoarseSource := by
  have hc:=ideal_log_box p.first.1.1 p.firstC.1 (Z^p.unit) 3 p.local_base h.first_cap.1
  have hd:=ideal_log_box p.first.1.2 p.firstD.1 (Z^p.unit) 3 p.local_base h.first_cap.2
  have hown : Supported (if p.second then p.D else p.C) := by
    cases p.second
    · exact p.hC
    · exact p.hD
  have hb:=ideal_log_box _ hown.1 (Z^p.unit) 130 p.local_base h.own_second_cap
  have hcf : 0≤Real.logb (Z^p.unit)
      ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ) ∧
      Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)≤3 := by
    cases p.reflected <;> assumption
  have hdf : 0≤Real.logb (Z^p.unit)
      ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ) ∧
      Real.logb (Z^p.unit) ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ)≤3 := by
    cases p.reflected <;> assumption
  obtain ⟨_,_,_,hpc,_,hRp,_⟩:=actual_first_gates (!p.reflected) p.first p.firstC p.firstD
    (Z^p.unit) p.local_base
  have hR : Real.logb (Z^p.unit)
      ((Ideal.span {activeConductor p.first.1.1 p.first.1.2}).absNorm:ℝ)≤3 := by
    linarith only [hpc,hRp,hc.2]
  have hnum : 0≤Real.logb (Z^p.unit)
      ((Ideal.span {firstSourceNumerator (!p.reflected) p.first}).absNorm:ℝ) := by
    apply Real.logb_nonneg p.local_base
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (first_source_numerator_ne_zero _ _ p.firstC))))
  have hmax : max
      (Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
       Real.logb (Z^p.unit) ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ)) 0≤3 :=
    max_le (by linarith only [hcf.2,hdf.1]) (by norm_num)
  have hfreq : -(13:ℝ)≤actualHighCoordinates p.reflected (!p.reflected) p.second p.first p.C p.D
      p.inactive (Z^p.unit) p.rowWidth p.length p.amp p.xi p.reserve p.eps 2 := by
    change -(13:ℝ)≤p.rowWidth-
      Real.logb (Z^p.unit) ((Ideal.span {activeConductor p.first.1.1 p.first.1.2}).absNorm:ℝ)-
      max (Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
        Real.logb (Z^p.unit) ((if p.reflected then p.first.1.1 else p.first.1.2).absNorm:ℝ)) 0+
      Real.logb (Z^p.unit) ((Ideal.span {firstSourceNumerator (!p.reflected) p.first}).absNorm:ℝ)-
      6*p.amp-(frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)+p.eps
    linarith only [h.row_nonneg,hR,hmax,hnum,h.amp_le_one,h.loss_le_quarter,h.eps_nonneg]
  have hvol : -(133:ℝ)≤actualHighCoordinates p.reflected (!p.reflected) p.second p.first p.C p.D
      p.inactive (Z^p.unit) p.rowWidth p.length p.amp p.xi p.reserve p.eps 3 := by
    change -(133:ℝ)≤p.length-
      Real.logb (Z^p.unit) ((if p.reflected then p.first.1.2 else p.first.1.1).absNorm:ℝ)-
      Real.logb (Z^p.unit) ((if p.second then p.D else p.C).absNorm:ℝ)
    linarith only [h.length_nonneg,hcf.2,hb.2]
  have hs : p.sideError+(1-LocalMoment.unmarkedDensity (3/4))*(frequencyLoss (Z^p.unit) 32 p.xi+p.reserve)+
      LocalMoment.unmarkedDensity (3/4)*p.eps≤1 := by
    norm_num [LocalMoment.unmarkedDensity]
    linarith only [h.side_le_quarter,h.loss_le_quarter,h.eps_le_quarter]
  have hmissing : 0≤Real.logb (Z^p.unit) ((firstSourceMissing (!p.reflected) p.first).absNorm:ℝ) := by
    apply Real.logb_nonneg p.local_base
    exact_mod_cast (first_missing_norm_le _ _ p.firstC p.firstD).1
  refine {
    scale_nonneg:=mul_nonneg p.unit_pos.le h.row_nonneg
    scale_le_one:=?_
    length_le_four:=?_
    amp_le_four:=?_
    small_le_one:=?_
    missing_nonneg:=mul_nonneg p.unit_pos.le hmissing
    frequency_lower:=?_
    volume_lower:=?_
    common_nonneg:=mul_nonneg p.unit_pos.le (add_nonneg hcf.1 hb.1) }
  · dsimp only [scale]
    nlinarith only [h.row_le_one,h.unit_le_one,p.unit_pos]
  · dsimp only [volumeLength]
    nlinarith only [h.length_le_four,h.unit_le_one,p.unit_pos]
  · dsimp only [amplification]
    nlinarith only [h.amp_le_one,h.unit_le_one,p.unit_pos]
  · dsimp only [small]
    have hm:=mul_le_mul_of_nonneg_left hs p.unit_pos.le
    linarith only [hm,h.unit_le_one]
  · dsimp only [coordinate]
    have hm:=mul_le_mul_of_nonneg_left hfreq p.unit_pos.le
    nlinarith only [hm,h.unit_le_one]
  · dsimp only [coordinate]
    have hm:=mul_le_mul_of_nonneg_left hvol p.unit_pos.le
    nlinarith only [hm,h.unit_le_one]

theorem CoarseSource.raw_edge_exponent (h : p.CoarseSource) (remainingFee : ℝ)
    (hfee : remainingFee≤2) : p.scale+p.shiftedOutside+remainingFee≤204 := by
  have hq : Cycle63.Arithmetic.q0≤3/4 := by have hq:=Cycle63.Arithmetic.q0_bounds.2;linarith only [hq]
  have hx:=p.shiftedOutside_coarse hq h.scale_nonneg h.length_le_four h.amp_le_four h.small_le_one
    h.missing_nonneg h.frequency_lower h.volume_lower h.common_nonneg
  linarith only [h.scale_le_one,hx,hfee]

end NativePaidPathNode
end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.NativePaidPathNode.SourceGates.coarse
