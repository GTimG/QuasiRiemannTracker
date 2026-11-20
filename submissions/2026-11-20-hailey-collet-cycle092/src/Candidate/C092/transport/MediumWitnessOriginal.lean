/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original source-cube same-zero witnesses on the actual measured medium rows.
The supplied cutoff is fixed as r0+m0 before selecting either witness. -/
import Candidate.C092.transport.MediumWitnessRows

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorSupportedWitness
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

def originalFamily (D : BaselineData) (F : BaselineSourceData D) (η : Character) (u : FreeRow) :=
  sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u)

lemma witness_zero_height_from_budget (D : BaselineData) {τ : ℝ}
    (hh : 4*τ < (1/200 : ℝ)*D.cost) : τ < (1/200 : ℝ)/2 := by
  have hc : D.cost ≤ 1 := by
    have hb := D.detector_budget
    have he := D.e_pos
    have hk := D.witnessKappa_pos
    have hε := D.epsilon_small
    linarith
  nlinarith

/-- The original supplier now has its full genuine common band. In particular,
nonfloor/lower-a and both detector bounds are conclusions, not analytic inputs.
The actual cutoff r0+m0 is chosen after the common eventual threshold but before
any attaining zero or dyadic pair is selected. -/
theorem original_medium_witnesses (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) :
    ∃ n : ℕ,0 < n ∧ ∀ η : Character,∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∃ idx grid : FreeRow → ℕ,ProbeAssembly.selected D F padding τ n η Z idx grid ∧
      ∀ (d threshold : ℝ),(1/200 : ℝ) ≤ d → d ≤ 7/8 → 1/50 < threshold →
      ∀ z : FreeRow → Fin D.N → ℂ,(∀ u j,(z u j).re=17/50) →
      (∀ u j,|(z u j).im| ≤ (3*idx u+1 : ℕ)*Z^τ) →
      ∀ i k : ℕ,
      let rows := mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid z i k
      rows.Nonempty →
      CommonBand D F η (Z^(Geometry.h+padding)) Z τ d threshold n idx grid z i k ∧
      ∀ r0 m0 : ℝ,1 ≤ r0+m0 → r0+m0 ≤ 3/2 →
      Nonempty (∀ u : rows,SupportedWitness (originalFamily D F η u.val) (Z^d) (bandLower D k)
        D.ε (r0+m0) (Z^τ) ((Z^d)^(τ/(2*(7/8 : ℝ)))) i) := by
  obtain ⟨n,hn,hselect⟩ := SelectedActual.buffered_selection D F padding τ hτ
  refine ⟨n,hn,?_⟩
  intro η
  have hband := actual_common_band D F P τ n hτ hheight
  have hw := supported_witnesses_from_source_cube F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t n
    (by norm_num) (by norm_num) hτ (witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos D.detector_budget
  filter_upwards [hselect,hband,hw] with Z hselect hband hw
  obtain ⟨idx,grid,hsel⟩ := hselect η
  refine ⟨hband.1,idx,grid,hsel,?_⟩
  intro d threshold hd hd' hthreshold z hz hzim i k
  dsimp only
  intro hne
  have hb := hband.2 d padding (Z^(Geometry.h+padding)) threshold hd hd' hthreshold
    η idx grid hsel z hz hzim i k hne
  refine ⟨hb,?_⟩
  intro r0 m0 ht ht'
  exact hw d hd hd' (Z^(Geometry.h+padding))
    (mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid z i k)
    hb.rows_band hb.calibration hb.conductor (bandLower D k) i hb.index_bound hb.nonfloor
    (hb.a_upper.trans (by norm_num))
    (fun u => hb.next u.val u.property) (fun u => hb.current u.val u.property) (r0+m0) ht ht'

/-- Both spikes retain this one actual label, zero and frequency. The length
collars are the original supplied constants, not newly imposed constraints. -/
theorem same_zero_lengths {Label : Type*} {χ : Label → Character}
    {U a ε r0 m0 T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε (r0+m0) T allowance i) :
    w.r ≤ r0+m0+ε ∧ r0+m0-w.r-ε ≤ w.m ∧ 0 ≤ w.m ∧ w.m ≤ 1/2+75*ε ∧
      (w.r < r0 → m0-ε ≤ w.m) := by
  refine ⟨w.inverse_length_upper,w.product_length_lower,w.plain_length_lower,w.plain_length_upper,?_⟩
  intro hr
  have h := w.product_length_lower
  linarith

end QRH.Cycle092.MediumWitness
