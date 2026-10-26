/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Absolute counts for the full second residual pool and literal physical rows.
The counts do not depend on the moving Mellin integration variables. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialPhysicalResidualCap
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalNormalizedAbsolute
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAbsoluteEnergy QuadraticInitialBound ConcreteTraceCRT
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance absoluteRowsDecidable {ι : Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem lattice_rows_card (rows : Finset O) (X : ℝ) (hX : 1≤X)
    (hrows : ∀z∈rows,normValue z≤X) :
    (rows.card:ℝ)≤diagonalControl ballProfile*X := by
  have hX0:=zero_lt_one.trans_le hX
  calc
    _=∑_z∈rows,(1:ℝ):=by simp
    _≤∑z∈rows,‖ballProfile (‖eisEmbedding z‖^2/X)‖:=Finset.sum_le_sum
      (fun z hz=>(ballProfile_majorizes X hX0 z (hrows z hz)).trans (Complex.re_le_norm _))
    _≤∑'z:O,‖ballProfile (‖eisEmbedding z‖^2/X)‖:=
      (radial_norm_summable ballProfile X hX0).sum_le_tsum rows (fun _ _=>norm_nonneg _)
    _≤_:=by simpa only [max_eq_right hX] using radial_weight_lattice_bound_all ballProfile X hX0

variable {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]

theorem second_residual_card (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ)
    (r : SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))) (Y : ℝ) (hY : 0≤Y)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),(I.absNorm:ℝ)≤Y) :
    ((secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r).card:ℝ)≤128*Y := by
  have hs:secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r⊆idealBall Y := by
    intro I hI
    apply (mem_idealBall Y I).mpr
    apply InitialPhysical.modified_second_residual_full_cap d modifier r Y ?_ I hI
    intro J hJ
    apply hpool J
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hJ
    exact Finset.mem_image.mpr ⟨v,by simpa only [Fintype.mem_piFinset] using hv,he⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (idealBall_card Y hY)

/-- The fixed ray-character cardinality is paid in full, as are all original
rows. Filtering to live rows occurs only on the left-hand side. -/
theorem second_live_weighted_rows (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ) (f : Label→ℝ) (hf : ∀l,0≤f l)
    (X : ℝ) (hX : 1≤X) (hrows : ∀l,∀z∈(d l).rows,normValue z≤X) :
    (∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),f r.1)≤
      (Fintype.card RayCharacter:ℝ)^2*diagonalControl ballProfile*X*(∑l,f l) := by
  have hfull:(∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),f r.1)≤
      ∑r:SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l)),f r.1:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun r _ _=>hf r.1)
  apply hfull.trans
  rw [Fintype.sum_sigma]
  have he:(∑l:Label,∑r:RayCharacter×RayCharacter×(modifiedDatumBlock (d l) (modifier l)).rows,f l)=
      ∑l:Label,(Fintype.card RayCharacter:ℝ)^2*((d l).rows.card:ℝ)*f l := by
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,nsmul_eq_mul]
    change (Fintype.card RayCharacter:ℝ)*((Fintype.card RayCharacter:ℝ)*((d l).rows.card:ℝ))*f l=
      (Fintype.card RayCharacter:ℝ)^2*((d l).rows.card:ℝ)*f l
    ring
  rw [he]
  calc
    _≤∑l:Label,(Fintype.card RayCharacter:ℝ)^2*(diagonalControl ballProfile*X)*f l := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (lattice_rows_card (d l).rows X hX (hrows l)) (sq_nonneg _)) (hf l)
    _=_:=by rw [←Finset.mul_sum];ring
end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.lattice_rows_card
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.second_residual_card
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.second_live_weighted_rows
