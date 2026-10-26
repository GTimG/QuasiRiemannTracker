import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedContraction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearSource CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceInputReindex CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstAmplificationChoice RayFourExpansion
open CenteredMomentHeckeColumnWindow
local instance secondDatumReindexDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Renaming original slots leaves the literal source column unchanged. -/
theorem source_column_reindex (e : α ≃ β) (s : Input α)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (z : O) :
    sourceColumn (reindex e s) C hC R seed L z = sourceColumn s C hC R seed L z := by
  unfold sourceColumn
  change (let Q := residualPool C hC.1 (original (reindex e s) R seed).columns
          let b := (original (reindex e s) R seed).beta
          rowPolynomial Finset.univ (sourceGenerator Q)
            (fun I : supportedColumns Q =>
              (if IsCoprime C (I : Ideal O) ∧ L ∣ (I : Ideal O)
               then b (C * I) else 0) * heightCoeff s.η s.t I) z) = _
  rw [columns_map, coefficient_map]
  rfl

/-- The physical volume normalization is invariant under slot equivalence. -/
theorem normalized_column_reindex (e : α ≃ β) (s : Input α)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (z : O) :
    normalizedColumn (reindex e s) C hC R seed L z =
      normalizedColumn s C hC R seed L z := by
  unfold normalizedColumn
  change (Real.sqrt (CenteredMomentAmplificationChildInput.volume (reindex e s)) : ℂ)⁻¹ *
    sourceColumn (reindex e s) C hC R seed L z = _
  rw [volume_map, source_column_reindex]
  rfl

/-- Height shifts commute with reindexing; no Mellin parameter is changed. -/
theorem normalized_column_reindex_height (e : α ≃ β) (s : Input α)
    (η : Character) (t : ℝ) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (z : O) :
    normalizedColumn (withHeight (reindex e s) η t) C hC R seed L z =
      normalizedColumn (withHeight s η t) C hC R seed L z :=
  normalized_column_reindex e (withHeight s η t) C hC R seed L z

/-- Place each varying slot subset in one fixed original ambient type. -/
def SecondInputDatum.image (e : α ↪ β) (d : SecondInputDatum α) : SecondInputDatum β where
  slots := d.slots.map e
  input := imageInput e d.slots d.input
  R := d.R
  seed := d.seed
  C := d.C
  D := d.D
  hC := d.hC
  hD := d.hD
  sameSupport := d.sameSupport
  inactive := d.inactive
  radius := d.radius
  rows := d.rows
  rows_ne := d.rows_ne
  K := d.K
  K_pos := d.K_pos
  dyad := d.dyad
  τ := d.τ
  family := d.family
  rowBudget := d.rowBudget

/-- The entire physical block is unchanged by the ambient embedding. -/
@[simp] theorem second_datum_image_block (e : α ↪ β) (d : SecondInputDatum α) :
    (d.image e).block = d.block := by
  have hc := columns_map (Finset.equivMap e d.slots) d.input d.R d.seed
  have hb := coefficient_map (Finset.equivMap e d.slots) d.input d.R d.seed
  dsimp only [CenteredMomentFirstAmplificationChoice.OriginalData.columns, original] at hc
  dsimp only [CenteredMomentFirstAmplificationChoice.OriginalData.beta,
    CenteredMomentFirstAmplificationChoice.OriginalData.profile, original] at hb
  unfold SecondInputDatum.block
  dsimp only [SecondInputDatum.image, imageInput]
  unfold originalSecondBlock
  rw [hc, hb]
  rfl

@[simp] theorem second_datum_image_volume (e : α ↪ β) (d : SecondInputDatum α) :
    CenteredMomentExceptionalAmplitudePair.volume (d.image e).input.toData =
      CenteredMomentExceptionalAmplitudePair.volume d.input.toData :=
  volume_map (Finset.equivMap e d.slots) d.input

/-- Exact columns on both original and reflected rows, at arbitrary shifted height. -/
theorem second_datum_image_column (e : α ↪ β) (d : SecondInputDatum α)
    (η : Character) (t : ℝ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (z : O) :
    normalizedColumn (withHeight (d.image e).input η t) C hC (d.image e).R (d.image e).seed L z =
      normalizedColumn (withHeight d.input η t) C hC d.R d.seed L z :=
  normalized_column_reindex_height (Finset.equivMap e d.slots) d.input η t C hC d.R d.seed L z

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
