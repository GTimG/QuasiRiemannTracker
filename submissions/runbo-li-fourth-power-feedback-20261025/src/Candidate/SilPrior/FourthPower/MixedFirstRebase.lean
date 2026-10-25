/- Copyright (c) 2026 Sil. Apache-2.0.
Exact removal of original ordinary prefixes by changing ordinary scales.
All tuple restrictions and raw coefficients are preserved. This module
does not select a reference or assert any prefix-independent estimate.

-/
import Candidate.SilPrior.FourthPower.MixedInnerExceptionalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Extraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstRebase
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRectangle CenteredMomentExtraction CenteredMomentLattice
open CenteredMomentOriginalRadialComparison
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open MixedPrincipalPair MixedPrincipalCentered MixedPrincipalAllocations MixedPrincipalWindow
open MixedInnerExceptionalBlock MixedCompletedRows MixedLiteralAllocation
open MixedCommonCoefficient MixedCommonRestriction MixedHeightEnergy MixedLiveNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Only original ordinary prefixes are absorbed. Genuine allocation B/G,
all fixed punctures, and every coefficient/profile remain literally fixed. -/
def rebase (s : Source ι a b) : Source ι a b where
  S := s.S
  H := s.H
  pool := s.pool
  d := (1,1)
  hd := ⟨one_ne_zero,one_ne_zero⟩
  B := s.B
  hB := s.hB
  G := s.G
  R := s.R
  Fhole := s.Fhole
  hprod := s.hprod
  hR := s.hR
  hFhole := s.hFhole
  ν := s.ν
  Wslot := s.Wslot
  P := s.P
  M := s.M
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁/s.d.1.absNorm
  X₂ := s.X₂/s.d.2.absNorm
  Y₁ := s.Y₁/s.d.1.absNorm
  Y₂ := s.Y₂/s.d.2.absNorm
  U₁ := s.U₁/s.d.1.absNorm
  U₂ := s.U₂/s.d.2.absNorm
  T := s.T/pairNorm s.d
  L := s.L/prefixNormMax s.d
  hL := div_pos s.hL (prefixNormMax_pos s.d s.hd)
  hX₁ := shortened_lower_left s.d s.hd s.L s.X₁ s.hL.le s.hX₁
  hX₂ := shortened_lower_right s.d s.hd s.L s.X₂ s.hL.le s.hX₂
  hY₁ := shortened_lower_left s.d s.hd s.L s.Y₁ s.hL.le s.hY₁
  hY₂ := shortened_lower_right s.d s.hd s.L s.Y₂ s.hL.le s.hY₂
  hXU₁ := div_le_div_of_nonneg_right s.hXU₁ (Nat.cast_nonneg _)
  hXU₂ := div_le_div_of_nonneg_right s.hXU₂ (Nat.cast_nonneg _)
  hYU₁ := div_le_div_of_nonneg_right s.hYU₁ (Nat.cast_nonneg _)
  hYU₂ := div_le_div_of_nonneg_right s.hYU₂ (Nat.cast_nonneg _)
  hpX := by rw [div_mul_div_comm,s.hpX];rfl
  hpY := by rw [div_mul_div_comm,s.hpY];rfl
  hP := s.hP
  hM := s.hM
  hpool := s.hpool
  hp := s.hp
  hpn := s.hpn
  hν := s.hν
  hWnorm := s.hWnorm
  hW := s.hW
  hS := s.hS
  hH := s.hH
  henclose := by
    intro I hI hlen
    apply s.henclose I hI
    simpa only [one_mul,map_mul,Nat.cast_mul,div_div] using hlen

theorem rebase_prefix (s : Source ι a b) : (rebase s).d=(1,1) := rfl

theorem rebase_length (s : Source ι a b) :
    (rebase s).L=s.L/prefixNormMax s.d := rfl

theorem rebase_enclosure (s : Source ι a b) (cover : OriginalEnclosure s) :
    OriginalEnclosure (rebase s) := by
  intro I hI hlen
  apply cover I hI
  simpa only [rebase,map_one,Nat.cast_one,div_one] using hlen

/-- Both ordinary finite pools are exactly the same at the divided
scales. No support is discarded, even when a divided scale is below one. -/
theorem rebase_pools (s : Source ι a b) : tuplePools (rebase s)=tuplePools s := by
  change sourcePools s.pool (1,1) ⟨one_ne_zero,one_ne_zero⟩ b
    (s.X₁/s.d.1.absNorm) (s.X₂/s.d.2.absNorm)
    (s.Y₁/s.d.1.absNorm) (s.Y₂/s.d.2.absNorm)=
      sourcePools s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂
  unfold sourcePools
  simp only [residual_plain_pool,map_one,Nat.cast_one,div_one]

theorem rebase_columns (s : Source ι a b) : sourceColumns (rebase s)=sourceColumns s := by
  unfold sourceColumns
  rw [rebase_pools]

/-- The inherited rectangle identity keeps the coprimality gate and
the final seed condition unchanged, before any tuple summation. -/
theorem profile_rebase (s : Source ι a b) (seed : Id)
    (W₁ W₂ : ℝ→ℂ) (v : Tuple ι) :
    profileCoefficient s.R s.ν s.Wslot s.P W₁ W₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v=
      profileCoefficient s.R s.ν s.Wslot s.P W₁ W₂
        (s.X₁/s.d.1.absNorm) (s.X₂/s.d.2.absNorm)
        (s.Y₁/s.d.1.absNorm) (s.Y₂/s.d.2.absNorm) 1 1 seed v := by
  unfold profileCoefficient
  rw [idealRectangle_extract]
  simp only [one_mul]

/-- Literal weighted column equality. In particular tupleWeight remains
inside the finite column sum, so cancellation and all natural zeros agree. -/
theorem rebase_coefficient (s : Source ι a b) (ha : 0<a) (seed : Id) :
    sourceCoefficient (rebase s) ha seed=sourceCoefficient s ha seed := by
  let W₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let W₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  change finiteColumnCoefficient (Fintype.piFinset (tuplePools (rebase s)))
      (fun v=>tupleWeight (punctureProduct s.S s.H) v*
        profileCoefficient s.R s.ν s.Wslot s.P W₁ W₂
          (s.X₁/s.d.1.absNorm) (s.X₂/s.d.2.absNorm)
          (s.Y₁/s.d.1.absNorm) (s.Y₂/s.d.2.absNorm) 1 1 seed v)=
    finiteColumnCoefficient (Fintype.piFinset (tuplePools s))
      (fun v=>tupleWeight (punctureProduct s.S s.H) v*
        profileCoefficient s.R s.ν s.Wslot s.P W₁ W₂
          s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v)
  rw [rebase_pools]
  congr 1
  funext v
  rw [profile_rebase s seed W₁ W₂ v]

theorem rebase_volume (s : Source ι a b) :
    sourceVolume (rebase s)=sourceVolume s/pairNorm s.d := by
  change (s.X₁/s.d.1.absNorm)*(s.X₂/s.d.2.absNorm)*(∏i,s.P i)=
    (s.X₁*s.X₂*∏i,s.P i)/pairNorm s.d
  rw [div_mul_div_comm]
  unfold pairNorm
  ring

/-- This is the sole outside normalization change for any identical raw
energy. It is an equality, with no sign or analytical hypothesis. -/
theorem normalized_energy_rebase (s : Source ι a b) (E : ℝ) :
    E/sourceVolume s=(E/sourceVolume (rebase s))/pairNorm s.d := by
  rw [rebase_volume]
  field_simp [(sourceVolume_pos s).ne',(pairNorm_pos s.hd.1 s.hd.2).ne'] <;> ring

def weightedRow (s : Source ι a b) (ha : 0<a) (seed : Id) (f : Id→ℂ) : ℂ :=
  normalization (s.X₁*s.X₂) s.P*
    ∑I∈sourceColumns s,sourceCoefficient s ha seed I*f I

/-- A row may carry any fixed character, window or height test f; the
actual weighted source is still present and is never replaced by f. -/
theorem weighted_row_square (s : Source ι a b) (ha : 0<a) (seed : Id) (f : Id→ℂ) :
    ‖weightedRow s ha seed f‖^2=
      ‖weightedRow (rebase s) ha seed f‖^2/pairNorm s.d := by
  have hnormal (r : Source ι a b) :
      ‖weightedRow r ha seed f‖^2=
        ‖∑I∈sourceColumns r,sourceCoefficient r ha seed I*f I‖^2/sourceVolume r := by
    rw [weightedRow,norm_mul,mul_pow,
      normalization_sq (r.X₁*r.X₂)
        (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)) r.P
        (fun i=>zero_lt_one.trans_le (r.hP i))]
    unfold sourceVolume
    ring
  rw [hnormal,hnormal,rebase_columns,rebase_coefficient]
  exact normalized_energy_rebase s _

/-- A selected-divisor/row average retains precisely the same outer
weights and one outside 1/p. No positivity of the weights is required. -/
theorem weighted_moment_rebase {κ : Type*} (s : Source ι a b) (ha : 0<a)
    (seed : Id) (rows : Finset κ) (w : κ→ℝ) (f : κ→Id→ℂ) :
    (∑x∈rows,w x*‖weightedRow s ha seed (f x)‖^2)=
      (∑x∈rows,w x*‖weightedRow (rebase s) ha seed (f x)‖^2)/pairNorm s.d := by
  simp_rw [weighted_row_square s ha seed]
  simp only [mul_div_assoc,Finset.sum_div]

/-- The same exact identity for the inherited radial energy with its
literal keep predicate, profile, radius and all independent heights. -/
theorem radial_moment_rebase (s : Source ι a b) (ha : 0<a) (seed : Id)
    (f : O→Id→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>weightedRow s ha seed (f z)) keep Φ K=
      radialEnergy (fun z=>weightedRow (rebase s) ha seed (f z)) keep Φ K/pairNorm s.d := by
  unfold radialEnergy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz,ite_true,weighted_row_square s ha seed]
    ring
  · simp only [hz,ite_false,zero_div]

end
end Candidate.SilPrior.FourthPower.MixedFirstRebase
