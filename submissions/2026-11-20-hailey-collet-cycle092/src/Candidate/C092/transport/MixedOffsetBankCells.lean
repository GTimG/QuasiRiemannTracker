/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The Q.2 bank on the literal buffered original amplitude subpartition. -/
import Candidate.C092.transport.MixedOffsetBankSource
import Candidate.C092.transport.ExistentialPacketBatches
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorFiberPartition HeckeDetectorAmplitudeFirst
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- No fresh buffer/grid or amplitude cell is selected. The caller's native
selected indices supply both detector bands on every original cell row.
The cutoff endpoints are fixed before the bank's attaining zeros/responses. -/
theorem actual_buffered_cell_bank (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200:ℝ)*D.cost) (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀ (idx grid : FreeRow→ℕ),ProbeAssembly.selected D F padding τ n η Z idx grid →
    ∀ (d threshold : ℝ),(1/200:ℝ)≤d → d≤7/8 → 1/50<threshold →
    ∀ (i k : ℕ) (z : Fin D.N→ℂ),(∀s,(z s).re=17/50) →
      (∀s,|(z s).im|≤(3*i+1:ℕ)*Z^τ) →
    let rows:=mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k
    rows.Nonempty →
    CommonBand D F η (Z^(Geometry.h+padding)) Z τ d threshold n idx grid (cellHeights idx i z) i k ∧
    ∀ bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
    let cell:=amplitudeCell D F Z d (bandLower D k) rows z bin
    cell.Nonempty → ∀ (t₀ γ : ℝ),0≤γ → 1≤t₀-γ → t₀≤3/2 →
      Nonempty (SourceBank F.modulus ⊤ le_top F.S F.exclusions η cell (Z^d) (bandLower D k)
        D.ε t₀ γ (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i) := by
  have hband:=actual_common_band D F P τ n hτ hheight
  have hbank:=actual_source_bank F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t n
    (by norm_num) (by norm_num) hτ (witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small
    D.cost_pos.le D.t_pos D.detector_budget
  filter_upwards [hband,hbank] with Z hband hbank
  refine ⟨hband.1,?_⟩
  intro idx grid hsel d threshold hd hd' hthreshold i k z hz hzim
  dsimp only
  intro hne
  have hgateRe : ∀ u s,(cellHeights idx i z u s).re=17/50 := by
    intro u s;by_cases h : idx u=i <;> simp [cellHeights,h,hz]
  have hgateIm : ∀ u s,|(cellHeights idx i z u s).im|≤(3*idx u+1:ℕ)*Z^τ := by
    intro u s
    by_cases h : idx u=i
    · simpa [cellHeights,h] using hzim s
    · norm_num [cellHeights,h]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_lt_one.trans hband.1).le _)
  have hne':=hne
  rw [←mediumRows_cellHeights D F (Z^(Geometry.h+padding)) Z d threshold idx grid z i k] at hne'
  have hb:=hband.2 d padding (Z^(Geometry.h+padding)) threshold hd hd' hthreshold
    η idx grid hsel (cellHeights idx i z) hgateRe hgateIm i k hne'
  refine ⟨hb,?_⟩
  have hrows:=hb.rows_band
  have hcal:=hb.calibration
  have hnorm:=hb.conductor
  have hnext:=hb.next
  have hcurrent:=hb.current
  rw [mediumRows_cellHeights] at hrows hcal hnorm hnext hcurrent
  intro bin
  intro hneCell t₀ γ hγ ht ht'
  have hsub : amplitudeCell D F Z d (bandLower D k)
      (mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k) z bin ⊆
      mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k :=
    Finset.filter_subset _ _
  exact hbank d hd hd' (Z^(Geometry.h+padding)) _ (hsub.trans hrows)
    (fun u hu=>hcal u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) (bandLower D k) i
    hb.index_bound hb.nonfloor (hb.a_upper.trans (by norm_num))
    (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu)) t₀ γ hγ ht ht'

#print axioms actual_buffered_cell_bank
end
end QRH.Cycle092.MixedOffsetBank
