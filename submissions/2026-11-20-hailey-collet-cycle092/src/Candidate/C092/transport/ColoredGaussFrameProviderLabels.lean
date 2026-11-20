/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Native fitting labels on the actual colored carrier, with explicit geometric cap debit. -/
import Candidate.C092.transport.ColoredGaussFrameProviderFrame
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeometry2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSectorLocalization CenteredMomentCompleteCommon
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- A native raised label over the true independently colored active carrier
    satisfies all Fits fields. The sole scalar debit is its explicit source
    norm/radical budget; no fitness or source-energy assertion is assumed. -/
theorem frame_good (ω₁ ω₂ : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayFourExpansion.RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayFourExpansion.RayCharacter)
    (k : Σ _ : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),Id)
    (hk : k.2∈labelPool (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) k.1)
    (hholes : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap))
    (hR₀ : ∀i,∀P∈s.H,P.val∈rs.R₀ i) (X : ℝ)
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤X)
    (hbudget : (s.R.absNorm:ℝ)*X^2*((∏I∈holes s.H,I).absNorm:ℝ)≤Z^θ.Bmask) :
    (frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).Good rs := by
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  have hGs := column_supported hg k.1
  have hsq : Squarefree k.2 := (Finset.mem_filter.mp hk).2
  have hc := lab_cols_le S X hX k.1
  have hgc : ((g k.1).absNorm:ℝ)≤X := by
    rcases hg k.1 with h|h <;> rw [h]
    · exact hc.1
    · exact hc.2
  obtain ⟨hk0,hkn⟩ := labelPool_le S X hX k.1 k.2 hk
  have hcube : g k.1 ∣ (∏P∈IdealMobiusDivisorSum.primeSupport (g k.1),P)^2 := by
    have hh := lab_cube_rad ω₁ ω₂ s ha k.1
    rcases hg k.1 with h|h <;> rw [h]
    · exact hh.1
    · exact hh.2
  have hcap := MixedSourceAssembly.radical_union_norm s.R (g k.1*k.2)
    s.hR (mul_ne_zero hGs.1 hk0) s.H
  have hX0 : 0≤X := (Nat.cast_nonneg (g k.1).absNorm).trans hgc
  have hmul : (((g k.1)*k.2).absNorm:ℝ)≤X^2 := by
    simp only [map_mul,Nat.cast_mul]
    exact (mul_le_mul hgc hkn (Nat.cast_nonneg _) hX0).trans_eq (pow_two X).symm
  have hcap' : (Ideal.absNorm (∏I∈QRH.Record1252270103KernelMass.primeSupport
      ((s.R*g k.1)*k.2)∪holes s.H,I):ℝ)≤Z^θ.Bmask := by
    rw [mul_assoc]
    apply hcap.trans
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans hbudget
  have hZ0 := zero_lt_one.trans rs.hZ
  have hN := absNorm_span_pos (lA S k.1) (lA_ne S k.1)
  refine { A_ne := lA_ne S k.1
           R_ne := s.hR
           G_ne := hGs.1
           seed_dvd := one_dvd _
           D_sq := hsq
           G_cube := hcube
           holes_sub := hholes
           cap := hcap'
           holes_R₀ := hR₀
           d₁ := s.hd.1
           d₂ := s.hd.2
           dual := ?_ }
  show Real.logb Z (((Ideal.span {lA S k.1}).absNorm:ℝ)*dyadicScale (raisedN rs S n k.1 1))≤
    2*rs.colLog-rs.kLog+mesh
  unfold raisedN
  rw [Function.update_self]
  obtain ⟨h1,_⟩ := topDyad_spec (Z^cutoffLog rs) _ (Real.rpow_pos_of_pos hZ0 _) hN
  rw [Real.logb_le_iff_le_rpow rs.hZ (mul_pos hN (dyadicScale_pos _))]
  exact h1

#print axioms frame_good
end
end QRH.Cycle092.ColoredGaussFrameProvider
