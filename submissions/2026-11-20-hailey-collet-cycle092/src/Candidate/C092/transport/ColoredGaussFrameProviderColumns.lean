/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Actual colored nonzero columns pay the native frame normalization. -/
import Candidate.C092.transport.ColoredGaussFrameProviderLabels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedCommonCoefficient MixedCommonRestriction
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance (priority := 2000) columnSumDecEq {κ κ₂ : Type*} : DecidableEq (κ⊕κ₂) := Classical.decEq _

theorem column_lower {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (seed I : Id) (hne : sourceColumn s ha ω₁ ω₂ seed I≠0) :
    a^2*sourceVolume s ≤ (s.d.1.absNorm:ℝ)*(s.d.2.absNorm:ℝ)*(I.absNorm:ℝ) := by
  obtain ⟨v,hv,hn,hprod⟩ := finiteColumnCoefficient_witness
    (Fintype.piFinset (tuplePools s))
    (fun v=>MixedOriginalSecondZero.originalTuple s ha seed v*ordinaryColor ω₁ ω₂ v) I hne
  rw [←hprod]
  have hpc : profileCoefficient s.R s.ν s.Wslot s.P
      (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v ≠ 0 := by
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hs' : ∀(W : 𝓢(ℝ,ℂ))(hsW : Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(t : ℝ),
      Function.support (CenteredMomentLattice.normPowerProfile W a b ha hsW (W.smooth ⊤) t : ℝ→ℂ)⊆Set.Icc a b := by
    intro W hsW t x hx
    apply hsW
    intro hz
    apply hx
    rw [CenteredMomentLattice.normPowerProfile_apply,hz,mul_zero]
  have hh := tuple_lower s.R s.ν s.Wslot s.P (fun i=>one_pos.trans_le (s.hP i)) s.hW _ _ a b ha
    (hs' s.W₁ s.hs₁ s.t₁) (hs' s.W₂ s.hs₂ s.t₂) s.X₁ s.X₂ s.Y₁ s.Y₂
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂)
    (s.hpX.trans s.hpY.symm) s.d.1 s.d.2 seed v hpc
  simpa only [sourceVolume,mul_assoc] using hh

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

theorem colored_hcol (ω₁ ω₂ : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (rs : GSrc θ mesh Z) (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
    (hP : ∀i,s.P i=Z^(rs.w i)) :
    ∀I, sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 I≠0 →
      θ.a^2*rs.vol ≤ (s.d.1.absNorm:ℝ)*(s.d.2.absNorm:ℝ)*(I.absNorm:ℝ) := by
  intro I hI
  have hh := column_lower s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 I hI
  have hv : rs.vol=sourceVolume s := by
    unfold GSrc.vol sourceVolume
    rw [hX₁,hX₂]
    simp only [hP]
  rw [hv]
  exact hh

/-- The true classWeight is converted to the unchanged native frame weight.
    Its column lower bound comes from actual colored tuple witnesses. -/
theorem class_frame_ratio (ω₁ ω₂ : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (rs : GSrc θ mesh Z) (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
    (hP : ∀i,s.P i=Z^(rs.w i)) (j₀ : DictIdx) (ξ : RayFourExpansion.RayCharacter)
    (ψ : Character) (χ₀ : RayFourExpansion.RayCharacter) (Q : Id) (m : O) (t Kc R : ℝ)
    (hKc : 0<Kc) (hkLog : Z^rs.kLog=Kc)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayFourExpansion.RayCharacter)
    (k : Σ _ : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),Id)
    (hb : classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
      (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) ψ χ₀ Q m t Kc R k.1 n≠0) :
    classWeight (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc k.1 n ≤
    (rs.vol/θ.a^2)*(rho (frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).G *
      ‖(frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).prefactor‖ *
      ((g k.1).absNorm:ℝ)*((s.d.1.absNorm:ℝ)*(s.d.2.absNorm:ℝ))*rs.norm) := by
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  let clow := θ.a^2
  have hcol := colored_hcol ω₁ ω₂ s ha rs hX₁ hX₂ hP

  have hZ0 : 0 < Z := zero_lt_one.trans rs.hZ
  set PD : ℝ := (s.d.1.absNorm : ℝ) * (s.d.2.absNorm : ℝ) with hPD
  have hPD0 : 0 < PD := by
    have h1 : 0 < (s.d.1.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.1)
    have h2 : 0 < (s.d.2.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.2)
    positivity
  have hvol := rs.vol_pos hZ0
  have hcl := (sq_pos_of_pos ha)
  obtain ⟨hCs, hDs, hCD⟩ := lab_data S k.1
  set C₂ := k.1.1.val.1
  set D₂ := k.1.1.val.2
  -- the columns of a nonzero block
  obtain ⟨⟨I, hI, hIn⟩, ⟨J, hJ, hJn⟩⟩ := labelBlock_ne_zero_column ψ t S
    (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) C₂ D₂ hCs hDs k.1.2 R _ ballProfile _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) hb
  have hc1 := hcol _ hI
  have hc2 := hcol _ hJ
  rw [map_mul, Nat.cast_mul] at hc1 hc2
  have hCn : 0 < (C₂.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hCs.1)
  have hDn : 0 < (D₂.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hDs.1)
  have hd2 := dyadicScale_pos (n 2)
  have hd3 := dyadicScale_pos (n 3)
  have h1 : rs.vol ≤ (PD/clow) * ((C₂.absNorm : ℝ) * dyadicScale (n 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcl]
    have : PD * ((C₂.absNorm : ℝ) * (I.absNorm : ℝ)) ≤ PD * ((C₂.absNorm : ℝ) * dyadicScale (n 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIn.le hCn.le) hPD0.le
    nlinarith
  have h2 : rs.vol ≤ (PD/clow) * ((D₂.absNorm : ℝ) * dyadicScale (n 3)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcl]
    have : PD * ((D₂.absNorm : ℝ) * (J.absNorm : ℝ)) ≤ PD * ((D₂.absNorm : ℝ) * dyadicScale (n 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJn.le hDn.le) hPD0.le
    nlinarith
  have hos := outerScalar_le C₂ D₂ hCs.1 hDs.1 Kc hKc.le n rs.vol (PD/clow) hvol (by positivity)
    h1 h2
  have hnz : normalizer C₂ D₂ k.1.2 ≤ ((g k.1).absNorm : ℝ) := by
    rcases hg k.1 with h | h <;> rw [h]
    · exact normalizer_le_left C₂ D₂ hCs hDs hCD k.1.2
    · exact normalizer_le_right C₂ D₂ hCs hDs hCD k.1.2
  have hnorm : rs.norm = Kc / rs.vol^2 := by unfold GSrc.norm; rw [hkLog]
  have hn0 := (normalizer_pos C₂ D₂ hCs k.1.2).le
  have hK := hKc
  change ‖rhoC C₂‖ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2) ≤
    (rs.vol / clow) * (rho (g k.1) * ‖(1:ℂ)‖ * ((g k.1).absNorm : ℝ) * PD * rs.norm)
  rw [norm_rhoC, rho_column hg, norm_one, mul_one, hnorm]
  have hr0 : 0 ≤ rho C₂ := by unfold rho; positivity
  calc rho C₂ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2)
      ≤ rho C₂ * ((PD/clow * rs.vol) * (Kc / rs.vol^2) * ((g k.1).absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hos hnz hn0 (by positivity)) hr0
    _ = (rs.vol / clow) * (rho C₂ * ((g k.1).absNorm : ℝ) * PD * (Kc / rs.vol^2)) := by ring

#print axioms column_lower
#print axioms class_frame_ratio
end
end QRH.Cycle092.ColoredGaussFrameProvider
