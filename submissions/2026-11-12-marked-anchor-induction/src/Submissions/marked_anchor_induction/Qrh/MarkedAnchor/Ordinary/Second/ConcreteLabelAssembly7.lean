/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 7: the hypotheses of `class_label_bound` from `RootLabelData`.

* `frame_good`: every frame label of a label and second divisor is `Good` (all `Fits` fields);
* `frame_dyad`: the raised dyad is at least twice the class row scale;
* `class_frame_ratio`: the class weight is at most `(vol/c)·ρ(G)·N(G)·(Z^k/X²)` on nonzero blocks
  (column-norm lower bound and `outerScalar_le`, `normalizer ≤ N(G)`).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly6

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondActiveDyadic CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

section
variable {η : Character} {P : SidePack η} {Q : Id} {m : O}
  {s : Source (Fin θ.N) θ.a θ.b} {ha : 0 < θ.a} {rs : GSrc θ mesh Z} {Kc R H : ℝ} {M : ℤ}
  {Mm : ℕ} {clow : ℝ}

/-- A column selector: `g l` is one of the two genuine common factors of `l`. -/
def IsColumn (S : Finset Id) (g : Lab S → Id) : Prop :=
  ∀ l, g l = l.1.val.1 ∨ g l = l.1.val.2

theorem column_supported {S : Finset Id} {g : Lab S → Id} (hg : IsColumn S g) (l : Lab S) :
    Supported (g l) := by
  rcases hg l with h | h <;> rw [h]
  · exact (lab_data S l).1
  · exact (lab_data S l).2.1

theorem rho_column {S : Finset Id} {g : Lab S → Id} (hg : IsColumn S g) (l : Lab S) :
    rho (g l) = rho l.1.val.1 := by
  rcases hg l with h | h <;> rw [h]
  unfold rho
  congr 2
  exact (lab_data S l).2.2.symm

/-- **All `Fits` fields of the frame labels.** -/
theorem frame_good (hR : RootLabelData (θ := θ) P Q m s ha rs Kc R H M Mm clow) (ξ : RayCharacter)
    (g : Lab (S0 s ha) → Id) (hg : IsColumn (S0 s ha) g) (n : Fin 4 → ℤ) (χ : RayCharacter)
    (k : Σ _ : Lab (S0 s ha), Id) (hk : k.2 ∈ labelPool (S0 s ha) k.1) :
    (frameData P.j₀ ξ s rs (S0 s ha) g n χ k).Good rs := by
  have hsq : Squarefree k.2 := (Finset.mem_filter.mp hk).2
  have hGs := column_supported hg k.1
  have hcap : (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport
      ((s.R * g k.1) * k.2) ∪ holes s.H, I) : ℝ) ≤ Z^θ.Bmask := by
    rcases hg k.1 with h | h <;> rw [h]
    · exact hR.hcapC k.1 k.2 hk
    · exact hR.hcapD k.1 k.2 hk
  have hcube : g k.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport (g k.1), P)^2 := by
    rcases hg k.1 with h | h <;> rw [h]
    · exact hR.hcubeRadC k.1
    · exact hR.hcubeRadD k.1
  have hZ0 : 0 < Z := zero_lt_one.trans rs.hZ
  have hN := absNorm_span_pos (lA (S0 s ha) k.1) (lA_ne _ k.1)
  refine
    { A_ne := lA_ne _ k.1
      R_ne := s.hR
      G_ne := hGs.1
      seed_dvd := one_dvd _
      D_sq := hsq
      G_cube := hcube
      holes_sub := hR.hholes_sub
      cap := hcap
      holes_R₀ := hR.hholes_R₀
      d₁ := s.hd.1
      d₂ := s.hd.2
      dual := ?_ }
  show Real.logb Z (((Ideal.span {lA (S0 s ha) k.1}).absNorm : ℝ) *
      dyadicScale (raisedN rs (S0 s ha) n k.1 1)) ≤ 2 * rs.colLog - rs.kLog + mesh
  unfold raisedN
  rw [Function.update_self]
  obtain ⟨h1, -⟩ := topDyad_spec (Z ^ cutoffLog rs) _ (Real.rpow_pos_of_pos hZ0 _) hN
  rw [Real.logb_le_iff_le_rpow rs.hZ (mul_pos hN (dyadicScale_pos _))]
  exact h1

/-- A nonzero class block has a retained row, hence `N(A₂) ≤ 4R`. -/
theorem twist_le_radius (ψ : Character) (χ₀ : RayCharacter) (t : ℝ) (S : Finset Id) (Kc : ℝ)
    (l : Lab S) (n : Fin 4 → ℤ)
    (hb : classBlock S (sourceCoefficient s ha 1) ψ χ₀ Q m t Kc R l n ≠ 0) :
    normValue (lA S l) ≤ 4 * R := by
  unfold classBlock labelBlock at hb
  obtain ⟨z, hz, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [CenteredMomentSecondEnergySplit.partRows_false] at hz
  have hz1 := (Finset.mem_filter.mp hz).1
  have hz0 := CenteredMomentSecondEnergySplit.sourceRows_nonzero _ _ _ _ z hz1
  have hw := CenteredMomentSecondLiveBlock.liveRows_weight _ _ _ _ _ z hz1
  have he := (retainedWeight_enclosure R _ hw).2
  rw [normValue_mul] at he
  have h1 := normValue_ge_one z hz0
  have h0 : 0 ≤ normValue (lA S l) := by unfold normValue; positivity
  have : normValue (lA S l) ≤ normValue (lA S l) * normValue z := le_mul_of_one_le_right h0 h1
  exact this.trans he

/-- **The raised dyad is above twice the class row scale.** -/
theorem frame_dyad (hR : RootLabelData (θ := θ) P Q m s ha rs Kc R H M Mm clow) (ξ : RayCharacter)
    (ψ : Character) (χ₀ : RayCharacter) (t : ℝ)
    (g : Lab (S0 s ha) → Id) (n : Fin 4 → ℤ) (χ : RayCharacter) (k : Σ _ : Lab (S0 s ha), Id)
    (hr : inRange (S0 s ha) Kc R H k.1 n)
    (hb : classBlock (S0 s ha) (sourceCoefficient s ha 1) ψ χ₀ Q m t Kc R k.1 n ≠ 0) :
    2 * dyadicScale (n 1) ≤
      dyadicScale ((frameData P.j₀ ξ s rs (S0 s ha) g n χ k).n 1) := by
  have hZ0 : 0 < Z := zero_lt_one.trans rs.hZ
  have hN := absNorm_span_pos (lA (S0 s ha) k.1) (lA_ne _ k.1)
  show 2 * dyadicScale (n 1) ≤ dyadicScale (raisedN rs (S0 s ha) n k.1 1)
  unfold raisedN
  rw [Function.update_self]
  apply dyad_lt_top _ _ (Real.rpow_pos_of_pos hZ0 _) hN
  have h1 := dyad_of_range _ _ _ (lA_ne _ k.1) Kc R H n (hr 1)
  have hA4 := twist_le_radius ψ χ₀ t (S0 s ha) Kc k.1 n hb
  have h2 : 8 * max (normValue (lA (S0 s ha) k.1)) (4 * R) ≤ Z ^ cutoffLog rs := by
    rw [max_eq_right hA4]; linarith [hR.hdyad]
  have he : normValue (lA (S0 s ha) k.1) = ((Ideal.span {lA (S0 s ha) k.1}).absNorm : ℝ) := rfl
  rw [he] at h1 h2
  change normValue (commonFrequencyGenerator k.1.1.val.1 k.1.1.val.2 *
    CenteredMomentSecondCanonicalNonunit.nonunitFrequencyGenerator k.1.1.val.1 k.1.1.val.2 k.1.2) *
      dyadicScale (n 1) ≤ _ at h1
  have h1' : ((Ideal.span {lA (S0 s ha) k.1}).absNorm : ℝ) * dyadicScale (n 1) ≤
      4 * max ((Ideal.span {lA (S0 s ha) k.1}).absNorm : ℝ) (4 * R) := h1
  linarith

/-- **The class weight ratio** on a nonzero block. -/
theorem class_frame_ratio (hR : RootLabelData (θ := θ) P Q m s ha rs Kc R H M Mm clow) (ξ : RayCharacter)
    (ψ : Character) (χ₀ : RayCharacter) (t : ℝ)
    (g : Lab (S0 s ha) → Id) (hg : IsColumn (S0 s ha) g) (n : Fin 4 → ℤ) (χ : RayCharacter)
    (k : Σ _ : Lab (S0 s ha), Id)
    (hb : classBlock (S0 s ha) (sourceCoefficient s ha 1) ψ χ₀ Q m t Kc R k.1 n ≠ 0) :
    classWeight (S0 s ha) Kc k.1 n ≤ (rs.vol / clow) *
      (rho (frameData P.j₀ ξ s rs (S0 s ha) g n χ k).G *
        ‖(frameData P.j₀ ξ s rs (S0 s ha) g n χ k).prefactor‖ *
        (((frameData P.j₀ ξ s rs (S0 s ha) g n χ k).G.absNorm : ℝ)) *
        ((((frameData P.j₀ ξ s rs (S0 s ha) g n χ k).d.1.absNorm : ℝ)) *
          (((frameData P.j₀ ξ s rs (S0 s ha) g n χ k).d.2.absNorm : ℝ))) * rs.norm) := by
  have hZ0 : 0 < Z := zero_lt_one.trans rs.hZ
  set PD : ℝ := (s.d.1.absNorm : ℝ) * (s.d.2.absNorm : ℝ) with hPD
  have hPD0 : 0 < PD := by
    have h1 : 0 < (s.d.1.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.1)
    have h2 : 0 < (s.d.2.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hd.2)
    positivity
  have hvol := rs.vol_pos hZ0
  have hcl := hR.hclow_pos
  obtain ⟨hCs, hDs, hCD⟩ := lab_data (S0 s ha) k.1
  set C₂ := k.1.1.val.1
  set D₂ := k.1.1.val.2
  -- the columns of a nonzero block
  obtain ⟨⟨I, hI, hIn⟩, ⟨J, hJ, hJn⟩⟩ := labelBlock_ne_zero_column ψ t (S0 s ha)
    (sourceCoefficient s ha 1) C₂ D₂ hCs hDs k.1.2 R _ ballProfile _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) hb
  have hc1 := hR.hcol _ hI
  have hc2 := hR.hcol _ hJ
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
  have hos := outerScalar_le C₂ D₂ hCs.1 hDs.1 Kc hR.hKc.le n rs.vol (PD/clow) hvol (by positivity)
    h1 h2
  have hnz : normalizer C₂ D₂ k.1.2 ≤ ((g k.1).absNorm : ℝ) := by
    rcases hg k.1 with h | h <;> rw [h]
    · exact normalizer_le_left C₂ D₂ hCs hDs hCD k.1.2
    · exact normalizer_le_right C₂ D₂ hCs hDs hCD k.1.2
  have hnorm : rs.norm = Kc / rs.vol^2 := by unfold GSrc.norm; rw [hR.hkLog]
  have hn0 := (normalizer_pos C₂ D₂ hCs k.1.2).le
  have hK := hR.hKc
  change ‖rhoC C₂‖ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2) ≤
    (rs.vol / clow) * (rho (g k.1) * ‖(1:ℂ)‖ * ((g k.1).absNorm : ℝ) * PD * rs.norm)
  rw [norm_rhoC, rho_column hg, norm_one, mul_one, hnorm]
  have hr0 : 0 ≤ rho C₂ := by unfold rho; positivity
  calc rho C₂ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2)
      ≤ rho C₂ * ((PD/clow * rs.vol) * (Kc / rs.vol^2) * ((g k.1).absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hos hnz hn0 (by positivity)) hr0
    _ = (rs.vol / clow) * (rho C₂ * ((g k.1).absNorm : ℝ) * PD * (Kc / rs.vol^2)) := by ring

end

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
