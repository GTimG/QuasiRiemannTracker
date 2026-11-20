/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Literal finite colored classes and their genuine native frame label images. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerBound
import Candidate.C092.transport.FixedPhysicalClassLedgerLabels
import Candidate.C092.transport.ColoredGaussFrameProviderRenormFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedPhysicalClassLedger
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.ColoredGaussFrameProvider
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The native class set is filtered only after forming the actual colored
    coefficient. No zero of the uncolored aggregate is used. -/
def actualClass (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Character)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ) (n : Fin 4→ℤ) :=
  (Finset.univ : Finset (Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
    (fun l=>inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc R H l n ∧
      classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) ψ χ₀ Q m t Kc R l n≠0)

theorem grouped_fixed_le_classes (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ ψ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc Tsec Z ξ H : ℝ) (hKc : 0<Kc) (M : ℤ)
    (hbox : ∀l n,inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc
      (frequencyRadius Tsec Z ξ) H l n→n∈box M) :
    RootColoredSeed.groupedPartTerms true s ha (idealCoeff ω₁) (idealCoeff ω₂) ψ χ₀ Q m t Kc Tsec Z ξ H  ≤ 
    ∑n∈box M,∑l∈actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc
      (frequencyRadius Tsec Z ξ) H n,
      classWeight (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc l n *
      ‖classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) ψ χ₀ Q m t Kc
        (frequencyRadius Tsec Z ξ) l n‖ :=
  splitLabel_le_classes _ _ ψ χ₀ Q m t Kc _ H hKc M hbox

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

def actualFrameLabels (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (n : Fin 4→ℤ) (χ : RayCharacter) : Finset (GLabel θ mesh Z) :=
  ((actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n).sigma
    (labelPool (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).image
      (fun k=>(frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).toLabel (θ:=θ) (mesh:=mesh) (Z:=Z) η)

/-- Fits is proved for every actual image label from the genuine coefficient
    carrier, cube-free constraints, source norm cap, and original hole data. -/
theorem actualFrameLabels_fits (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayCharacter)
    (hholes : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap))
    (hR₀ : ∀i,∀P∈s.H,P.val∈rs.R₀ i) (X : ℝ)
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ) ≤ X)
    (hbudget : (s.R.absNorm:ℝ)*X^2*((∏I∈holes s.H,I).absNorm:ℝ) ≤ Z^θ.Bmask) :
    ∀x∈actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ,Fits η rs x := by
  intro x hx
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
  exact toLabel_fits η rs _ (frame_good ω₁ ω₂ s ha rs j₀ ξ g hg n χ k
    (Finset.mem_sigma.mp hk).2 hholes hR₀ X hX hbudget)

/-- Native Bmask≥24 fits every actual label under the existing Z^8
    root/selected column caps. Original holes are empty, as proved by the producer. -/
theorem actualFrameLabels_fits_caps (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayCharacter) (hH : s.H=∅) (hB : (24:ℝ) ≤ θ.Bmask)
    (hR : (s.R.absNorm:ℝ) ≤ Z^(8:ℝ))
    (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ) ≤ Z^(8:ℝ)) :
    ∀x∈actualFrameLabels η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g n χ,Fits η rs x := by
  apply actualFrameLabels_fits η s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H rs j₀ ξ g hg n χ
  · rw [hH];exact Finset.empty_subset _
  · intro i P hP;rw [hH] at hP;exact False.elim (Finset.notMem_empty _ hP)
  · exact hX
  · have hz : 0<Z := zero_lt_one.trans rs.hZ
    have hh : (s.R.absNorm:ℝ)*(Z^(8:ℝ))^2  ≤  Z^(24:ℝ) := by
      calc
        _  ≤  Z^(8:ℝ)*(Z^(8:ℝ))^2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
        _ = Z^(24:ℝ) := by
          rw [show (24:ℝ)=8+8*2 by norm_num,Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_two]
    have hh' := hh.trans (Real.rpow_le_rpow_of_exponent_le rs.hZ.le hB)
    simpa [hH,MixedCompletedRows.holes] using hh'


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
    classWeight (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc k.1 n  ≤ 
    (rs.vol/θ.a^2)*(rho (frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).G *
      ‖(frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).prefactor‖ *
      ((g k.1).absNorm:ℝ)*((s.d.1.absNorm:ℝ)*(s.d.2.absNorm:ℝ))*rs.norm) := by
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  let clow := θ.a^2
  have hcol := QRH.Cycle092.ColoredGaussFrameProvider.colored_hcol ω₁ ω₂ s ha rs hX₁ hX₂ hP

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
  have h1 : rs.vol  ≤  (PD/clow) * ((C₂.absNorm : ℝ) * dyadicScale (n 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcl]
    have : PD * ((C₂.absNorm : ℝ) * (I.absNorm : ℝ))  ≤  PD * ((C₂.absNorm : ℝ) * dyadicScale (n 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIn.le hCn.le) hPD0.le
    nlinarith
  have h2 : rs.vol  ≤  (PD/clow) * ((D₂.absNorm : ℝ) * dyadicScale (n 3)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcl]
    have : PD * ((D₂.absNorm : ℝ) * (J.absNorm : ℝ))  ≤  PD * ((D₂.absNorm : ℝ) * dyadicScale (n 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJn.le hDn.le) hPD0.le
    nlinarith
  have hos := outerScalar_le C₂ D₂ hCs.1 hDs.1 Kc hKc.le n rs.vol (PD/clow) hvol (by positivity)
    h1 h2
  have hnz : normalizer C₂ D₂ k.1.2  ≤  ((g k.1).absNorm : ℝ) := by
    rcases hg k.1 with h | h <;> rw [h]
    · exact normalizer_le_left C₂ D₂ hCs hDs hCD k.1.2
    · exact normalizer_le_right C₂ D₂ hCs hDs hCD k.1.2
  have hnorm : rs.norm = Kc / rs.vol^2 := by unfold GSrc.norm; rw [hkLog]
  have hn0 := (normalizer_pos C₂ D₂ hCs k.1.2).le
  have hK := hKc
  change ‖rhoC C₂‖ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2)  ≤ 
    (rs.vol / clow) * (rho (g k.1) * ‖(1:ℂ)‖ * ((g k.1).absNorm : ℝ) * PD * rs.norm)
  rw [norm_rhoC, rho_column hg, norm_one, mul_one, hnorm]
  have hr0 : 0  ≤  rho C₂ := by unfold rho; positivity
  calc rho C₂ * (outerScalar C₂ D₂ Kc n * normalizer C₂ D₂ k.1.2)
       ≤  rho C₂ * ((PD/clow * rs.vol) * (Kc / rs.vol^2) * ((g k.1).absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hos hnz hn0 (by positivity)) hr0
    _ = (rs.vol / clow) * (rho C₂ * ((g k.1).absNorm : ℝ) * PD * (Kc / rs.vol^2)) := by ring

/-- The authentic class-to-frame map keeps its original multiplicity.
The second divisor is recovered from the image label, so it adds no duplicate. -/
theorem frame_mult (η : Character) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z) (j₀ : DictIdx) (ξ : RayCharacter)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (n : Fin 4→ℤ) (χ : RayCharacter)
    (Ks : Finset (Σ _ : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)),Id))
    (Mm : ℕ) (hmult : ∀G A,
      ((Finset.univ : Finset (Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
        (fun l=>g l=G ∧ lA _ l=A)).card  ≤  Mm) :
    let f := fun k=>(frameData j₀ ξ s rs (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g n χ k).toLabel
      (θ:=θ) (mesh:=mesh) (Z:=Z) η
    ∀y∈Ks.image f,(Ks.filter (fun k=>f k=y)).card  ≤  Mm := by
  intro f y hy
  refine le_trans ?_ (hmult y.G y.twist)
  apply Finset.card_le_card_of_injOn (fun k=>k.1)
  · intro k hk
    have he := (Finset.mem_filter.mp hk).2
    simp only [Finset.coe_filter,Set.mem_ofPred_eq,Finset.mem_univ,true_and]
    rw [←he]
    exact ⟨rfl,rfl⟩
  · intro k hk k' hk' he
    have hX := (Finset.mem_filter.mp hk).2
    have hX' := (Finset.mem_filter.mp hk').2
    have hD : k.2=k'.2 := by
      have e1 : (f k).D=k.2 := rfl
      have e2 : (f k').D=k'.2 := rfl
      rw [←e1,←e2,hX,hX']
    exact Sigma.ext he (heq_of_eq hD)

#print axioms frame_mult
#print axioms class_frame_ratio
#print axioms grouped_fixed_le_classes
#print axioms actualFrameLabels_fits_caps
end
end QRH.Cycle092.FixedPhysicalClassLedger
