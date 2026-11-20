/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Literal finite colored classes and their genuine native frame label images. -/
import Candidate.C092.transport.ActualLabelFiniteCostsSupply
import Candidate.C092.transport.ColoredGaussFrameProviderActual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularPhysicalClassBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup
open CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWindowBudget CenteredMomentSecondExceptionalFamily CenteredMomentChildRows
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
open QRH.Cycle092.RegularColoredForward
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

lemma twist_le_radius (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (S : Finset Id) (β : Id→ℂ) (Kc R : ℝ) (l : Lab S) (n : Fin 4→ℤ)
    (hb : classBlock S β ψ χ₀ Q m t Kc R l n≠0) : normValue (lA S l) ≤ 4*R := by
  unfold classBlock labelBlock at hb
  obtain ⟨z,hz,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hz1 := (Finset.mem_filter.mp hz).1
  have hz0 := CenteredMomentSecondEnergySplit.sourceRows_nonzero _ _ _ _ z hz1
  have hw := liveRows_weight _ _ _ _ _ z hz1
  have he := (retainedWeight_enclosure R _ hw).2
  rw [normValue_mul] at he
  have h1 := normValue_ge_one z hz0
  have h0 : 0≤normValue (lA S l) := by unfold normValue;positivity
  exact (le_mul_of_one_le_right h0 h1).trans he

/-- The original regular class supplies the same actual raised dyad. -/
lemma frame_dyad (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z)
    (S : Finset Id) (β : Id→ℂ) (j₀ : DictIdx) (ξ : RayCharacter)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t Kc R H : ℝ)
    (g : Lab S→Id) (n : Fin 4→ℤ) (χ : RayCharacter) (k : Σ _ : Lab S,Id)
    (hr : inRange S Kc R H k.1 n) (hb : classBlock S β ψ χ₀ Q m t Kc R k.1 n≠0)
    (hcut : 32*R ≤ Z^cutoffLog rs) :
    2*dyadicScale (n 1) ≤ dyadicScale ((frameData j₀ ξ s rs S g n χ k).n 1) := by
  have hz : 0<Z := zero_lt_one.trans rs.hZ
  have hN := absNorm_span_pos (lA S k.1) (lA_ne _ k.1)
  show 2*dyadicScale (n 1) ≤ dyadicScale (raisedN rs S n k.1 1)
  unfold raisedN
  rw [Function.update_self]
  apply dyad_lt_top _ _ (Real.rpow_pos_of_pos hz _) hN
  have h1 := dyad_of_range _ _ _ (lA_ne _ k.1) Kc R H n (hr 1)
  have hA4 := twist_le_radius ψ χ₀ Q m t S β Kc R k.1 n hb
  have h2 : 8*max (normValue (lA S k.1)) (4*R) ≤ Z^cutoffLog rs := by
    rw [max_eq_right hA4]
    linarith
  have he : normValue (lA S k.1)=((Ideal.span {lA S k.1}).absNorm:ℝ) := rfl
  rw [he] at h1 h2
  change normValue (commonFrequencyGenerator k.1.1.val.1 k.1.1.val.2*
    nonunitFrequencyGenerator k.1.1.val.1 k.1.1.val.2 k.1.2)*dyadicScale (n 1) ≤ _ at h1
  have h1' : ((Ideal.span {lA S k.1}).absNorm:ℝ)*dyadicScale (n 1) ≤
    4*max ((Ideal.span {lA S k.1}).absNorm:ℝ) (4*R) := h1
  linarith

/-- A complete actual regular class is bounded by its genuine finite native
label image. The original class-image multiplicity Mm is charged once.
The caller supplies the filled/exhausted numerical frame budget B₀. -/
theorem actual_class_bound (ω₁ ω₂ : Character) (J : ℕ) :
    ∃ Cg : ℝ,0≤Cg ∧
    ∀ {L : ℝ} {θ : GData L} {mesh Z : ℝ} {η : Character} (P : SidePack η)
      (ξ : RayCharacter) (Q : Id) (m : O) (hm : m≠0)
      (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m) (hQ72 : Q≤Ideal.span {(72:O)})
      (hQ : internalQ θ.Q θ.η₀=Q) (χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (rs : GSrc θ mesh Z)
      (hW₁ : rs.W₁=s.W₁) (hW₂ : rs.W₂=s.W₂) (ht₁ : rs.t₁=s.t₁/(2*Real.pi))
      (ht₂ : rs.t₂=s.t₂/(2*Real.pi)) (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
      (hY₁ : rs.Y₁=s.Y₁) (hY₂ : rs.Y₂=s.Y₂) (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R)
      (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d)
      (t Kc R H : ℝ) (n : Fin 4→ℤ) (hKc : 0<Kc) (hkLog : Z^rs.kLog=Kc)
      (hcut : 32*R≤Z^cutoffLog rs)
      (hholes : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap))
      (hR₀ : ∀i,∀P∈s.H,P.val∈rs.R₀ i) (Xcol : ℝ)
      (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Xcol)
      (hbudget : (s.R.absNorm:ℝ)*Xcol^2*((∏I∈holes s.H,I).absNorm:ℝ)≤Z^θ.Bmask)
      (Mm : ℕ) (hmult : ∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
        IsColumn _ g → ∀G A,((Finset.univ : Finset (Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
          (fun l=>g l=G ∧ lA _ l=A)).card≤Mm)
      (B₀ : ℝ) (hB₀ : 0≤B₀)
      (hseam : ∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
        IsColumn _ g → ∀χ v,
        ∑x∈actualFrameLabels η s ha ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R H rs P.j₀ ξ g n χ,
          gWeight x*framegEnergy ω₁ ω₂ η rs x v≤B₀*(1+‖v‖)^(2*J)),
    (∑l∈actualClass s ha ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R H n,
      classWeight (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc l n*
      ‖classBlock (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
        (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) (childCharacter P.base ξ) χ₀ Q m t Kc R l n‖)≤
      Cg*((rs.vol/θ.a^2)*Mm*B₀)*(heightEnvelope t^J*profileMoment J)^2 := by
  obtain ⟨Cg,hCg,hcl⟩ := ColoredGaussFrameProvider.class_label_bound ω₁ ω₂ ballProfile 0 J
  refine ⟨Cg,hCg,?_⟩
  intro L θ mesh Z η P ξ Q m hm hl h2 hQ72 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    hV₀ hCR hcan t Kc R H n hKc hkLog hcut hholes hR₀ Xcol hX hbudget Mm hmult B₀ hB₀ hseam
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  let β := sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1
  let ψ := childCharacter P.base ξ
  let Ls := actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n
  let gC : Lab S→Id := fun l=>l.1.val.1
  let gD : Lab S→Id := fun l=>l.1.val.2
  have hgC : IsColumn S gC := fun l=>Or.inl rfl
  have hgD : IsColumn S gD := fun l=>Or.inr rfl
  have hLmem : ∀l∈Ls,inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n≠0 :=
    fun l hl=>(Finset.mem_filter.mp hl).2
  have hmem : ∀k∈Ls.sigma (fun l=>(classLabel ψ χ₀ Q m Kc R S n l).pool),
      k.1∈Ls ∧ k.2∈labelPool S k.1 := fun k hk=>Finset.mem_sigma.mp hk
  have hwt : ∀l,0≤classWeight S Kc l n := by
    intro l
    unfold classWeight
    have hn := (normalizer_pos _ _ (lab_data S l).1 l.2).le
    have ho : 0≤outerScalar l.1.val.1 l.1.val.2 Kc n := by unfold outerScalar;positivity
    positivity
  have hSs : S⊆sourceColumns s := Finset.filter_subset _ _
  have hSz : ∀I∈sourceColumns s,I∉S → sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 I=0 := by
    intro I hI hn
    by_contra hc
    exact hn ((CenteredMomentActiveSource.mem_activeSource _ _ _).mpr ⟨hI,hc⟩)
  have hvol : 0<rs.vol := rs.vol_pos (zero_lt_one.trans rs.hZ)
  have hE : 0≤(rs.vol/θ.a^2)*Mm*B₀ := by positivity
  have h := hcl P ξ Q m hm hl h2 hQ72 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    hV₀ hCR S hSs hSz Ls (classLabel ψ χ₀ Q m Kc R S n) (fun l=>famSpec ψ S l)
    (fun l=>classWeight S Kc l n) hwt
    (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
    (by have := dyadicScale_pos (n 0);have := dyadicScale_pos (n 1);have := dyadicScale_pos (n 2);have := dyadicScale_pos (n 3);positivity)
    t (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    (dyadicScale (n 1)) (dyadicScale_pos _) (fun l _=>rows_major _ _ (dyadicScale_pos _))
    (rs.vol/θ.a^2) B₀ B₀ (by positivity) hB₀ hB₀ Mm
    (frameData P.j₀ ξ s rs S gC n) (frameData P.j₀ ξ s rs S gD n)
    (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
    (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
    (fun χ k hk=>ColoredGaussFrameProvider.frame_good ω₁ ω₂ s ha rs P.j₀ ξ gC hgC n χ k (hmem k hk).2 hholes hR₀ Xcol hX hbudget)
    (fun χ k hk=>ColoredGaussFrameProvider.frame_good ω₁ ω₂ s ha rs P.j₀ ξ gD hgD n χ k (hmem k hk).2 hholes hR₀ Xcol hX hbudget)
    (fun _ _=>hcan) (fun _ _=>hcan)
    (fun χ k hk=>frame_dyad s rs S β P.j₀ ξ ψ χ₀ Q m t Kc R H gC n χ k (hLmem k.1 (hmem k hk).1).1 (hLmem k.1 (hmem k hk).1).2 hcut)
    (fun χ k hk=>frame_dyad s rs S β P.j₀ ξ ψ χ₀ Q m t Kc R H gD n χ k (hLmem k.1 (hmem k hk).1).1 (hLmem k.1 (hmem k hk).1).2 hcut)
    (fun χ k hk=>class_frame_ratio ω₁ ω₂ s ha rs hX₁ hX₂ hcan.P P.j₀ ξ ψ χ₀ Q m t Kc R hKc hkLog gC hgC n χ k (hLmem k.1 (hmem k hk).1).2)
    (fun χ k hk=>class_frame_ratio ω₁ ω₂ s ha rs hX₁ hX₂ hcan.P P.j₀ ξ ψ χ₀ Q m t Kc R hKc hkLog gD hgD n χ k (hLmem k.1 (hmem k hk).1).2)
    (fun χ=>FixedPhysicalClassLedger.frame_mult η s ha ω₁ ω₂ rs P.j₀ ξ gC n χ _ Mm (hmult gC hgC))
    (fun χ=>FixedPhysicalClassLedger.frame_mult η s ha ω₁ ω₂ rs P.j₀ ξ gD n χ _ Mm (hmult gD hgD))
    (hseam gC hgC) (hseam gD hgD)
  rw [pow_zero,one_mul,windowBudget_sq J t _ hE] at h
  rw [mul_assoc Cg]
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro l hl
  rw [classBlock_eq]

/-- Every actual dyadic class is included, with the original box cardinality. -/
theorem actual_split_bound (ω₁ ω₂ : Character) (J : ℕ) :
    ∃ Cg : ℝ,0≤Cg ∧
    ∀ {L : ℝ} {θ : GData L} {mesh Z : ℝ} {η : Character} (P : SidePack η)
      (ξ : RayCharacter) (Q : Id) (m : O) (hm : m≠0)
      (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m) (hQ72 : Q≤Ideal.span {(72:O)})
      (hQ : internalQ θ.Q θ.η₀=Q) (χ₀ : RayCharacter)
      (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (rs : GSrc θ mesh Z)
      (hW₁ : rs.W₁=s.W₁) (hW₂ : rs.W₂=s.W₂) (ht₁ : rs.t₁=s.t₁/(2*Real.pi))
      (ht₂ : rs.t₂=s.t₂/(2*Real.pi)) (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
      (hY₁ : rs.Y₁=s.Y₁) (hY₂ : rs.Y₂=s.Y₂) (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R)
      (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d)
      (t Kc R H : ℝ) (M : ℤ) (hKc : 0<Kc) (hkLog : Z^rs.kLog=Kc)
      (hcut : 32*R≤Z^cutoffLog rs)
      (hbox : ∀l n,inRange (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) Kc R H l n → n∈box M)
      (hholes : s.H⊆ReferencePrimeEnclosure.enclosure (θ.Cap*Z^θ.Lcap))
      (hR₀ : ∀i,∀P∈s.H,P.val∈rs.R₀ i) (Xcol : ℝ)
      (hX : ∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Xcol)
      (hbudget : (s.R.absNorm:ℝ)*Xcol^2*((∏I∈holes s.H,I).absNorm:ℝ)≤Z^θ.Bmask)
      (Mm : ℕ) (hmult : ∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
        IsColumn _ g → ∀G A,((Finset.univ : Finset (Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
          (fun l=>g l=G ∧ lA _ l=A)).card≤Mm)
      (B₀ : ℝ) (hB₀ : 0≤B₀)
      (hseam : ∀n∈box M,∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
        IsColumn _ g → ∀χ v,
        ∑x∈actualFrameLabels η s ha ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R H rs P.j₀ ξ g n χ,
          gWeight x*framegEnergy ω₁ ω₂ η rs x v≤B₀*(1+‖v‖)^(2*J)),
    splitLabel (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))
      (sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) (childCharacter P.base ξ) χ₀ Q m t Kc R H ≤
      ((box M).card:ℝ)*Cg*((rs.vol/θ.a^2)*Mm*B₀)*(heightEnvelope t^J*profileMoment J)^2 := by
  obtain ⟨Cg,hCg,hclass⟩ := actual_class_bound ω₁ ω₂ J
  refine ⟨Cg,hCg,?_⟩
  intro L θ mesh Z η P ξ Q m hm hl h2 hQ72 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
    hV₀ hCR hcan t Kc R H M hKc hkLog hcut hbox hholes hR₀ Xcol hX hbudget Mm hmult B₀ hB₀ hseam
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  let β := sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1
  let ψ := childCharacter P.base ξ
  calc
    _ ≤ ∑n∈box M,∑l∈actualClass s ha ω₁ ω₂ ψ χ₀ Q m t Kc R H n,
        classWeight S Kc l n*‖classBlock S β ψ χ₀ Q m t Kc R l n‖ :=
      splitLabel_le_classes S β ψ χ₀ Q m t Kc R H hKc M hbox
    _ ≤ ∑n∈box M,Cg*((rs.vol/θ.a^2)*Mm*B₀)*(heightEnvelope t^J*profileMoment J)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hclass P ξ Q m hm hl h2 hQ72 hQ χ₀ s ha rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂
        hV₀ hCR hcan t Kc R H n hKc hkLog hcut hholes hR₀ Xcol hX hbudget Mm hmult B₀ hB₀ (hseam n hn)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring

#print axioms actual_class_bound
#print axioms actual_split_bound
end
end QRH.Cycle092.RegularPhysicalClassBudget
