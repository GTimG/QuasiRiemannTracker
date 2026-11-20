/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Hidden actual class preimages and authentic pointwise H15 row witnesses. -/
import Candidate.C092.transport.FixedFrameRowWitnessLabel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedFrameRowWitness
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization CenteredMomentRowNorm CenteredMomentSecondSectorColumns
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentSourceRow CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

lemma sourcePrefix_eq_native (s : Source (Fin θ.N) θ.a θ.b) (x : GLabel θ mesh Z)
    (hd : x.d=s.d) : sourcePrefix s x.G x.D=FixedFramePacking.prefixNorm x := by
  unfold sourcePrefix FixedFramePacking.prefixNorm
  rw [hd]
  ring

lemma sourceVolume_eq_native (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z)
    (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d) :
    FixedFourierH15.sourceVolume s=rs.vol := by
  unfold FixedFourierH15.sourceVolume GSrc.vol
  rw [hX₁,hX₂,s.hpX]
  simp only [hcan.P]

/-- An actual nonzero fixed summand supplies its hidden native class and
    divisor, real Family.height_eq and exact H15 datum at this SAME z.
    No equality of tsums is used and Fits is recovered from the nonzero row. -/
theorem actual_row_witness {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z)
    (hX₁ : rs.X₁=s.X₁) (hX₂ : rs.X₂=s.X₂)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d)
    (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R) (χ₀ : RayFourExpansion.RayCharacter)
    (Q : Id) (hQ : Q≠0) (m : O) (t Kc R H : ℝ)
    (g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id)
    (hg : IsColumn (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)) g)
    (n : Fin 4→ℤ) (χ : RayFourExpansion.RayCharacter)
    (x : GLabel θ mesh Z)
    (hx : x∈FixedPhysicalClassLedger.actualFrameLabels η s ha ω₁ ω₂ (childCharacter P.base ξ)
      χ₀ Q m t Kc R H rs P.j₀ ξ g n χ) (v : ℝ) (z : O)
    (hne : FixedPhysicalClassLedger.rowEnergy s ha ω₁ ω₂ η rs Q x v z≠0) :
    let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
    ∃(l : Lab S)(E : Id),
      l∈FixedPhysicalClassLedger.actualClass s ha ω₁ ω₂ (childCharacter P.base ξ) χ₀ Q m t Kc R H n ∧
      E∈labelPool S l ∧
      x=(frameData P.j₀ ξ s rs S g n χ ⟨l,E⟩).toLabel η ∧
      x.G=g l ∧ x.D=E ∧ x.d=s.d ∧ x.seed=1 ∧
      sourcePrefix s x.G x.D=FixedFramePacking.prefixNorm x ∧ FixedFourierH15.sourceVolume s=rs.vol ∧
    ∃(hG : Supported x.G)(D : FixedCubeDatum),
      D.η=childCharacter (childCharacter P.base ξ) χ ∧ D.Q=Q ∧
      D.m=FixedCubeGauss.nativeSourceMask s ∧ D.A=lA S l ∧ D.z=z ∧
      (∀I : Id,Supported I → IsCoprime x.G I → ∀u,
        heightCoeff (famτ (childCharacter P.base ξ) S l χ) u I=
          heightCoeff (childCharacter P.base ξ) u I*CanonicalRowCompletion.idealRowHom D.A I*
            RayFourExpansion.rayCharacter χ (primaryGenerator I)) ∧
      FixedPhysicalClassLedger.rowEnergy s ha ω₁ ω₂ η rs Q x v z=
        ‖nativeRowPolynomial s ha D ω₁ ω₂ (childCharacter P.base ξ) χ x.G hG x.D v‖^2*
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (x.n 1))).re := by
  dsimp only
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
  have hf : Fits η rs ((frameData P.j₀ ξ s rs _ g n χ k).toLabel η) := by
    by_contra h
    exact hne (by simp only [FixedPhysicalClassLedger.rowEnergy,dif_neg h])
  have hz : FixedPhysicalClassLedger.initialFixed
      (((frameData P.j₀ ξ s rs _ g n χ k).toLabel η).char rs) Q z := by
    by_contra h
    exact hne (by simp only [FixedPhysicalClassLedger.rowEnergy,dif_pos hf,if_neg h])
  have hG : Supported (g k.1) := by
    rcases hg k.1 with h|h
    · rw [h];exact (lab_data _ k.1).1
    · rw [h];exact (lab_data _ k.1).2.1
  have hGc : ∀I,IsCoprime (g k.1) I → IsCoprime k.1.1.val.1 I ∨ IsCoprime k.1.1.val.2 I := by
    intro I hc
    rcases hg k.1 with h|h
    · exact Or.inl (h ▸ hc)
    · exact Or.inr (h ▸ hc)
  obtain ⟨D,hη,hDQ,hM,hA,hzD,hrow⟩ := label_row_witness P ξ
    (famSpec (childCharacter P.base ξ) _ k.1) χ (g k.1) hG hGc s ha ω₁ ω₂ rs hV₀ hCR Q hQ
    (frameData P.j₀ ξ s rs _ g n χ k) rfl rfl rfl rfl hf v z hz
  refine ⟨k.1,k.2,(Finset.mem_sigma.mp hk).1,(Finset.mem_sigma.mp hk).2,rfl,rfl,rfl,rfl,rfl,
    sourcePrefix_eq_native s _ rfl,sourceVolume_eq_native s rs hX₁ hX₂ hcan,hG,D,
    hη,hDQ,hM,hA,hzD,?_,?_⟩
  · intro I hI hc u
    rw [hA]
    exact (famSpec (childCharacter P.base ξ) _ k.1).height_eq χ I hI (hGc I hc) u
  · change _ = ‖nativeRowPolynomial s ha D ω₁ ω₂ (childCharacter P.base ξ) χ (g k.1) hG k.2 v‖^2*
      (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/dyadicScale (raisedN rs _ n k.1 1))).re
    simpa only [nativeRowBallEnergy,hzD,frameData,LabelData.toLabel] using hrow

#print axioms sourcePrefix_eq_native
#print axioms sourceVolume_eq_native
#print axioms actual_row_witness
end
end QRH.Cycle092.FixedFrameRowWitness
