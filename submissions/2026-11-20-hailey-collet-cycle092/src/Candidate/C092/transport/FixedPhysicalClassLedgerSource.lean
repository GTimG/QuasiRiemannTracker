/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Fixed one-sided source energy and its genuine packed twin on native labels.
The keep is the actual inducing classifier, never the regular complement. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerClasses
import Candidate.C092.transport.ColoredGaussFrameProviderActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentChildRows CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentNaturalFixedRaySource
open QRH.SilDensitySplit.CubeFree
open CenteredMomentRestrictedSourceNormalization CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.Cycle092.TwistedRawSource QRH.Cycle092.RegularColoredForward
namespace QRH.Cycle092.FixedPhysicalClassLedger
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- The literal fixed half of the canonical nonzero row partition. -/
def initialFixed (τ : Character) (Q : Id) (z : O) : Prop :=
  z≠0 ∧ FixedInducingRow τ Q fixedBadMask 1 z

lemma initialFixed_congr (τ τ' : Character) (Q : Id) (wm : O) (hwm : wm≠0)
    (hcoef : ∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) → idealCoeff τ I=idealCoeff τ' I) :
    initialFixed τ Q=initialFixed τ' Q := by
  have hr := keep_congr τ τ' Q (fun _=>0) wm hwm hcoef
  funext z
  apply propext
  by_cases hz:z=0
  · simp [initialFixed,hz]
  · have hh := Iff.of_eq (congrFun hr z)
    change (z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z) ↔
      (z≠0 ∧ ¬FixedInducingRow τ' Q fixedBadMask 1 z) at hh
    have hn : ¬FixedInducingRow τ Q fixedBadMask 1 z ↔ ¬FixedInducingRow τ' Q fixedBadMask 1 z :=
      ⟨fun h=>(hh.mp ⟨hz,h⟩).2,fun h=>(hh.mpr ⟨hz,h⟩).2⟩
    have hh' := not_iff_not.mp hn
    exact and_congr Iff.rfl hh'

/-- Character transport is proved on the same masked colored coefficients. -/
lemma source_energy_congr (τ τ' : Character) (Q : Id) (S : Finset Id) (c : Id→ℂ)
    (wm : O) (hwm : wm≠0)
    (hcoef : ∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) → idealCoeff τ I=idealCoeff τ' I)
    (hcol : ∀I∈S,Supported I → c I≠0 → IsCoprime I (Ideal.span {wm}))
    (H v : ℝ) :
    sourceRestrictedEnergy (initialFixed τ Q) S c (heightCoeff τ v) ballProfile H=
      sourceRestrictedEnergy (initialFixed τ' Q) S c (heightCoeff τ' v) ballProfile H := by
  unfold sourceRestrictedEnergy
  rw [initialFixed_congr τ τ' Q wm hwm hcoef]
  congr 1
  funext I
  have hs := (Finset.mem_filter.mp I.property).2
  by_cases hz:c I=0
  · simp only [hz,zero_mul]
  · unfold heightCoeff
    rw [hcoef I hs (hcol I (Finset.mem_filter.mp I.property).1 hs hz)]

/-- The fixed raw row energy is the actual source polynomial on the native
label’s G/divisor/prefix data, including its genuine ball profile. -/
def rawEnergy (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η rs x) (Q : Id) (v : ℝ) : ℝ :=
  sourceRestrictedEnergy (initialFixed (x.char rs) Q) (residualPool x.G h.G_ne (sourceColumns s))
    (fun I=>if IsCoprime x.G I ∧ x.D∣I then
      sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) x.seed (x.G*I) else 0)
    (heightCoeff (x.char rs) v) ballProfile (dyadicScale (x.n 1))

def gEnergy (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (v : ℝ) : ℝ :=
  if h:Fits η rs x then (x.G.absNorm:ℝ)*(x.D.absNorm:ℝ)*
    ((x.d.1.absNorm:ℝ)*(x.d.2.absNorm:ℝ))*rs.norm*rawEnergy s ha ω₁ ω₂ η rs x h Q v else 0

lemma rawEnergy_nonneg (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η rs x) (Q : Id) (v : ℝ) :
    0≤rawEnergy s ha ω₁ ω₂ η rs x h Q v :=
  sourceRestrictedEnergy_nonneg _ _ _ _ _ _ (dyadicScale_pos _) (fun _=>ballProfile_nonneg _)

/-- The artificial divisor cancels precisely once against native gWeight. -/
lemma frame_ratio (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η rs x) (Q : Id) (v : ℝ) :
    gWeight x*gEnergy s ha ω₁ ω₂ η rs Q x v=
      rho x.common*‖x.prefactor‖*(x.G.absNorm:ℝ)*((x.d.1.absNorm:ℝ)*(x.d.2.absNorm:ℝ))*rs.norm*
        rawEnergy s ha ω₁ ω₂ η rs x h Q v := by
  have hD : (x.D.absNorm:ℝ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr h.D_sq.ne_zero
  unfold gWeight gEnergy
  rw [dif_pos h]
  field_simp

/-- The same actual fixed source energy is the packed twin energy. -/
theorem source_packed_col {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C₂ D₂ : Id} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C₂ D₂)} {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hGs : Supported G) (hGc : ∀I,IsCoprime G I → IsCoprime C₂ I ∨ IsCoprime D₂ I)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character)
    (Q D : Id) (H v : ℝ) (hCR : P.Cs∣s.R) :
    sourceRestrictedEnergy (initialFixed (τ χ) Q) (residualPool G hGs.1 (sourceColumns s))
      (fun I=>if IsCoprime G I ∧ D∣I then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)
      (heightCoeff (τ χ) v) ballProfile H=
    sourceRestrictedEnergy (initialFixed (packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C₂ D₂ U)) Q)
      (residualPool G hGs.1 (sourceColumns s))
      (fun I=>if IsCoprime G I ∧ D∣I then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)
      (heightCoeff (packedChar η (P.j₀*ξ*χ) (P.V*secondTwist C₂ D₂ U)) v) ballProfile H := by
  have hV := mul_ne_zero P.hV (secondTwist_ne_zero C₂ D₂ hC₂ U)
  apply source_energy_congr _ _ Q _ _ (packMask P.Z₀ G) (packMask_ne_zero _ _ P.hZ₀ hGs)
  · intro I hI hw
    obtain ⟨hz,hc⟩ := packMask_coprime _ _ I hw
    have h1 := second_packed_side P ξ hfam χ I hI hz (hGc I hc) 0
    rw [Packet.heightCoeff_zero,Packet.heightCoeff_zero] at h1
    rw [h1,packedChar_coef η _ _ hV I hI]
  · intro I hI hs hc
    have hmask : IsCoprime G I ∧ D∣I := by
      by_contra hn
      exact hc (if_neg hn)
    have h0 : sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)≠0 := by
      simpa only [if_pos hmask] using hc
    have hcop := ColoredGaussFrameProvider.originalColumn_coprime ω₁ ω₂
      s.S s.H s.pool s.d s.hd s.R 1 s.ν s.Wslot s.P _ _ θ.b s.X₁ s.X₂ s.Y₁ s.Y₂ (G*I)
      (by rwa [←ColoredGaussFrameProvider.sourceColumn_original s ha (idealCoeff ω₁) (idealCoeff ω₂) 1])
    have hz := P.zcop I ((hcop.of_isCoprime_of_dvd_right hCR).of_mul_left_right)
    rw [packMask,ConcretePrimeRowBridge.span_idealGenerator]
    exact IsCoprime.mul_right hz hmask.1.symm

#print axioms initialFixed_congr
#print axioms source_packed_col
#print axioms frame_ratio
end QRH.Cycle092.FixedPhysicalClassLedger
