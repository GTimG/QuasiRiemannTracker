/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Fixed one-sided source energy and its genuine packed twin on native labels.
The keep is the actual inducing classifier, never the regular complement. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerSource
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

/-- The original fixed row selector reduces to the actual family character.
The nonzero condition is retained through the same reduction. -/
lemma family_fixed_keep {ψ : Character} {C D : Id} {hC : Supported C} {hD : Supported D}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)} {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family ψ C D hC hD U τ) (χ : RayFourExpansion.RayCharacter) (Q : Id)
    (m : O) (hm : m≠0) (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m) :
    fixedKeep ψ χ Q m (secondTwist C D U)=initialFixed (τ χ) Q := by
  funext z
  apply propext
  by_cases hz:z=0
  · simp [fixedKeep,initialFixed,hz]
  · exact and_congr Iff.rfl (hfam.inducing_iff χ Q m z hm hz hl h2)

/-- Literal fixed source energy enters the unchanged native label. The proof
uses the actual colored zero extension, true twin, and honest raised radius. -/
theorem source_le_frame {η : Character} (P : SidePack η) (ξ : RayFourExpansion.RayCharacter)
    {C₂ D₂ : Id} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CenteredMomentCanonicalFirst.CommonIndex C₂ D₂)} {τ : RayFourExpansion.RayCharacter→Character}
    (hfam : Family (childCharacter P.base ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayFourExpansion.RayCharacter)
    (G : Id) (hGs : Supported G) (hGc : ∀I,IsCoprime G I → IsCoprime C₂ I ∨ IsCoprime D₂ I)
    (Q : Id) (m : O) (hm : m≠0) (hl : ConcretePrimeRowBridge.goodLambda∣m) (h2 : (2:O)∣m)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ : Character) (rs : GSrc θ mesh Z)
    (hV₀ : rs.V₀=P.V) (hCR : P.Cs∣s.R)
    (x : LabelData) (hj : x.j=P.j₀*ξ*χ) (hA : x.A₂=secondTwist C₂ D₂ U)
    (hxG : x.G=G) (hseed : x.seed=1) (hx : x.Good rs)
    (S : Finset Id) (hSs : S⊆sourceColumns s)
    (hSz : ∀I∈sourceColumns s,I∉S → sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 I=0)
    (Hs : ℝ) (hH : 0<Hs) (hHk : 2*Hs  ≤  dyadicScale (x.n 1)) (v : ℝ) :
    sourceRestrictedEnergy (fixedKeep (childCharacter P.base ξ) χ Q m (secondTwist C₂ D₂ U))
      (residualPool G hGs.1 S)
      (fun I=>if IsCoprime G I ∧ x.D∣I then sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)
      (heightCoeff (τ χ) v) ballProfile Hs  ≤ 
      rawEnergy s ha ω₁ ω₂ η rs (x.toLabel η) (toLabel_fits η rs x hx) Q v := by
  rw [sourceRestrictedEnergy_pool_eq _ _ _ (residualPool_mono G hGs.1 hSs) _ _ (by
    intro I hI hnI
    rw [mem_residualPool] at hI
    have hnI' : G*I∉S := fun h=>hnI ((mem_residualPool G hGs.1 S I).mpr h)
    by_cases hc:IsCoprime G I ∧ x.D∣I
    · rw [if_pos hc,hSz _ hI hnI']
    · rw [if_neg hc])]
  rw [family_fixed_keep hfam χ Q m hm hl h2]
  refine (QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup.sourceRestrictedEnergy_radius_le _ _ _ _ _ _ hH
    (dyadicScale_pos _) hHk).trans (le_of_eq ?_)
  rw [source_packed_col P ξ hfam χ G hGs hGc s ha ω₁ ω₂ Q x.D _ v hCR]
  unfold rawEnergy
  simp only [LabelData.toLabel]
  simp only [hj,hA,hV₀,hxG,hseed]

lemma gEnergy_nonneg (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (Q : Id) (x : GLabel θ mesh Z) (v : ℝ) :
    0 ≤ gEnergy s ha ω₁ ω₂ η rs Q x v := by
  have hn : 0 ≤ rs.norm := by
    unfold GSrc.norm
    exact div_nonneg (Real.rpow_nonneg (zero_lt_one.trans rs.hZ).le _) (sq_nonneg _)
  unfold gEnergy
  split_ifs with h
  · exact mul_nonneg (by positivity) (rawEnergy_nonneg s ha ω₁ ω₂ η rs x h Q v)
  · rfl

lemma pointwise_ratio (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a) (ω₁ ω₂ η : Character)
    (rs : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η rs x) (Q : Id)
    (w src Λ v : ℝ) (hw0 : 0 ≤ w)
    (hw : w ≤ Λ*(rho x.common*‖x.prefactor‖*(x.G.absNorm:ℝ)*
      ((x.d.1.absNorm:ℝ)*(x.d.2.absNorm:ℝ))*rs.norm))
    (hsrc0 : 0 ≤ src) (hsrc : src ≤ rawEnergy s ha ω₁ ω₂ η rs x h Q v) :
    w*src ≤ Λ*(gWeight x*gEnergy s ha ω₁ ω₂ η rs Q x v) := by
  rw [frame_ratio s ha ω₁ ω₂ η rs x h Q v]
  calc
    _  ≤  (Λ*(rho x.common*‖x.prefactor‖*(x.G.absNorm:ℝ)*
      ((x.d.1.absNorm:ℝ)*(x.d.2.absNorm:ℝ))*rs.norm))*rawEnergy s ha ω₁ ω₂ η rs x h Q v :=
      mul_le_mul hw hsrc hsrc0 (hw0.trans hw)
    _ = _ := by ring

/-- Original image multiplicity is paid once, independently of row packing. -/
theorem weighted_column_bound_mult {K : Type*} (s : Source (Fin θ.N) θ.a θ.b)
    (ha : 0<θ.a) (ω₁ ω₂ η : Character) (rs : GSrc θ mesh Z) (Q : Id)
    (Ks : Finset K) (wt : K→ℝ) (src : K→ℝ→ℝ) (X : K→GLabel θ mesh Z)
    (M : ℕ) (hM : ∀y∈Ks.image X,(Ks.filter (fun k=>X k=y)).card  ≤  M)
    (Λ B : ℝ) (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) (J : ℕ)
    (hratio : ∀k∈Ks,∀v,wt k*src k v ≤ Λ*(gWeight (X k)*gEnergy s ha ω₁ ω₂ η rs Q (X k) v))
    (hseam : ∀v,∑x∈Ks.image X,gWeight x*gEnergy s ha ω₁ ω₂ η rs Q x v ≤ B*(1+‖v‖)^(2*J)) :
    ∀v,∑k∈Ks,wt k*src k v ≤ (Λ*M*B)*(1+‖v‖)^(2*J) := by
  intro v
  have hnn : ∀y,0 ≤ gWeight y*gEnergy s ha ω₁ ω₂ η rs Q y v :=
    fun y=>mul_nonneg (gWeight_nonneg y) (gEnergy_nonneg s ha ω₁ ω₂ η rs Q y v)
  calc
    _  ≤  ∑k∈Ks,Λ*(gWeight (X k)*gEnergy s ha ω₁ ω₂ η rs Q (X k) v) := Finset.sum_le_sum (fun k hk=>hratio k hk v)
    _ = Λ*∑y∈Ks.image X,((Ks.filter (fun k=>X k=y)).card:ℝ)*(gWeight y*gEnergy s ha ω₁ ω₂ η rs Q y v) := by
      rw [←Finset.mul_sum,Finset.sum_image' (fun k=>gWeight (X k)*gEnergy s ha ω₁ ω₂ η rs Q (X k) v)]
      intro y hy
      rw [Finset.sum_congr rfl (fun k hk=>by rw [(Finset.mem_filter.mp hk).2]),Finset.sum_const,nsmul_eq_mul]
    _  ≤  Λ*∑y∈Ks.image X,(M:ℝ)*(gWeight y*gEnergy s ha ω₁ ω₂ η rs Q y v) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y hy=>mul_le_mul_of_nonneg_right (by exact_mod_cast hM y hy) (hnn y))) hΛ
    _  ≤  Λ*(M*(B*(1+‖v‖)^(2*J))) := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hseam v) (Nat.cast_nonneg _)) hΛ
    _ = _ := by ring

#print axioms source_le_frame
#print axioms weighted_column_bound_mult
end QRH.Cycle092.FixedPhysicalClassLedger
