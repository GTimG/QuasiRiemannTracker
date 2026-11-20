/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Independent ordinary colors survive the native twin packing and source-to-frame map. -/
import Candidate.C092.transport.ColoredGaussFrameProviderReindex
import Lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredGaussFrameProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
open QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) packingSumDecEq {κ κ₂ : Type*} : DecidableEq (κ⊕κ₂) := Classical.decEq _

/-- Coprimality is extracted from a genuinely nonzero colored tuple, rather
    than inferred from the uncolored aggregate. -/
theorem originalColumn_coprime (ω₁ ω₂ : Character) {α : Type*} [Fintype α]
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id) (ν : α→Id→ℂ)
    (Wslot : α→ℝ→ℂ) (P : α→ℝ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (I : Id) (h : frameOriginalColumn (idealCoeff ω₁) (idealCoeff ω₂) S H pool d hd R seed ν Wslot P
      W₁ W₂ b X₁ X₂ Y₁ Y₂ I≠0) : IsCoprime I R := by
  unfold frameOriginalColumn finiteColumnCoefficient at h
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hvI := (Finset.mem_filter.mp hv).2
  by_contra hc
  apply hne
  unfold profileCoefficient
  rw [hvI,if_neg hc]
  ring
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentCompleteCommon
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open Candidate.FourthPower

/-- Genuine colored common labels inherit cube-freeness from actual tuple witnesses. -/
theorem common_powerFree (ω₁ ω₂ : Character) {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a)
    (p : commonLabels (supportedColumns (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))
      (supportedColumns (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))) :
    SexticSieve.PowerFree 3 p.val.1 ∧ SexticSieve.PowerFree 3 p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have hi := hI.1
  have hj := hJ.1
  unfold RootColoredSeed.active at hi hj
  rw [mem_activeSource] at hi hj
  have hfI := TwistedRawBall.source_fifth_free s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 q.1 hi.2
  have hfJ := TwistedRawBall.source_fifth_free s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 q.2 hj.2
  rw [←he]
  exact ⟨fun P hP hd=>hfI P hP (hd.trans (commonPart_dvd q.1 q.2 hI.2.1)),
    fun P hP hd=>hfJ P hP (hd.trans (commonPart_dvd q.2 q.1 hJ.2.1))⟩

theorem lab_cubeFree (ω₁ ω₂ : Character) {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a)
    (l : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))) :
    QRH.SilDensitySplit.CubeFree.Packet.CubeFreeCommon l.1.val.1 l.1.val.2 := by
  intro P
  have hf := common_powerFree ω₁ ω₂ s ha l.1
  have hd := commonLabels_data _ _ l.1.val.1 l.1.val.2 l.1.property
  have h1 := leftExponent_pos l.1.val.1 l.1.val.2 P
  have h2 := rightExponent_pos l.1.val.1 l.1.val.2 P
  have hl := (QRH.SilDensitySplit.CubeFree.FP.KernelIdeal.powerFree_iff_valuations hd.1).mp hf.1 P.val
  have hr := (QRH.SilDensitySplit.CubeFree.FP.KernelIdeal.powerFree_iff_valuations hd.2.1).mp hf.2 P.val
  simp only [QRH.Record1252270103KernelMass.valuation,factorization_eq_count] at hl hr
  unfold leftExponent rightExponent CenteredExceptionalCount.valuation at *
  omega

theorem lab_cube_rad (ω₁ ω₂ : Character) {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a)
    (l : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))) :
    l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2 ∧
      l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2 := by
  have hd := commonLabels_data _ _ l.1.val.1 l.1.val.2 l.1.property
  have hcf := lab_cubeFree ω₁ ω₂ s ha l
  have hcount : ∀ (left : Bool) (Q : Id), Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors
      (if left then l.1.val.1 else l.1.val.2)) ≤ 2 := by
    intro left Q
    by_cases hQ : Q ∈ CenteredMomentCompleteCommon.commonSupport l.1.val.1 l.1.val.2
    · have h := hcf ⟨Q, hQ⟩
      cases left
      · have hv : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.2) = 1 ∨
            Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.2) = 2 := h.2
        simp only [Bool.false_eq_true, ite_false]
        omega
      · have hv : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.1) = 1 ∨
            Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors l.1.val.1) = 2 := h.1
        simp only [ite_true]
        omega
    · have hz : Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors
          (if left then l.1.val.1 else l.1.val.2)) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        apply hQ
        unfold CenteredMomentCompleteCommon.commonSupport
        have hs : (QRH.Record1252270103KernelMass.primeSupport l.1.val.1 : Finset Id) =
            QRH.Record1252270103KernelMass.primeSupport l.1.val.2 := hd.2.2
        cases left
        · simp only [Bool.false_eq_true, ite_false] at hmem
          have h2 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2 := Multiset.mem_toFinset.mpr hmem
          have h1 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1 := by
            have : Q ∈ (QRH.Record1252270103KernelMass.primeSupport l.1.val.2 : Finset Id) := h2
            rw [← hs] at this; exact this
          exact Finset.mem_inter.mpr ⟨h1, h2⟩
        · simp only [ite_true] at hmem
          have h1 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1 := Multiset.mem_toFinset.mpr hmem
          have h2 : Q ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2 := by
            have : Q ∈ (QRH.Record1252270103KernelMass.primeSupport l.1.val.1 : Finset Id) := h1
            rw [hs] at this; exact this
          exact Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [hz]; omega
  exact ⟨QRH.SilDensitySplit.CubeFree.Second.Provider.dvd_rad_sq hd.1 (hcount true), QRH.SilDensitySplit.CubeFree.Second.Provider.dvd_rad_sq hd.2.1 (hcount false)⟩


open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentRestrictedSourceNormalization

theorem rawEnergy_nonneg (ω₁ ω₂ : Character) {L : ℝ} {θ : GData L} {mesh Z : ℝ}
    (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η r x) (v : ℝ) :
    0≤frameRawEnergy ω₁ ω₂ η r x h v := by
  unfold frameRawEnergy frameLabelEnergy
  exact sourceRestrictedEnergy_nonneg _ _ _ _ _ _ (dyadicScale_pos _) (fun _=>ballProfile_nonneg _)

end
end QRH.Cycle092.ColoredGaussFrameProvider

open Lean Meta Elab Command
private def liftFrame (src dst : Name) : CommandElabM Unit := do
  liftTermElabM do
    let cty ← Term.elabTerm (← `(OAI.SevenEighths.HeckeFamily.Character)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let cty ← instantiateMVars cty
    withLocalDeclD `ω₁ cty fun w1 => withLocalDeclD `ω₂ cty fun w2 => do
      let c1 ← mkAppM `OAI.SevenEighths.HeckeFamily.idealCoeff #[w1]
      let c2 ← mkAppM `OAI.SevenEighths.HeckeFamily.idealCoeff #[w2]
      let f1 ← mkAppM `DFunLike.coe #[c1]
      let f2 ← mkAppM `DFunLike.coe #[c2]
      let ci ← getConstInfo src
      let trans (e : Expr) : MetaM Expr := Core.transform e (post := fun e => do
        let f := e.getAppFn
        let args := e.getAppArgs
        let .const n ls := f | return .done e
        let p := `QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
        let a := `QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
        let q := `QRH.Cycle092.ColoredGaussFrameProvider
        let table := #[
          (`QRH.SilDensitySplit.CubeFree.FP.MixedHeightEnergy.originalColumn,
            `QRH.Cycle092.RegularColoredForward.frameOriginalColumn,2,#[c1,c2]),
          (`QRH.SilDensitySplit.CubeFree.Packet.Reduce.labelEnergy,
            `QRH.Cycle092.RegularColoredForward.frameLabelEnergy,16,#[w1,w2]),
          (`QRH.SilDensitySplit.CubeFree.FP.MixedPrincipalWindow.sourceCoefficient,
            `QRH.Cycle092.TwistedRawSource.sourceColumn,6,#[f1,f2]),
          (`QRH.SilDensitySplit.CubeFree.Packet.Grouped.rawEnergy,
            `QRH.Cycle092.RegularColoredForward.frameRawEnergy,4,#[w1,w2]),
          (`QRH.SilDensitySplit.CubeFree.Packet.Grouped.gEnergy,
            `QRH.Cycle092.RegularColoredForward.framegEnergy,4,#[w1,w2]),
          (`QRH.SilDensitySplit.CubeFree.Packet.Grouped.gFrame,
            `QRH.Cycle092.RegularColoredForward.frameSideFrame,3,#[w1,w2]),
          (`QRH.SilDensitySplit.CubeFree.Packet.Grouped.rawEnergy_nonneg,
            q ++ `rawEnergy_nonneg,0,#[w1,w2]),
          (a ++ `frame_ratio,q ++ `frame_ratio,0,#[w1,w2]),
          (a ++ `pointwise_ratio,q ++ `pointwise_ratio,0,#[w1,w2]),
          (a ++ `source_le_frame,q ++ `source_le_frame,0,#[w1,w2]),
          (a ++ `weighted_column_bound_mult,q ++ `weighted_column_bound_mult,0,#[w1,w2]),
          (a ++ `column_hyp,q ++ `column_hyp,0,#[w1,w2]),
          (a ++ `originalColumn_coprime,q ++ `originalColumn_coprime,0,#[w1,w2]),
          (a ++ `zeroPrimes_side,q ++ `zeroPrimes_side,0,#[w1,w2]),
          (a ++ `labelEnergy_packed_col,q ++ `labelEnergy_packed_col,0,#[w1,w2]),
          (p ++ `labelEnergy_congr,q ++ `labelEnergy_congr,0,#[w1,w2]),
          (a ++ `labelEnergy_source,q ++ `labelEnergy_source,15,#[w1,w2]),
          (`QRH.SilDensitySplit.CubeFree.Second.Concrete.S0,
            `QRH.Cycle092.RootColoredSeed.active,6,#[f1,f2]),
          (`QRH.SilDensitySplit.CubeFree.Second.Provider.lab_cubeFree,
            q ++ `lab_cubeFree,0,#[w1,w2])]
        for (old,new,idx,colors) in table do
          if n==old && args.size>=idx then
            return .done (mkAppN (.const new ls) (args[:idx].toArray ++ colors ++ args[idx:].toArray))
        return .done e)
      let ty ← trans ci.type
      unless (ty.find? (· == w1)).isSome && (ty.find? (· == w2)).isSome do
        throwError "both colors must occur in {src}"
      let some value := ci.value? true | throwError "no proof {src}"
      let value ← trans value
      let ty ← mkForallFVars #[w1,w2] ty
      let value ← mkLambdaFVars #[w1,w2] value
      let ty ← instantiateMVars ty
      let value ← instantiateMVars value
      addDecl (.thmDecl {name:=dst,levelParams:=ci.levelParams,type:=ty,value:=value})

run_cmd do
  liftFrame `QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame.labelEnergy_congr
    `QRH.Cycle092.ColoredGaussFrameProvider.labelEnergy_congr
  for n in #[`zeroPrimes_side,`labelEnergy_packed_col,`source_le_frame,
      `frame_ratio,`pointwise_ratio,`weighted_column_bound_mult,`column_hyp,`class_label_bound] do
    liftFrame (`QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly ++ n)
      (`QRH.Cycle092.ColoredGaussFrameProvider ++ n)

#print axioms QRH.Cycle092.ColoredGaussFrameProvider.common_powerFree
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.lab_cube_rad
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.labelEnergy_congr
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.labelEnergy_packed_col
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.source_le_frame

#print axioms QRH.Cycle092.ColoredGaussFrameProvider.frame_ratio
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.column_hyp
#print axioms QRH.Cycle092.ColoredGaussFrameProvider.class_label_bound
