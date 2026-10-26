import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildProfiles
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowProfileCommon
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowCommon
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound for the final daughters of a LOW child through both allocation layers, with the returned part of the
daughter that attains the largest one. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- A finite family of bounds, each with a returned part that is zero or of a given kind, has a common returned part
of the same kind that bounds all of them. -/
theorem exists_returned_max {ι : Type*} [Finite ι] (valid : ι → Prop) (Good : ℝ → Prop) (hGood : Good 0)
    (Φ : ι → ℝ → Prop) (hΦ : ∀ t r r', Φ t r → r ≤ r' → Φ t r')
    (hday : ∀ t, valid t → ∃ r, 0 ≤ r ∧ Good r ∧ Φ t r) :
    ∃ R, 0 ≤ R ∧ Good R ∧ ∀ t, valid t → Φ t R := by
  by_cases hne : Nonempty ι
  · let f : ι → ℝ := fun t => if h : valid t then Classical.choose (hday t h) else 0
    have hf : ∀ t, 0 ≤ f t ∧ Good (f t) ∧ (valid t → Φ t (f t)) := by
      intro t
      by_cases h : valid t
      · have hspec := Classical.choose_spec (hday t h)
        have hft : f t = Classical.choose (hday t h) := by simp only [f, h, ↓reduceDIte]
        rw [hft]
        exact ⟨hspec.1, hspec.2.1, fun _ => hspec.2.2⟩
      · have hft : f t = 0 := by simp only [f, h, ↓reduceDIte]
        rw [hft]
        exact ⟨le_rfl, hGood, fun h' => absurd h' h⟩
    obtain ⟨t₀, ht₀⟩ := Finite.exists_max f
    exact ⟨f t₀, (hf t₀).1, (hf t₀).2.1, fun t ht => hΦ _ _ _ ((hf t).2.2 ht) (ht₀ t)⟩
  · exact ⟨0, le_rfl, hGood, fun t => absurd ⟨t⟩ hne⟩

/-- The bound for the final daughters of a LOW child through both allocation layers, over the dyadic ideals `Ds`.
The returned part is that of one daughter, the largest, and is chosen before the rows `zs`. -/
def LowCommonStmt [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Kcls : ℝ, ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C
      g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*unit+ξ/2
    let padding := omega+εpad*unit
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z≤pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0≤Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1≤Z^L) →
    ∀(v₁ : O)(Tz : ℝ),
      (∀(W' : ℝ)(hW' : st.width≤W'),Presented η₀ Z (widenState st W' hW') v₁ Tz) →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∃Ret : ℝ,0≤Ret ∧
      ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ st.rowWidth lossFloor
        (Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-unit*Cycle63.Optimization.fixedDeletion cell+gridSlack)
        (unit*Cycle63.Optimization.secondAmp cell+ampSlack) Kcls
        (Z^(2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh)))
        Ret ∧
    ∀(zs : Finset O)(weight : O→ℝ),
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z)≤
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(2*εshell)*
        (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
          rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)*Z^pad

/-- The bound for one final daughter of a LOW child controlled by the original plain profiles gives the bound for the
final daughters through both allocation layers. -/
theorem lowCommon_of_profiles [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (εshell : ℝ) (heshell : 0<εshell)
    (hprofiles : LowProfilesStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad
      Mmin Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented) :
    LowCommonStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell
      Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented := by
  choose Ks hKs hcommon using fun J : Finset α=>actual_common_low_energy (ι:=↥J) bs εshell heshell
  let Kall := 1+∑J : Finset α,Ks J
  have hKall : 0<Kall := by
    dsimp [Kall]
    have hh : 0≤∑J : Finset α,Ks J := Finset.sum_nonneg (fun J _=>(hKs J).le)
    linarith
  have hKle (J : Finset α) : Ks J≤Kall := by
    have hh := Finset.single_le_sum (fun J (_ : J∈Finset.univ)=>(hKs J).le) (Finset.mem_univ J)
    dsimp [Kall]; linarith
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,Sp,Kcls,C,hC,hbound⟩ := hprofiles η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,Sp,Kcls,Kall*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps v₁ Tz hpres
    hQM' hQη low
  let exponent : ℝ := nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+
    2*ε*d*(Fintype.card α:ℝ)+rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hZE : 0≤Z^exponent := Real.rpow_nonneg (zero_le_one.trans hZone.le) _
  -- the returned part of the largest final daughter
  let ι := Σ(B₂ : ↥(actualAllocations src.pools q.E₂)),Σ(D : ↥Ds),
    Σ(a : ↥((commonData src q.E₂ q.R₂ B₂).toSource.active D.1)),Bool
  obtain ⟨R,hR0,hRgood,hRle⟩ := exists_returned_max (ι:=ι)
    (fun t => commonScalar src q.E₂ q.R₂ t.1≠0)
    (fun r => ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ st.rowWidth lossFloor
        (Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-unit*Cycle63.Optimization.fixedDeletion cell+gridSlack)
        (unit*Cycle63.Optimization.secondAmp cell+ampSlack) Kcls
        (Z^(2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh)))
        r)
    (ReturnedClause.zero AllowRet base η₀ Z Bnorm Tz v₁ _ _ _ _ _ _)
    (fun t r => finalPositiveEnergy (commonData src q.E₂ q.R₂ t.1) t.2.2.2 t.2.1.1 t.2.2.1.1
        (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      C*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(Z^exponent+r))
    (fun t r r' h hrr => le_trans h (by gcongr))
    (by
      intro t hn
      let q' : Chain s := { q with B₂:=t.1 }
      have hB₂ : frozenCoefficient t.1.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0 :=
        right_ne_zero_of_mul hn
      let g' : LiveMainGeometry s q' Z Mrow amp omega ξ bs (Fintype.card α) :=
        { reflected:=g.reflected, C₀:=g.C₀, D₀:=g.D₀, hC₀:=g.hC₀, hD₀:=g.hD₀,
          heq₀:=g.heq₀, selected:=g.selected, E₀:=g.E₀, hmod:=g.hmod,
          δ:=g.δ, reserve:=g.reserve, homega:=g.homega, datum:=g.datum,
          parent:=g.parent, row:=g.row, radius_eq:=g.radius_eq, label:=g.label,
          first_nonzero:=g.first_nonzero, second_nonzero:=hB₂ }
      exact hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
        hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
        unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q' g' χ hP hPN t.2.2.2 t.2.1.1 t.2.2.1.1 p₀ hp₁ hp₂
        (hcaps t.1 hn t.2.1.1 t.2.1.2 t.2.2.1.1 t.2.2.1.2 t.2.2.2).1
        (hcaps t.1 hn t.2.1.1 t.2.1.2 t.2.2.1.1 t.2.2.1.2 t.2.2.2).2 v₁ Tz hpres)
  refine ⟨R,hR0,hRgood,?_⟩
  intro zs weight hkeep hweight
  let E := C*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*(Z^exponent+R)
  have hE : 0≤E := by dsimp [E]; positivity
  have henergy (B₂ : actualAllocations src.pools q.E₂)(hn : commonScalar src q.E₂ q.R₂ B₂≠0)
      (D : Ideal O)(hD : D∈Ds)
      (alloc : Allocation D (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
      (halloc : alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D)(second : Bool) :
      finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
        (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤E :=
    hRle ⟨B₂,⟨D,hD⟩,⟨alloc,halloc⟩,second⟩ hn
  have hC₂ : q.E₂≠0 := CenteredMomentAllocatedNaturalRadial.common_nonzero q.first q.E₂ q.B₂
  have hh := hcommon (liveIndices q.B₁.val) src hsupper q.E₂ q.R₂ hC₂ Ds zs weight
    T Z pad E hT hZone hE hDs (fun z=>st.radial.keep z ∧ low z)
    st.radial.profile st.radial.scale st.radial.scale_pos (fun z _=>st.radial.nonneg z)
    hkeep hweight hallow henergy
  apply hh.trans
  have hp:=src.toData.profile_nonneg
  have hn:=CenteredMomentFirstScale.norm_pos q.E₂ hC₂
  calc
    _≤Kall*src.toData.profileFactor*(∏j,src.M j)^2*E*(q.E₂.absNorm:ℝ)^(εshell-1)*
        (2*T)^(2*εshell)*Z^pad := by
      gcongr
      exact hKle _
    _=_ := by dsimp [E,exponent]; ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
