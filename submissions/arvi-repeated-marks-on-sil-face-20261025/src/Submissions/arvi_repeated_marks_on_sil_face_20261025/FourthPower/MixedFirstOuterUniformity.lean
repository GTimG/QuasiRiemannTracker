/- Copyright (c) 2026 Sil. Apache-2.0.
The constants of the chosen energy bound precede the actual finite outer
supplier partition, its remaining slots, all source profiles and heights.
No analytic estimate is assumed; the checked independent-height bound is
applied to each of the finitely many outer live types.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstSourceWindow
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstReheight
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstCenteredSourceMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstOuterUniformity
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentNaturalFixedRaySource ReferencePrimeEnclosure
open MixedPrincipalPair MixedPrincipalWindow MixedCanonicalSource MixedSupplierSource
open MixedFirstGeometricCaps MixedInnerExceptionalBlock MixedFirstUniformLossBudget
open MixedFirstChosenEnergy MixedFirstProfileEnvelope MixedFirstAvoidance MixedFirstReheight
open MixedFirstActualNonexceptional MixedLiteralAllocation MixedPrincipalAllocations
open MixedFirstPhysicalApplication MixedFirstSeededEnergy
open MixedCompletedRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι]

abbrev OuterLive (L : Finset ι) := {i // i∉Lᶜ}

theorem outer_live_card (L : Finset ι) :
    Fintype.card (OuterLive L) ≤ Fintype.card ι :=
  Fintype.card_le_of_injective (fun i : OuterLive L=>i.val) Subtype.val_injective

/-- The actual remaining supplier type is precisely the complementary
finite subset of its fixed outer live type; no abstract universe reindex
or unrestricted replacement family is introduced. -/
theorem rest_type_eq (q : MixedSupplierFourthRow.Data ι) :
    RestIndex q = ↥(q.Jᶜ) := by
  change {j : OuterLive q.L // j∉q.J} = {j : OuterLive q.L // j∈q.Jᶜ}
  congr 1
  funext j
  exact propext Finset.mem_compl.symm

private theorem subtype_statement_transport {κ : Type u}
    (P : (p : κ → Prop) → Fintype (Subtype p) → Prop)
    {p q : κ → Prop} (h : p=q)
    (ip : Fintype (Subtype p)) (iq : Fintype (Subtype q))
    (hp : P p ip) : P q iq := by
  cases h
  have hi : ip=iq := Subsingleton.elim _ _
  cases hi
  exact hp


variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- One degree, seminorm family, constant and eventual threshold for every
outer partition and every further live subset. The explicit polynomial
height cost remains available to the later Fourier integration. -/
theorem uniform_chosen_outer_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b B Lslot Lcap Cap BR BH Bη lo hi cstar Kslot Bseed εfinal rho : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hB : 1≤B) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBη : 0≤Bη) (hCapb : b≤Cap) (hBcap : B≤Lcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hcstar : 0<cstar) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hεfinal : 0<εfinal) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed εfinal rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀L : Finset ι, ∀T : Finset (OuterLive L),
    ∀(θ : OuterLive L→RayQuotient.Characters M Hray)(w σ freq : OuterLive L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
      cstar*Z^(referenceExponent R P S d)≤s.L→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t₀ V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈MixedSupplierPositive.selectedProducts q,
          ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal := by
  dsimp only
  have hcardL (L : Finset ι) : Fintype.card (OuterLive L)≤N :=
    (outer_live_card L).trans hcard
  choose JL controlL hbase using fun L : Finset ι=>
    uniform_chosen_independent_energy (ι:=OuterLive L) M Hray hHray
      Φ N Holes (hcardL L) Wslot a b B Lslot Lcap Cap BR BH Bη lo hi cstar
      Kslot Bseed εfinal rho hWs hW ha haUpper hb hB hLslot hLcap hCap hBR hBH
      hBη hCapb hBcap hβ hcstar hKslot hBseed hεfinal hrho Q hQt hQ72 hQM
  let J := ∑L : Finset ι,JL L
  let control := (Finset.univ : Finset (Finset ι)).biUnion controlL
  have hJL (L : Finset ι) : JL L≤J :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ L)
  have hcontrol (L : Finset ι) : controlL L⊆control :=
    Finset.subset_biUnion_of_mem controlL (Finset.mem_univ L)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  choose CL hCL hbase using fun L : Finset ι=>hbase L η₀ hη₀
  let C := 1+∑L : Finset ι,CL L
  have hC : 0<C := by
    have hn := Finset.sum_nonneg (fun L (_ : L∈(Finset.univ : Finset (Finset ι)))=>(hCL L).le)
    dsimp only [C]
    linarith
  have hCLC (L : Finset ι) : CL L≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CL)
      (fun U _=>(hCL U).le) (Finset.mem_univ L)
    dsimp only [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro L T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqν hqW
    hWcap hWinv hqvolume hR0 hmixed hnative hlength Dseed hDseed hDcap
  have he := (hZ L).2 T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s
    hcanonical hunit hMs hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP
    cover η hη K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α q
    hα hqP hqpool hqν hqW hWcap hWinv hqvolume hR0 hmixed hnative hlength
    Dseed hDseed hDcap
  have hprofile : sourceControl (controlL L) s.W₁*sourceControl (controlL L) s.W₂≤
      sourceControl control s.W₁*sourceControl control s.W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono (hcontrol L) s.W₁)
      (MixedPrincipalPositivePart.control_mono (hcontrol L) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofile0 : 0≤sourceControl (controlL L) s.W₁*sourceControl (controlL L) s.W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofileSq := pow_le_pow_left₀ hprofile0 hprofile 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hheightPow := pow_le_pow_right₀ hheight (hJL L)
  have hrowHeight : (1:ℝ)≤1+|tp| := by linarith [abs_nonneg tp]
  have hrowHeightPow := pow_le_pow_right₀ hrowHeight (hJL L)
  have hslot0 : 0≤Kslot^(2*N) := pow_nonneg (zero_le_one.trans hKslot) _
  have hz : 0<Z := zero_lt_one.trans (hZ L).1
  dsimp only at he ⊢
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hK.le)
  have hc := mul_le_mul_of_nonneg_right (hCLC L) hslot0
  have hp := mul_le_mul hc hprofileSq (sq_nonneg _)
    (mul_nonneg hC.le hslot0)
  have hh := mul_le_mul hp hheightPow (pow_nonneg (zero_le_one.trans hheight) _)
    (mul_nonneg (mul_nonneg hC.le hslot0) (sq_nonneg _))
  exact mul_le_mul hh hrowHeightPow (pow_nonneg (zero_le_one.trans hrowHeight) _)
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hslot0) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hheight) _))


/-- The same constants apply to the literal nested remaining type of every actual outer supplier. -/
theorem uniform_chosen_rest_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b B Lslot Lcap Cap BR BH Bη lo hi cstar Kslot Bseed εfinal rho : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hB : 1≤B) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBη : 0≤Bη) (hCapb : b≤Cap) (hBcap : B≤Lcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hcstar : 0<cstar) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hεfinal : 0<εfinal) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed εfinal rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀qouter : MixedSupplierFourthRow.Data ι,
    ∀(θ : OuterLive qouter.L→RayQuotient.Characters M Hray)(w σ freq : OuterLive qouter.L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive qouter.L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source (RestIndex qouter) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : RestIndex qouter,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : RestIndex qouter,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
      cstar*Z^(referenceExponent R P S d)≤s.L→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t₀ V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈MixedSupplierPositive.selectedProducts q,
          ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal := by
  dsimp only
  obtain ⟨J,control,hbase⟩ := uniform_chosen_outer_energy (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b B Lslot Lcap Cap BR BH Bη lo hi cstar
    Kslot Bseed εfinal rho hWs hW ha haUpper hb hB hLslot hLcap hCap hBR hBH
    hBη hCapb hBcap hβ hcstar hKslot hBseed hεfinal hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hη₀
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro qouter
  let step := budgetStep B Bseed εfinal rho
  let Statement (p : OuterLive qouter.L → Prop) (ip : Fintype (Subtype p)) : Prop :=
    letI := ip
    ∀(θ : OuterLive qouter.L→RayQuotient.Characters M Hray)(w σ freq : OuterLive qouter.L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive qouter.L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ({j : OuterLive qouter.L // p j}) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : {j : OuterLive qouter.L // p j},∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : {j : OuterLive qouter.L // p j},w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
      cstar*Z^(referenceExponent R P S d)≤s.L→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t₀ V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈MixedSupplierPositive.selectedProducts q,
          ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal
  let leftInst : Fintype ↥(qouter.Jᶜ) := inferInstance
  let rightInst : Fintype (RestIndex qouter) := inferInstance
  have hp : (fun j : OuterLive qouter.L => j∈qouter.Jᶜ) =
      (fun j : OuterLive qouter.L => j∉qouter.J) := by
    funext j
    exact propext Finset.mem_compl
  have he : Statement (fun j : OuterLive qouter.L => j∈qouter.Jᶜ) leftInst :=
    hZ.2 qouter.L qouter.Jᶜ
  change Statement (fun j : OuterLive qouter.L => j∉qouter.J) rightInst
  exact subtype_statement_transport Statement hp leftInst rightInst he

open CenteredExceptionalProfile
/- APPENDIX FRAGMENT for MixedFirstOuterUniformity.lean.
Add `import Candidate.FourthPower.MixedFirstCenteredSourceMoment`
at the module header, then append this fragment before the existing
final `end` / namespace end. Reuse the already checked private
subtype_statement_transport; no new module or Source reindex is needed.

-/
open Set MixedFirstCenteredSourceMoment MixedFirstSourceMoment
open MixedSupplierFourthRow MixedSupplierPositive
open CenteredMomentUncenteredTerminal
open CompletedGauss (primaryGenerator)

/-- One actual centered-moment bound, with degree, original profile
controls, constant and threshold preceding the outer live slots and every
further subset. No energy estimate is supplied as a premise. -/
theorem uniform_centered_outer_moment
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed ε rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀L : Finset ι, ∀T : Finset (OuterLive L),
    ∀(θ : OuterLive L→RayQuotient.Characters M Hray)(w σ freq : OuterLive L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→s.G=1→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    ((Dseed.absNorm:ℝ)^step*Z^step)*groupedMoment q s ha η tp keep Φ K≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε := by
  dsimp only
  have hcardL (L : Finset ι) : Fintype.card (OuterLive L)≤N :=
    (outer_live_card L).trans hcard
  choose JL controlL hbase using fun L : Finset ι=>
    uniform_centered_source_moment (ι:=OuterLive L) M Hray hHray
      Φ N Holes (hcardL L) Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
      hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
      hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  let J := ∑L : Finset ι,JL L
  let control := (Finset.univ : Finset (Finset ι)).biUnion controlL
  have hJL (L : Finset ι) : JL L≤J :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ L)
  have hcontrol (L : Finset ι) : controlL L⊆control :=
    Finset.subset_biUnion_of_mem controlL (Finset.mem_univ L)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  choose CL hCL hbase using fun L : Finset ι=>hbase L η₀ hη₀
  let C := 1+∑L : Finset ι,CL L
  have hC : 0<C := by
    have hn := Finset.sum_nonneg (fun L (_ : L∈(Finset.univ : Finset (Finset ι)))=>(hCL L).le)
    dsimp only [C]
    linarith
  have hCLC (L : Finset ι) : CL L≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CL)
      (fun U _=>(hCL U).le) (Finset.mem_univ L)
    dsimp only [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro L T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hG hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  have he := (hZ L).2 T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s
    hcanonical hunit hG hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂
    η hη K hK hKcap hKinv χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW
    hWcap hWinv hqvolume hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  have hprofile : sourceControl (controlL L) s.W₁*sourceControl (controlL L) s.W₂≤
      sourceControl control s.W₁*sourceControl control s.W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono (hcontrol L) s.W₁)
      (MixedPrincipalPositivePart.control_mono (hcontrol L) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofile0 : 0≤sourceControl (controlL L) s.W₁*sourceControl (controlL L) s.W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofileSq := pow_le_pow_left₀ hprofile0 hprofile 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hheightPow := pow_le_pow_right₀ hheight (hJL L)
  have hrowHeight : (1:ℝ)≤1+|tp| := by linarith [abs_nonneg tp]
  have hrowHeightPow := pow_le_pow_right₀ hrowHeight (hJL L)
  have hslot0 : 0≤Kslot^(2*N) := pow_nonneg (zero_le_one.trans hKslot) _
  have hz : 0<Z := zero_lt_one.trans (hZ L).1
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hK.le)
  have hc := mul_le_mul_of_nonneg_right (hCLC L) hslot0
  have hp := mul_le_mul hc hprofileSq (sq_nonneg _)
    (mul_nonneg hC.le hslot0)
  have hh := mul_le_mul hp hheightPow (pow_nonneg (zero_le_one.trans hheight) _)
    (mul_nonneg (mul_nonneg hC.le hslot0) (sq_nonneg _))
  exact mul_le_mul hh hrowHeightPow (pow_nonneg (zero_le_one.trans hrowHeight) _)
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hslot0) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hheight) _))

/-- The same constants apply to the literal actual remaining supplier
type, including its dependent finite products, columns, normalization,
F-dependent eligibility and original full seed reserve. -/
theorem uniform_centered_rest_moment
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed ε rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀qouter : MixedSupplierFourthRow.Data ι,
    ∀(θ : OuterLive qouter.L→RayQuotient.Characters M Hray)(w σ freq : OuterLive qouter.L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive qouter.L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source (RestIndex qouter) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→s.G=1→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : RestIndex qouter,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : RestIndex qouter,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    ((Dseed.absNorm:ℝ)^step*Z^step)*groupedMoment q s ha η tp keep Φ K≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε := by
  dsimp only
  obtain ⟨J,control,hbase⟩ := uniform_centered_outer_moment (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hη₀
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro qouter
  let step := budgetStep B Bseed ε rho
  let Statement (p : OuterLive qouter.L → Prop) (ip : Fintype (Subtype p)) : Prop :=
    letI := ip
    ∀(θ : OuterLive qouter.L→RayQuotient.Characters M Hray)(w σ freq : OuterLive qouter.L→ℝ)
      (t₀ tp V : ℝ)(R₀ : OuterLive qouter.L→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ({j : OuterLive qouter.L // p j}) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→s.G=1→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : {j : OuterLive qouter.L // p j},∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : {j : OuterLive qouter.L // p j},w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    ((Dseed.absNorm:ℝ)^step*Z^step)*groupedMoment q s ha η tp keep Φ K≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε
  let leftInst : Fintype ↥(qouter.Jᶜ) := inferInstance
  let rightInst : Fintype (RestIndex qouter) := inferInstance
  have hp : (fun j : OuterLive qouter.L => j∈qouter.Jᶜ) =
      (fun j : OuterLive qouter.L => j∉qouter.J) := by
    funext j
    exact propext Finset.mem_compl
  have he : Statement (fun j : OuterLive qouter.L => j∈qouter.Jᶜ) leftInst :=
    hZ.2 qouter.L qouter.Jᶜ
  change Statement (fun j : OuterLive qouter.L => j∉qouter.J) rightInst
  exact subtype_statement_transport Statement hp leftInst rightInst he

end
end Candidate.FourthPower.MixedFirstOuterUniformity

namespace Candidate.FourthPower.MixedFirstOuterUniformity
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CompletedGauss (primaryGenerator)
open CenteredMomentSourceProfileMass CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstPhysicalApplication MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceMoment MixedFirstProfileEnvelope
open MixedFirstCenteredSourceMoment MixedFirstSeededMoment MixedFirstSourceWindow
open QRH.Record1252270103KernelMass
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open MixedCanonicalSource ReferencePrimeEnclosure
open MixedFirstUniformLossBudget MixedFirstChosenEnergy MixedFirstReferenceChoice
open MixedFirstActualNonexceptional CenteredExceptionalProfile MixedFirstGeometricCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {ι : Type u} [Fintype ι]

/-- A finite shape records the original outer live slots, actual remaining
slots, and the live slots after genuine common allocation. It records no
ideal values, profiles, character, seed or height. -/
abbrev SeededOuterShape (ι : Type u) [Fintype ι] :=
  Σ L : Finset ι, Σ T : Finset (OuterLive L), Finset T

abbrev SeededOuterIndex (shape : SeededOuterShape ι) := ↥(shape.2.2)

theorem seeded_outer_index_card (shape : SeededOuterShape ι) :
    Fintype.card (SeededOuterIndex shape)≤Fintype.card ι := by
  have hU : Fintype.card (SeededOuterIndex shape)≤Fintype.card ↥(shape.2.1) :=
    Fintype.card_le_of_injective (fun i : SeededOuterIndex shape=>i.val) Subtype.val_injective
  have hT : Fintype.card ↥(shape.2.1)≤Fintype.card (OuterLive shape.1) :=
    Fintype.card_le_of_injective (fun i : shape.2.1=>i.val) Subtype.val_injective
  exact hU.trans (hT.trans (outer_live_card shape.1))

/-- The literal checked seeded-window contract, packaged only to transport
its entire dependent source type and Fintype together. This is a conclusion,
not an assumed energy estimate. In particular P removes the original full
ordinary prefix, and both original reciprocals remain on the RHS. -/
def SeededWindowEstimate (κ : Type u) [Fintype κ]
    (M : Id) [NeZero M] (Hray : Subgroup (O⧸M)ˣ)
    (hHray : RayOrthogonality.globalUnits M≤Hray)
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (ha : 0<a) (Q : Id) (J : ℕ) (control : Finset (ℕ×ℕ))
    (C : ℝ) (η₀ : Character) (Z : ℝ) : Prop :=
    let step:=budgetStep B Bseed ε rho
    ∀(θ : κ→RayQuotient.Characters M Hray)(w σ freq : κ→ℝ)
      (t₀ tp V : ℝ)(R₀ : κ→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source κ a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      θ w σ freq t₀ R₀ s→s.B=(fun _=>1)→(∀i,s.M i≤Kslot)→
      (s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R:=inputWidth η K Z
    let P:=Real.logb Z (s.T/pairNorm s.d)
    let S:=∑i,w i
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    ∀X θwin : ℝ,0<X→∀rows : Finset O,
    Z^step*seededGroupedWindowRows q s ha D η tp keep Φ K Vwin X θwin rows≤
      C*Kslot^(2*N)*(∏i,s.M i)^2*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*heightCost tp θwin^(2*J)*
        (∫w : ℝ,(1+‖w‖)^J*‖columnDensity Vwin hVc hVs w‖)^2*
        ((η.modulus.absNorm:ℝ)*K)*Z^ε/(pairNorm s.d*(D.absNorm:ℝ))

variable (M : Id) [NeZero M] (Hray : Subgroup (O⧸M)ˣ)
  (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- One common choice for every actual finite three-level shape. The
Fourier density moment is enlarged to the same J by monotonicity, with no
new power of Z, no selected-family mass and no extra norm divisor. -/
theorem uniform_seeded_outer_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(L : Finset ι)(T : Finset (OuterLive L))(U : Finset T),
    SeededWindowEstimate ↥U M Hray hHray
      Vwin hVc hVs Φ N Holes Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
      ha Q J control C η₀ Z := by
  choose JS controlS hbase using fun shape : SeededOuterShape ι=>
    MixedFirstSourceWindow.uniform_seeded_selected_column_window
      (ι:=SeededOuterIndex shape) M Hray hHray
      Vwin hVc hVs Φ N Holes ((seeded_outer_index_card shape).trans hcard) Wslot
      a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
      hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
      hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  let J := ∑shape : SeededOuterShape ι,JS shape
  let control := (Finset.univ : Finset (SeededOuterShape ι)).biUnion controlS
  have hJS (shape : SeededOuterShape ι) : JS shape≤J :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ shape)
  have hcontrols (shape : SeededOuterShape ι) : controlS shape⊆control :=
    Finset.subset_biUnion_of_mem controlS (Finset.mem_univ shape)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  choose CS hCS hbase using fun shape : SeededOuterShape ι=>hbase shape η₀ hη₀
  let C := 1+∑shape : SeededOuterShape ι,CS shape
  have hC : 0<C := by
    have hn := Finset.sum_nonneg
      (fun shape (_ : shape∈(Finset.univ : Finset (SeededOuterShape ι)))=>(hCS shape).le)
    dsimp only [C]
    linarith
  have hCSC (shape : SeededOuterShape ι) : CS shape≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CS)
      (fun sh _=>(hCS sh).le) (Finset.mem_univ shape)
    dsimp only [C]
    linarith
  refine ⟨C,hC,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  let emptyShape : SeededOuterShape ι := ⟨∅,∅,∅⟩
  refine ⟨(hZ emptyShape).1,?_⟩
  intro L T U
  let shape : SeededOuterShape ι := ⟨L,T,U⟩
  unfold SeededWindowEstimate
  dsimp only
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hBunit hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible D hD hDcap X θwin hX rows
  have he := (hZ shape).2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s
    hcanonical hBunit hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂
    η hη K hK hKcap hKinv χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW
    hWcap hWinv hqvolume hR0 hmixed hnative keep hkeep heligible D hD hDcap X θwin hX rows
  have hprofile : sourceControl (controlS shape) s.W₁*sourceControl (controlS shape) s.W₂≤
      sourceControl control s.W₁*sourceControl control s.W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono (hcontrols shape) s.W₁)
      (MixedPrincipalPositivePart.control_mono (hcontrols shape) s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofile0 : 0≤sourceControl (controlS shape) s.W₁*sourceControl (controlS shape) s.W₂ :=
    mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hprofileSq := pow_le_pow_left₀ hprofile0 hprofile 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hheightPow := pow_le_pow_right₀ hheight (hJS shape)
  have hwindowHeight : 1≤heightCost tp θwin := by
    unfold heightCost
    have hπ : 0≤2*Real.pi := by positivity
    apply one_le_mul_of_one_le_of_one_le
    · linarith [norm_nonneg tp,mul_nonneg hπ (norm_nonneg θwin)]
    · linarith
  have hwindowPow := pow_le_pow_right₀ hwindowHeight
    (Nat.mul_le_mul_left 2 (hJS shape))
  have hmoment0 : 0≤∫w : ℝ,(1+‖w‖)^(JS shape)*‖columnDensity Vwin hVc hVs w‖ :=
    integral_nonneg (fun w=>mul_nonneg
      (pow_nonneg (by positivity : (0:ℝ)≤1+‖w‖) _) (norm_nonneg _))
  have hmoment : (∫w : ℝ,(1+‖w‖)^(JS shape)*‖columnDensity Vwin hVc hVs w‖)≤
      ∫w : ℝ,(1+‖w‖)^J*‖columnDensity Vwin hVc hVs w‖ := by
    apply integral_mono (columnDensity_moments Vwin hVc hVs (JS shape))
      (columnDensity_moments Vwin hVc hVs J)
    intro w
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg w)) (hJS shape)) (norm_nonneg _)
  have hmomentSq := pow_le_pow_left₀ hmoment0 hmoment 2
  have hslot0 : 0≤Kslot^(2*N) := pow_nonneg (zero_le_one.trans hKslot) _
  have hz : 0<Z := zero_lt_one.trans (hZ shape).1
  have hden : 0≤pairNorm s.d*(D.absNorm:ℝ) :=
    mul_nonneg (pairNorm_pos s.hd.1 s.hd.2).le (Nat.cast_nonneg _)
  have hc : CS shape*Kslot^(2*N)*(∏i,s.M i)^2≤C*Kslot^(2*N)*(∏i,s.M i)^2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCSC shape) hslot0) (sq_nonneg _)
  have hc0 : 0≤C*Kslot^(2*N)*(∏i,s.M i)^2 := by positivity
  have hp := mul_le_mul hc hprofileSq (sq_nonneg _) hc0
  have hp0 : 0≤C*Kslot^(2*N)*(∏i,s.M i)^2*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2 := by positivity
  have hh := mul_le_mul hp hheightPow (pow_nonneg (zero_le_one.trans hheight) _) hp0
  have hh0 : 0≤C*Kslot^(2*N)*(∏i,s.M i)^2*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*(height t₀ V s.t₁ s.t₂)^J :=
    mul_nonneg hp0 (pow_nonneg (zero_le_one.trans hheight) _)
  have hw := mul_le_mul hh hwindowPow (pow_nonneg (zero_le_one.trans hwindowHeight) _) hh0
  have hw0 : 0≤C*Kslot^(2*N)*(∏i,s.M i)^2*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*(height t₀ V s.t₁ s.t₂)^J*
      heightCost tp θwin^(2*J) :=
    mul_nonneg hh0 (pow_nonneg (zero_le_one.trans hwindowHeight) _)
  apply he.trans
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hK.le)
  exact mul_le_mul hw hmomentSq (sq_nonneg _) hw0

private theorem seeded_subtype_statement_transport {κ : Type u}
    (P : (p : κ→Prop)→Fintype (Subtype p)→Prop)
    {p q : κ→Prop} (h : p=q) (ip : Fintype (Subtype p)) (iq : Fintype (Subtype q))
    (hp : P p ip) : P q iq := by
  cases h
  have hi : ip=iq := Subsingleton.elim _ _
  cases hi
  exact hp

/-- The literal actual remaining supplier type, followed by any genuine
live subset. In application use U=liveIndices B.val. Frozen x, common G,
allocation B and all their actual profiles occur only AFTER these constants.
No coefficient replacement or abstract equivalence of source families is used. -/
theorem uniform_seeded_rest_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀qouter : MixedSupplierFourthRow.Data ι,∀U : Finset (RestIndex qouter),
    SeededWindowEstimate ↥U M Hray hHray
      Vwin hVc hVs Φ N Holes Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
      ha Q J control C η₀ Z := by
  obtain ⟨J,control,hbase⟩ := uniform_seeded_outer_window (ι:=ι) M Hray hHray
    Vwin hVc hVs Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hη₀
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro qouter
  let Statement (p : OuterLive qouter.L→Prop) (ip : Fintype (Subtype p)) : Prop :=
    letI := ip
    ∀U : Finset (Subtype p),SeededWindowEstimate ↥U M Hray hHray
      Vwin hVc hVs Φ N Holes Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
      ha Q J control C η₀ Z
  let leftInst : Fintype ↥(qouter.Jᶜ) := inferInstance
  let rightInst : Fintype (RestIndex qouter) := inferInstance
  have hp : (fun j : OuterLive qouter.L=>j∈qouter.Jᶜ) =
      (fun j : OuterLive qouter.L=>j∉qouter.J) := by
    funext j
    exact propext Finset.mem_compl
  have he : Statement (fun j : OuterLive qouter.L=>j∈qouter.Jᶜ) leftInst :=
    hZ.2 qouter.L qouter.Jᶜ
  change Statement (fun j : OuterLive qouter.L=>j∉qouter.J) rightInst
  exact seeded_subtype_statement_transport Statement hp leftInst rightInst he

end
end Candidate.FourthPower.MixedFirstOuterUniformity
