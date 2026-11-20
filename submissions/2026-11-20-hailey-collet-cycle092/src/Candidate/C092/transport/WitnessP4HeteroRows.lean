/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual frozen-label P4 witnesses are paid by the authentic PairAt source. -/
import Candidate.C092.transport.WitnessRowSupActualPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.WitnessRowSup.Actual.Hetero
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths ConcretePrimeRowBridge CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness HeckeDetectorDyadicProfiles
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_WitnessP4HeteroRows_52c5ecaa53c4dbf3_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The literal heterogeneous fixed-pair source. The retained long anchor
has its own native keep gate and exact common-mark presentation. The short
witness keep and mark presentation follow from the actual original state. -/
theorem actual_fixed_pair
    {U Bmask bstate Z N Y l bΦ mesh ε C : ℝ} {W : ℝ→ℂ}
    (s : NaturalState U Bmask bstate) (η₀ : Character) (Q : Ideal O)
    (ηLong baseLong : Character) (QLong : Ideal O)
    (hQM : Q ≤ M)
    (j : Option (RayQuotient.Characters M H × RayQuotient.Characters M H))
    {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hpair : PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh ε Z
      ηLong (witnessBase M H hH s.character η₀ j)
      baseLong (witnessBase M H hH η₀ η₀ j) QLong Q degree controls C)
    (Tslots : Finset Slot) (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ)
    (θLong : Slot→RayQuotient.Characters M H) (σLong vLong : Slot→ℝ)
    (tMark tLong slotHeight heightLong XL XS : ℝ) (hZ : 0 < Z)
    (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ slotHeight) (hv : ∀ i,|v i| ≤ slotHeight)
    (hσLonglo : ∀ i,(33/50:ℝ) ≤ σLong i) (hσLonghi : ∀ i,σLong i ≤ (33/50:ℝ))
    (hhLong : 0 ≤ heightLong) (hvLong : ∀ i,|vLong i| ≤ heightLong)
    (hsum : (∑ i∈Tslots,w i) ≤ l) (hXL : 0 < XL) (hXS : 0 < XS)
    (hXN : length Z XL ≤ N) (hXY : length Z XS ≤ Y)
    (rows : Finset FreeRow)
    (hk : ∀ u∈rows,initialKeep s.character (internalQ Q η₀) u.val)
    (hkLong : ∀ u∈rows,initialKeep ηLong (internalQ QLong baseLong) u.val)
    (hmLong : ∀ u∈rows,∀ k∈Tslots,
      ‖normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 Z w k) (originalCoefficients M H hH η₀ θ W Z w σ v k) tMark (Z^(w k))‖ =
      ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools M H 2 Z w k) (originalCoefficients M H hH baseLong θLong W Z w σLong vLong k) tLong (Z^(w k))‖)
    (hy : ∀ u∈rows,rowNorm u ≤ Z) :
    ∀ p : Profiles (1/4) (9/4),
      finiteEnergyOn Tslots rows ηLong (witnessBase M H hH s.character η₀ j)
        (p.profile 0) (p.profile 1) tLong 0 XL XS
        (fun i u=>normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 Z w i) (originalCoefficients M H hH η₀ θ W Z w σ v i)
          tMark (Z^(w i))) ≤
      (C*QuadraticInitialBound.diagonalControl radialMajorant*
        (1+|tLong|+(|tMark|+|tLong|+slotHeight+heightLong))^degree*Z^(1+ε))*(p.control controls)^2 := by
  have hslot : 0 ≤ |tMark|+|tLong|+slotHeight+heightLong := by positivity
  have hvl (k : Slot) : |vLong k| ≤ |tMark|+|tLong|+slotHeight+heightLong := by
    linarith [hvLong k,abs_nonneg tMark,abs_nonneg tLong]
  have hvs (k : Slot) : |tMark+v k| ≤ |tMark|+|tLong|+slotHeight+heightLong := by
    linarith [abs_add_le tMark (v k),hv k,abs_nonneg tLong]
  apply pairAt_fixed_height M H hH hpair Tslots θLong θ w σLong σ
    vLong (fun k=>tMark+v k) tLong (|tMark|+|tLong|+slotHeight+heightLong)
    XL XS hw hwm hσLonglo hσLonghi hσlo hσhi hslot hvl hvs hsum hXL hXS hXN hXY rows _ hkLong
    (fun u hu=>(witness_initialKeep M H hH Q hQM s.character η₀ j u).mpr (hk u hu)) hy hmLong
  intro u hu i hi
  simpa only [sub_zero] using original_mark_presentation M H hH s.character η₀ j θ W
    Z hZ w σ v tMark 0 u i

/-- Actual P4 witness rectangle, on the original frozen finite family.
J and C are chosen from the fixed annular test and source controls BEFORE
all live states, original rows, label choices, dyads, zeros and frequencies.
There is no external per-row witness-profile estimate in this statement. -/
theorem actual_witness_rowwise (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧
    ∀ (U Bmask bstate Z N Y l bΦ mesh εsource Csource : ℝ) (W : ℝ→ℂ)
      (s : NaturalState U Bmask bstate) (η₀ : Character) (Q : Ideal O)
    (ηLong baseLong : Character) (QLong : Ideal O)
      (hQM : Q ≤ M)
      (hmask : s.mask = fixedBadMask*idealGenerator 1)
      (hkeep : ∀ z,s.radial.keep z ↔ initialKeep s.character (internalQ Q η₀) z)
      (j : Option (RayQuotient.Characters M H × RayQuotient.Characters M H))
      (degree : ℕ),
      PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh εsource Z
        ηLong (witnessBase M H hH s.character η₀ j)
        baseLong (witnessBase M H hH η₀ η₀ j) QLong Q degree controls Csource →
    ∀ (Tslots : Finset Slot) (θ : Slot→RayQuotient.Characters M H) (w σslot v : Slot→ℝ)
      (θLong : Slot→RayQuotient.Characters M H) (σLong vLong : Slot→ℝ)
      (tMark tLong slotHeight heightLong XL : ℝ),0 < Z →
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ) ≤ σslot i) → (∀ i,σslot i ≤ (33/50:ℝ)) →
      0 ≤ slotHeight → (∀ i,|v i| ≤ slotHeight) →
      (∀ i,(33/50:ℝ) ≤ σLong i) → (∀ i,σLong i ≤ (33/50:ℝ)) →
      0 ≤ heightLong → (∀ i,|vLong i| ≤ heightLong) →
      (∑ i∈Tslots,w i) ≤ l → 0 < XL → length Z XL ≤ N →
    ∀ (rows : Finset FreeRow) (hrows : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,initialKeep ηLong (internalQ QLong baseLong) u.val) →
      (∀ u∈rows,∀ k∈Tslots,
        ‖normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 Z w k) (originalCoefficients M H hH η₀ θ W Z w σslot v k) tMark (Z^(w k))‖ =
        ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 Z w k) (originalCoefficients M H hH baseLong θLong W Z w σLong vLong k) tLong (Z^(w k))‖) →
      (∀ u∈rows,rowNorm u ≤ Z) →
    ∀ (d a ε cutoff T allowance m : ℝ) (i : ℕ),0 < U → 0 ≤ a →
      0 ≤ T → 0 ≤ allowance → 0 ≤ Csource → length Z ((U^d)^m) ≤ Y →
    ∀ ws : ∀ u : rows,SupportedWitness
        (family M H hH s η₀ (naturalRow s.character u.val.val
          (s.row_ne_zero u.val.val (hrows u.val u.property)))) (U^d) a ε cutoff T allowance i,
      (∀ u : rows,(ws u).label=j) → (∀ u : rows,(ws u).m=m) →
    ∀ (WL : 𝓢(ℝ,ℂ)),Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) →
    ∀ (weight : rows→ℝ) (A : ℝ),0 ≤ A → (∀ u,0 ≤ weight u) → (∀ u,weight u ≤ A) →
      (∑ u : rows,weight u*‖QRH.Cycle092.SignedEnergy.actualPlain (ws u)*
        (original ηLong s.mask 1 u.val.val WL tLong XL*
          ∏ k∈Tslots,normalizedSlot s.character s.mask 1 u.val.val
            (originalPools M H 2 Z w k) (originalCoefficients M H hH η₀ θ W Z w σslot v k)
            tMark (Z^(w k)))‖^2) ≤
        12*A*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
          (1+|tLong|+(|tMark|+|tLong|+slotHeight+heightLong))^degree*Z^(1+εsource))*
          (sourceControl controls WL)^2*C^2*
          (1+(2*Real.pi*allowance+(3*i : ℕ)*T))^(2*J+1) := by
  obtain ⟨J,C,hC,hrowwise⟩ := original_pair_rowwise (Slot:=Slot) positiveAnnular
    positiveAnnular_support positiveAnnular_smooth controls
  refine ⟨J,C,hC,?_⟩
  intro U Bmask bstate Z N Y l bΦ mesh εsource Csource W s η₀ Q ηLong baseLong QLong hQM hmask hkeep j degree hpair
    Tslots θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL hZ hw hwm hσlo hσhi hh hv
    hσLonglo hσLonghi hhLong hvLong hsum hXL hXN rows hrows hkLong hmLong hy d a ε cutoff T allowance m i hU ha hT hall hCsrc hXY ws hlabel hm WL hWL
    weight A hA hweight hweightA
  let ηW := witnessBase M H hH s.character η₀ j
  let mark : Slot→FreeRow→ℂ := fun k u=>normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
    (originalPools M H 2 Z w k) (originalCoefficients M H hH η₀ θ W Z w σslot v k) tMark (Z^(w k))
  let χ : FreeRow→Character := fun u=>if hu : u∈rows then
    family M H hH s η₀ (naturalRow s.character u.val (s.row_ne_zero u.val (hrows u hu))) j else ηW
  let sig : FreeRow→ℝ := fun u=>if hu : u∈rows then (ws ⟨u,hu⟩).zero.re else 0
  let freq : FreeRow→ℝ := fun u=>if hu : u∈rows then 2*Real.pi*(ws ⟨u,hu⟩).nu-(ws ⟨u,hu⟩).zero.im else 0
  let wt : FreeRow→ℝ := fun u=>if hu : u∈rows then weight ⟨u,hu⟩ else 0
  let Hwit := 2*Real.pi*allowance+(3*i : ℕ)*T
  let K := Csource*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|tLong|+(|tMark|+|tLong|+slotHeight+heightLong))^degree*Z^(1+εsource)
  have hK : 0 ≤ K := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp [K]; positivity
  have hfix := actual_fixed_pair M H hH s η₀ Q ηLong baseLong QLong hQM j hpair Tslots θ w σslot v θLong σLong vLong tMark tLong
    slotHeight heightLong XL ((U^d)^m) hZ hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hsum hXL
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hU _) _) hXN hXY rows
    (fun u hu=>(hkeep u.val).mp (hrows u hu)) hkLong hmLong hy
  have hχ (u : FreeRow) (hu : u∈rows) : ∀ n,elementCoeff (χ u) n =
      rowTwist (elementHom ηW) (fixedBadMask*idealGenerator 1) 1 (1*u.val) n := by
    simpa only [χ,dif_pos hu,ηW,←hmask] using
      witness_row M H hH s η₀ (naturalRow s.character u.val (s.row_ne_zero u.val (hrows u hu))) j
  have hsig (u : FreeRow) (hu : u∈rows) : sig u ∈ Icc (0:ℝ) 1 := by
    simpa only [sig,dif_pos hu] using (witness_coordinates (ws ⟨u,hu⟩) ha).1
  have hfreq (u : FreeRow) (hu : u∈rows) : |freq u| ≤ Hwit := by
    simpa only [freq,dif_pos hu,Hwit] using (witness_coordinates (ws ⟨u,hu⟩) ha).2
  have hr := hrowwise Tslots rows ηLong ηW WL hWL tLong XL ((U^d)^m) K
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hU _) _) hK mark hfix χ hχ wt A Hwit hA
    (by dsimp [Hwit];positivity)
    (fun u hu=>by simpa only [wt,dif_pos hu] using hweight ⟨u,hu⟩)
    (fun u hu=>by simpa only [wt,dif_pos hu] using hweightA ⟨u,hu⟩) sig freq hsig hfreq
  rw [←Finset.sum_coe_sort rows] at hr
  convert hr using 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [wt,sig,freq,χ,dif_pos u.property,mark,K,Hwit]
  rw [QRH.Cycle092.SignedEnergy.actualPlain,hlabel u,hm u,hmask]

#print axioms actual_fixed_pair
#print axioms actual_witness_rowwise
end
end QRH.Cycle092.WitnessRowSup.Actual.Hetero
