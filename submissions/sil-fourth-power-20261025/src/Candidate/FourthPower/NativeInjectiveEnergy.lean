/- Copyright (c) 2026 Sil. Apache-2.0.
Apply reverse collision completion to literal natural slots. Only full
subset products of the original coefficients with bounded finite holes
are required. The final radial estimate is in the original positive norm.
-/
import Candidate.FourthPower.NativeCollisionEnergy
import Candidate.FourthPower.NativeFiniteHoles
import Candidate.FourthPower.KernelNaturalSlots
import Candidate.FourthPower.ReferencePrimeEnclosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativeInjectiveEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval
open OAI.SevenEighths.Record12518109GainDeletion
open KernelCollisionMass KernelNaturalSlots NativeFiniteHoles
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem masked_slot_sum (atoms pool : Finset Id) (hs : pool⊆atoms)
    (χ : Character) (β : Id→ℂ) (P : ℝ) (R : Finset atoms) :
    (∑p : atoms,if p∈R then 0 else slotTerm χ pool β P p.val)=
      naturalSlot χ pool (fun I=>if I∈R.image Subtype.val then 0 else β I) P := by
  rw [←sum_slotTerm χ pool atoms _ P hs]
  apply Finset.sum_congr rfl
  intro p _
  have hm : p.val∈R.image Subtype.val ↔ p∈R := by
    constructor
    · intro h
      obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp h
      have he : q=p := Subtype.ext hqp
      simpa only [he] using hq
    · intro h
      exact Finset.mem_image.mpr ⟨p,h,rfl⟩
  by_cases hr : p∈R <;> by_cases hp : p.val∈pool <;> simp [slotTerm,hm,hr,hp]

variable {α : Type*} [Fintype α]

/-- A literal transfer from canonical full-product energies; it makes no
claim that arbitrary bounded replacements have such energies. -/
theorem natural_finite_energy (B ε : ℝ) (hB : 1≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X : ℝ,1≤X → ∀atoms : Finset Id,
      (∀I∈atoms,Supported I ∧ (I.absNorm:ℝ)≤X) →
      ∀{Row : Type*}(rows : Finset Row)(ρ : Row→ℝ)(D : Row→ℂ)(χ : Row→Character)
        (pool : α→Finset Id)(β : α→Id→ℂ)(P : α→ℝ)(E : ℝ),
      (∀i,pool i⊆atoms) → 0≤E → (∀u∈rows,0≤ρ u) →
      (∀u∈rows,∀(i : α)(p : atoms),‖slotTerm (χ u) (pool i) (β i) (P i) p.val‖≤centralWeight B p.val) →
      (∀T : Finset α,∀R : α→Finset Id,
        (∀i∈T,(R i).card≤Fintype.card α*Fintype.card α) →
        (∑u∈rows,ρ u*‖D u*(∏i∈T,naturalSlot (χ u) (pool i) (holeCoefficient β R i) (P i))‖^2)≤E) →
      (∑u∈rows,ρ u*‖D u*injectiveTuplePolynomial
        (fun i=>fun p : atoms=>slotTerm (χ u) (pool i) (β i) (P i) p.val)‖^2)≤C*X^ε*E := by
  let N := Fintype.card α
  obtain ⟨δ,hδ,hcost⟩ := NativeCollisionEnergy.stepCost_subpower N B ε hB hε
  let K := SieveDescent.rootMass (1+δ)+1
  have hK : 1≤K := by dsimp [K]; exact le_add_of_nonneg_left (SieveDescent.rootMass_nonneg _)
  obtain ⟨C,hC,hcost⟩ := hcost K hK
  refine ⟨C,hC,?_⟩
  intro X hX atoms hatoms Row rows ρ D χ pool β P E hp hE hρ ha
  intro hfull
  let L := K*X^δ
  have hL : 1≤L := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX hδ.le)
  have he (i : α) : (∑p : atoms,(centralWeight B p.val)^2)≤L*B^2 := by
    apply (central_pool_energy δ B X hδ (zero_lt_one.trans_le hX) atoms hatoms).trans
    dsimp only [L,K]
    have hmass : 0≤B^2*X^δ := mul_nonneg (sq_nonneg B) (Real.rpow_nonneg (zero_le_one.trans hX) _)
    nlinarith
  have hh := NativeCollisionEnergy.injective_energy_of_subsets rows ρ
    (fun u i p=>slotTerm (χ u) (pool i) (β i) (P i) p.val)
    (fun _i : α=>fun p : atoms=>centralWeight B p.val) D B L E hρ hB hL hE
    (fun _ p=>centralWeight_nonneg B (zero_le_one.trans hB) p.val)
    (fun _ p=>centralWeight_le B (zero_le_one.trans hB) p.val (hatoms p.val p.property).1)
    he ha N le_rfl (by
      intro T R hR
      let R' (i : α) : Finset Id := (R i).image Subtype.val
      have hR' (i : α) (hi : i∈T) : (R' i).card≤N*N := Finset.card_image_le.trans (hR i hi)
      have hf := hfull T R' hR'
      apply (le_of_eq ?_).trans hf
      apply Finset.sum_congr rfl
      intro u _
      apply congrArg (fun z : ℂ=>ρ u*‖D u*z‖^2)
      apply Finset.prod_congr rfl
      intro i _
      have hm := masked_slot_sum atoms (pool i) (hp i) (χ u) (β i) (P i) (R i)
      apply (Eq.trans ?_ hm).trans
      · apply congrArg (fun f : Id→ℂ=>naturalSlot (χ u) (pool i) f (P i))
        funext I
        dsimp only [holeCoefficient,R']
      · apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p∈R i <;> simp [NativeCollisionEnergy.mask,hp])
  exact hh.trans (mul_le_mul_of_nonneg_right (hcost X hX) hE)

/-- The same transfer for the actual compact physical radial norm. There
is no multiplication by the number of physical rows or available primes. -/
theorem natural_radial_energy (B ε : ℝ) (hB : 1≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X : ℝ,1≤X → ∀atoms : Finset Id,
      (∀I∈atoms,Supported I ∧ (I.absNorm:ℝ)≤X) →
      ∀(D : O→ℂ)(χ : O→Character)(pool : α→Finset Id)(β : α→Id→ℂ)(P : α→ℝ)(E : ℝ),
      (∀i,pool i⊆atoms) → 0≤E →
      (∀(u : O)(i : α)(p : atoms),‖slotTerm (χ u) (pool i) (β i) (P i) p.val‖≤centralWeight B p.val) →
      ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial →
      (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀T : Finset α,∀R : α→Finset Id,
        (∀i∈T,(R i).card≤Fintype.card α*Fintype.card α) →
        radialEnergy (fun z=>D z*∏i∈T,naturalSlot (χ z) (pool i) (holeCoefficient β R i) (P i))
          keep Φ K≤E) →
      radialEnergy (fun z=>D z*injectiveTuplePolynomial
        (fun i=>fun p : atoms=>slotTerm (χ z) (pool i) (β i) (P i) p.val)) keep Φ K≤C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := natural_finite_energy (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX atoms hatoms D χ pool β P E hp hE ha keep Φ K radial hK hs hΦ hchildren
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
  intro rows
  let ρ (z : O) : ℝ := if keep z then (Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hρ (z : O) : 0≤ρ z := by dsimp [ρ]; split_ifs; exact hΦ z; exact le_rfl
  have hfull (T : Finset α) (R : α→Finset Id)
      (hR : ∀i∈T,(R i).card≤Fintype.card α*Fintype.card α) :
      (∑z∈rows,ρ z*‖D z*(∏i∈T,naturalSlot (χ z) (pool i) (holeCoefficient β R i) (P i))‖^2)≤E := by
    let G (z : O) := D z*∏i∈T,naturalSlot (χ z) (pool i) (holeCoefficient β R i) (P i)
    have hsum := compact_radial_summable G keep Φ K radial hK hs
    have hh := hsum.sum_le_tsum rows (fun z _=>by
      split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
    have hid (z : O) : ρ z*‖G z‖^2=
        if keep z then ‖G z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
      dsimp [ρ]; split_ifs <;> ring
    change (∑z∈rows,ρ z*‖G z‖^2)≤E
    simp_rw [hid]
    exact hh.trans (hchildren T R hR)
  have hh := hbound X hX atoms hatoms rows ρ D χ pool β P E hp hE
    (fun z _=>hρ z) (fun z _=>ha z) hfull
  apply (le_of_eq ?_).trans hh
  apply Finset.sum_congr rfl
  intro z _
  dsimp [ρ]
  split_ifs <;> ring

open Filter CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor QuadraticInitialBound
open HeckeDyadic ConcretePrimeRowBridge

/-- Keep only the atoms on which the physical character can be nonzero. -/
def supportedPool (pool : Finset Id) : Finset Id := pool.filter Supported

theorem natural_character_off_supported (η : Character) (z : O) (hz : z≠0) :
    ∀I : Id,¬Supported I → idealCoeff (naturalCharacter η z) I=0 := by
  intro I hI
  have he := CenteredMomentSourceRow.rowWeight_zero_of_not_supported η
    CenteredMomentSecondHeightFamily.fixedBadMask 1 z 0
    (dvd_mul_right _ _) (dvd_mul_left _ _) I hI
  change (idealCoeff η I*CanonicalRowCompletion.idealRowHom
    (CenteredMomentSecondHeightFamily.fixedBadMask^6*(1*z)) I)*
    (I.absNorm:ℂ)^(Complex.I*0)=0 at he
  rw [naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
  simpa only [one_mul,mul_zero,Complex.cpow_zero,mul_one] using he

theorem supported_slotTerm (χ : Character)
    (hχ : ∀I,¬Supported I → idealCoeff χ I=0)
    (pool : Finset Id) (β : Id→ℂ) (P : ℝ) (I : Id) :
    slotTerm χ (supportedPool pool) β P I=slotTerm χ pool β P I := by
  by_cases hs : Supported I
  · simp [slotTerm,supportedPool,hs]
  · simp [slotTerm,supportedPool,hs,hχ I hs]

theorem supported_naturalSlot (χ : Character)
    (hχ : ∀I,¬Supported I → idealCoeff χ I=0)
    (pool : Finset Id) (β : Id→ℂ) (P : ℝ) :
    naturalSlot χ (supportedPool pool) β P=naturalSlot χ pool β P := by
  unfold naturalSlot supportedPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  by_cases hs : Supported I <;> simp [hs,hχ I]

theorem radial_supported_slots (η : Character) (D : O→ℂ)
    (T : Finset α) (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (keep : O→Prop) (hkeep : ∀z,keep z → z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>D z*∏i∈T,naturalSlot (naturalCharacter η z)
      (supportedPool (pool i)) (β i) (P i)) keep Φ K =
    radialEnergy (fun z=>D z*∏i∈T,naturalSlot (naturalCharacter η z)
      (pool i) (β i) (P i)) keep Φ K := by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [ite_eq_left hk]
    have hχ := natural_character_off_supported η z (hkeep z hk)
    simp_rw [supported_naturalSlot _ hχ]
  · simp only [ite_eq_right hk]

theorem canonical_pool_norm_le (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (P : ℝ) (hP : 0<P) (I : Id) (hI : I∈primePool M H 2 P) :
    (I.absNorm:ℝ)≤2*P := by
  have hi := (mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1).2
  change I.absNorm≤⌊max 1 (2:ℝ)*P⌋₊ at hi
  have hh := ((Nat.cast_le (α:=ℝ)).mpr hi).trans
    (Nat.floor_le (show 0≤max 1 (2:ℝ)*P by positivity))
  simpa only [max_eq_right (show (1:ℝ)≤2 by norm_num)] using hh

theorem canonical_pool_enclosed (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (Z w L Cap : ℝ) (hZ : 1≤Z) (hw : w≤L) (hCap : 2≤Cap) :
    supportedPool (primePool M H 2 (Z^w))⊆ReferencePrimeEnclosure.primePool (Cap*Z^L) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  have hp : Prime I := (Finset.mem_filter.mp hi.1).2.1
  apply Finset.mem_filter.mpr
  refine ⟨(CenteredMomentSourceMass.mem_idealBall _ _).mpr ⟨hp.ne_zero,?_⟩,hp,hi.2⟩
  exact (canonical_pool_norm_le M H _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _) I hi.1).trans
    (mul_le_mul hCap (Real.rpow_le_rpow_of_exponent_le hZ hw)
      (Real.rpow_nonneg (zero_le_one.trans hZ) _) (by linarith))

theorem cutoff_loss (Z L Cap ε q : ℝ) (hZ : 1≤Z) (hL : 0≤L)
    (hCap : 0≤Cap) (hε : 0<ε) :
    (Cap*Z^L)^(ε/(2*(L+1)))*Z^(q+ε/2)≤
      Cap^(ε/(2*(L+1)))*Z^(q+ε) := by
  let δ := ε/(2*(L+1))
  have hd : 0<2*(L+1) := by positivity
  have hδ : 0<δ := div_pos hε hd
  have heq : δ*(2*(L+1))=ε := div_mul_cancel₀ _ (ne_of_gt hd)
  have he : L*δ≤ε/2 := by nlinarith
  have hZ0 := zero_lt_one.trans_le hZ
  change (Cap*Z^L)^δ*Z^(q+ε/2)≤Cap^δ*Z^(q+ε)
  rw [Real.mul_rpow hCap (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
  calc
    _ ≤ (Cap^δ*Z^(ε/2))*Z^(q+ε/2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he)
          (Real.rpow_nonneg hCap _)) (Real.rpow_nonneg hZ0.le _)
    _ = Cap^δ*Z^(q+ε) := by
      rw [mul_assoc,←Real.rpow_add hZ0]
      congr 2
      ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The canonical source supplies the full-product hypotheses. The cutoff
and atom enclosure remain explicit geometric data; no moment estimate is
an input. All inherited ordinary heights and divided lengths are retained. -/
theorem canonical_shortened_children [DecidableEq α]
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot ε η lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hε : 0<ε) (hη : 0<η)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀X : ℝ,1≤X → ∀atoms : Finset Id,
      (∀I∈atoms,Supported I ∧ (I.absNorm:ℝ)≤X) →
      (∀i,supportedPool (primePool M H 2 (Z^(w i)))⊆atoms) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        injectiveTuplePolynomial (fun i=>fun p : atoms=>
          slotTerm (naturalCharacter s.character z) (supportedPool (primePool M H 2 (Z^(w i))))
            (heightCoefficient (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t) (Z^(w i)) p.val))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*X^η*Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Ci,hCi,hinj⟩ := natural_radial_energy (α:=α) (2*B) η (by linarith) hη
  obtain ⟨degree,S,hchildren⟩ := NativeFiniteHoles.shortened_children M H hH
    (Finset.univ : Finset α) (Holes+Fintype.card α*Fintype.card α) W 1 2 a b radial Mcap L Lslot ε lo hi κ
    (by norm_num) hWs hW ha haUpper hb hrad hM hLslot hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Ci*Cc,mul_pos hCi hCc,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂ X hX atoms hatoms hpool
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let β := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let D := fun z=>polynomial (naturalCharacter s.character z) false W₁
      (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
    polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i := by
    refine ⟨(hatoms I (hpool i hI)).1,?_⟩
    exact canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1
  have hbcoef (i : α) (I : Id) (hI : I∈pool i) : ‖β i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [β,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [β,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,B] using he
  have hh := hinj X hX atoms hatoms D (fun z=>naturalCharacter s.character z) pool β P E
    hpool hE (fun z i p=>slotTerm_bound _ _ _ _ B (hP i) (zero_le_one.trans hB)
      (hp i) (hbcoef i) p.val)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos
    s.radial_support s.radial.nonneg (by
      intro T R hR
      have hbudget (i : α) (hi : i∈T) : (R₀ i∪R i).card≤Holes+Fintype.card α*Fintype.card α :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add (hR₀ i) (hR i hi))
      have he := hZ.2 θ w σ freq t V (fun i _=>hw i) (fun i _=>hwL i)
        (fun i _=>hσ i) (fun i _=>hσhi i) hV (fun i _=>hfreq i) Bmask s hQ hwidth
        T (Finset.subset_univ _) (fun i=>R₀ i∪R i) hbudget
        W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
      have hmask (i : α) : holeCoefficient β R i=
          heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪R i) i) t := by
        funext I
        by_cases hi : I∈R i <;> by_cases hj : I∈R₀ i <;>
          simp [β,holeCoefficient,heightCoefficient,hi,hj]
      simp_rw [hmask]
      rw [radial_supported_slots s.character D T (fun i=>primePool M H 2 (P i))
        (fun i=>heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪R i) i) t) P
        (effectiveState s).radial.keep (fun z hz=>s.row_ne_zero z hz.1)]
      exact he)
  apply hh.trans_eq
  dsimp only [E]
  ring

/-- The actual supported prime enclosure is constructed here and its cost
is absorbed in the chosen epsilon. No atom-enclosure or energy hypothesis
remains. Cap and Lcap may also enclose the ordinary factors downstream. -/
theorem canonical_closed_children [DecidableEq α]
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Ideal O) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
        polynomial (naturalCharacter s.character z) false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
        injectiveTuplePolynomial (fun i=>fun p : ReferencePrimeEnclosure.primePool (Cap*Z^Lcap)=>
          slotTerm (naturalCharacter s.character z) (supportedPool (primePool M H 2 (Z^(w i))))
            (heightCoefficient (holeCoefficient (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t) (Z^(w i)) p.val))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let η := ε/(2*(Lcap+1))
  have hη : 0<η := div_pos hε (by positivity)
  obtain ⟨degree,S,hbound⟩ := canonical_shortened_children (α:=α) M H hH Holes W
    a b radial Mcap L Lslot (ε/2) η lo hi κ hWs hW ha haUpper hb hrad hM hLslot
    (half_pos hε) hη hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbound⟩ := hbound η₀ hQη
  refine ⟨Cap^η*C,mul_pos (Real.rpow_pos_of_pos hCap0 _) hC,hbound.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
  have hX : 1≤Cap*Z^Lcap := one_le_mul_of_one_le_of_one_le (by linarith)
    (Real.one_le_rpow hZ.1.le hLcap0)
  have hatoms (I : Id) (hI : I∈ReferencePrimeEnclosure.primePool (Cap*Z^Lcap)) :
      Supported I ∧ (I.absNorm:ℝ)≤Cap*Z^Lcap :=
    ⟨(Finset.mem_filter.mp hI).2.2,
      ((CenteredMomentSourceMass.mem_idealBall _ _).mp (Finset.mem_filter.mp hI).1).2⟩
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂ D₁ D₂ hD₁ hD₂
    (Cap*Z^Lcap) hX (ReferencePrimeEnclosure.primePool (Cap*Z^Lcap)) hatoms
    (fun i=>canonical_pool_enclosed M H Z (w i) Lcap Cap hZ.1.le ((hwL i).trans hLcap) hCap)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hcost := mul_le_mul_of_nonneg_left
    (cutoff_loss Z Lcap Cap ε (s.width+κ*(∑i,w i)) hZ.1.le hLcap0 hCap0.le hε)
    (show 0≤C*diagonalControl s.radial.profile*
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*(1+|t|+V)^degree by positivity)
  apply he.trans
  convert hcost using 1 <;> dsimp only [η] <;> ring

end
end Candidate.FourthPower.NativeInjectiveEnergy
