/- Copyright (c) 2026 Sil. Apache-2.0.
Forward restriction in the original physical norm. The analytic child input
is the literal remaining sum proved in NativeRemainingEnergy, not an
arbitrary replacement coefficient estimate.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeRemainingEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RestorationInverseEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.ReferenceForwardRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Candidate.FourthPower.NativeForwardEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools KernelRowProfiles
open KernelPhysicalScalars KernelFamilyEnergy ReferencePrimeEnclosure RestorationFamily
open RestorationInverseEnergy ReferenceForwardRows NativeRemainingEnergy NativeInjectiveEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT HeckeDyadic
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem literal_forward_expansion (S : Finset PrimeIdeal) (χ : Character)
    (pool : α→Finset Id) (β : α→Id→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ t₁ t₂ : ℝ)
    (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hW₁ : Function.support W₁⊆Set.Iic b) (hW₂ : Function.support W₂⊆Set.Iic b)
    (hχ : ∀I,¬Supported I → idealCoeff χ I=0)
    (henclose : ∀I,Supported I →
      ((I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) → primeSupport I⊆primeValues S) :
    row false S χ pool β P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂=
      ∑T : Finset α,∑frozen∈frozenChoices T S,∑d∈divisorPool (supportedRectangle S b X₁ X₂),
        scalar χ S (ordinarySeriesFor false) (markedSeriesFor false)
          (fun i : T=>pool i.val) (fun i : T=>β i.val) (fun i : T=>P i.val) frozen d *
          (polynomial χ false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
            polynomial χ false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
            remainingSum T (naturalCoefficients χ S pool β P) frozen (fun _=>1)) := by
  rw [row,natural_rectangle_expansion false S χ pool β P _ _ b X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T _
  rw [frozenChoices,Finset.sum_filter]
  apply Finset.sum_congr (by ext; simp)
  intro frozen _
  by_cases hinj : Function.Injective frozen
  · simp only [hinj,ite_true]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 := divisor_supported hd
    have h₁ := shortened_positive_le hX₁ hd0.1
    have h₂ := shortened_positive_le hX₂ hd0.2.1
    have hrow := enclosed_phase_pair χ S W₁ W₂ b
      (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ)) t₁ t₂ h₁.1 h₂.1 hW₁ hW₂ hχ (by
        intro I hI hlen
        apply henclose I hI
        exact hlen.elim
          (fun h=>Or.inl (h.trans (mul_le_mul_of_nonneg_left h₁.2 hb)))
          (fun h=>Or.inr (h.trans (mul_le_mul_of_nonneg_left h₂.2 hb))))
    simp only [childValue,Bool.false_eq_true,ite_false]
    rw [remaining_constant,hrow]
  · simp only [hinj,ite_false]

/-- The scalar mass is summed before the physical norm. The number of
prime assignments is absent from the bound. The remaining energy premise
names exactly the canonical child family established separately. -/
theorem finite_forward_energy (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X : ℝ,1≤X → ∀S : Finset PrimeIdeal,
      (∀Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤X) →
    ∀{Row : Type*}(rows : Finset Row)(ρ : Row→ℝ)(χ : Row→Character)
      (pool : α→Finset Id)(β : α→Id→ℂ)(P : α→ℝ),
      (∀i,0<P i) → (∀i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ)≤2*P i) →
      (∀i I,I∈pool i → ‖β i I‖≤B) →
    ∀(W₁ W₂ : ℝ→ℂ)(b X₁ X₂ t₁ t₂ E : ℝ),0≤b → 0<X₁ → 0<X₂ → 0≤E →
      Function.support W₁⊆Set.Iic b → Function.support W₂⊆Set.Iic b →
      (∀u∈rows,0≤ρ u) → (∀u∈rows,∀I,¬Supported I → idealCoeff (χ u) I=0) →
      (∀I,Supported I → ((I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) →
        primeSupport I⊆primeValues S) →
      (∀(T : Finset α)(frozen : T→S),Function.Injective frozen →
        ∀d∈divisorPool (supportedRectangle S b X₁ X₂),
          (∑u∈rows,ρ u*‖polynomial (χ u) false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
            polynomial (χ u) false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
            remainingSum T (naturalCoefficients (χ u) S pool β P) frozen (fun _=>1)‖^2)≤E) →
      (∑u∈rows,ρ u*‖row false S (χ u) pool β P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂‖^2)≤C*X^ε*E := by
  choose CT hCT hbound using fun T : Finset α=>
    actual_subpower_energy (α:=T) false B ε hB hε
  let C := 1+∑T : Finset α,CT T
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _=>(hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨(Fintype.card (Finset α):ℝ)^2*C,by positivity,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ t₁ t₂ E
    hb hX₁ hX₂ hE hW₁ hW₂ hρ hχ henclose hchildren
  let D := divisorPool (supportedRectangle S b X₁ X₂)
  let G (T : Finset α) (frozen : T→S) (d : Id×Id) (u : Row) :=
    polynomial (χ u) false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
      polynomial (χ u) false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
      remainingSum T (naturalCoefficients (χ u) S pool β P) frozen (fun _=>1)
  let F (T : Finset α) (u : Row) := ∑frozen∈frozenChoices T S,∑d∈D,
    scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false)
      (fun i : T=>pool i.val) (fun i : T=>β i.val) (fun i : T=>P i.val) frozen d * G T frozen d u
  have hF (T : Finset α) : (∑u∈rows,ρ u*‖F T u‖^2)≤C*X^ε*E := by
    have hh := hbound T X hX S hS (frozenChoices T S)
      (fun t ht=>(Finset.mem_filter.mp ht).2) (fun _=>D)
      (fun _ _ d hd=>⟨(divisor_supported hd).1,(divisor_supported hd).2.1⟩)
      (fun _ _ d hd=>(divisor_supported hd).2.2)
      rows ρ χ (fun i : T=>pool i.val) (fun i : T=>β i.val) (fun i : T=>P i.val)
      (fun i=>hP i.val) (fun i=>hp i.val) (fun i=>hβ i.val) (G T) E hE hρ
      (fun t ht d hd=>hchildren T t (Finset.mem_filter.mp ht).2 d hd)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCTC T) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hE)
  have hid (u : Row) (hu : u∈rows) : row false S (χ u) pool β P
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂=∑T : Finset α,F T u :=
    literal_forward_expansion S (χ u) pool β P W₁ W₂ b X₁ X₂ t₁ t₂
      hb hX₁ hX₂ hW₁ hW₂ (hχ u hu) henclose
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ F F (fun _=>1)
    (C*X^ε*E) hρ (fun _=>zero_le_one) (by intros; simp) hF
  calc
    _ = ∑u∈rows,ρ u*‖∑T : Finset α,F T u‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hid u hu]
    _ ≤ _ := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,mul_assoc] using hh

/-- Compact radial summation preserves the finite positive-norm estimate.
Off-support character vanishing is required only on retained physical rows. -/
theorem radial_forward_energy (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X : ℝ,1≤X → ∀S : Finset PrimeIdeal,
      (∀Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤X) →
    ∀(χ : O→Character)(pool : α→Finset Id)(β : α→Id→ℂ)(P : α→ℝ),
      (∀i,0<P i) → (∀i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ)≤2*P i) →
      (∀i I,I∈pool i → ‖β i I‖≤B) →
    ∀(W₁ W₂ : ℝ→ℂ)(b X₁ X₂ t₁ t₂ E : ℝ),0≤b → 0<X₁ → 0<X₂ → 0≤E →
      Function.support W₁⊆Set.Iic b → Function.support W₂⊆Set.Iic b →
    ∀(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial →
      (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → ∀I,¬Supported I → idealCoeff (χ z) I=0) →
      (∀I,Supported I → ((I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) →
        primeSupport I⊆primeValues S) →
      (∀(T : Finset α)(frozen : T→S),Function.Injective frozen →
        ∀d∈divisorPool (supportedRectangle S b X₁ X₂),
          radialEnergy (fun z=>polynomial (χ z) false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
            polynomial (χ z) false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
            remainingSum T (naturalCoefficients (χ z) S pool β P) frozen (fun _=>1)) keep Φ K≤E) →
      radialEnergy (fun z=>row false S (χ z) pool β P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂) keep Φ K≤C*X^ε*E := by
  obtain ⟨C,hC,hfinite⟩ := finite_forward_energy (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ t₁ t₂ E
    hb hX₁ hX₂ hE hW₁ hW₂ keep Φ K radial hK hs hΦ hχ henclose hchildren
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
  intro rows
  let rows' := rows.filter keep
  let ρ (z : O) := (Φ (‖eisEmbedding z‖^2/K)).re
  have hchild (T : Finset α) (frozen : T→S) (hf : Function.Injective frozen)
      (d : Id×Id) (hd : d∈divisorPool (supportedRectangle S b X₁ X₂)) :
      (∑z∈rows',ρ z*‖polynomial (χ z) false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
        polynomial (χ z) false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
        remainingSum T (naturalCoefficients (χ z) S pool β P) frozen (fun _=>1)‖^2)≤E := by
    let G (z : O) := polynomial (χ z) false W₁ (X₁/(d.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
      polynomial (χ z) false W₂ (X₂/(d.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
      remainingSum T (naturalCoefficients (χ z) S pool β P) frozen (fun _=>1)
    have hsum := compact_radial_summable G keep Φ K radial hK hs
    have hh := hsum.sum_le_tsum rows' (fun z _=>by
      split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
    apply (le_of_eq ?_).trans (hh.trans (hchildren T frozen hf d hd))
    apply Finset.sum_congr rfl
    intro z hz
    have hk := (Finset.mem_filter.mp hz).2
    simp only [hk,ite_true]
    change ρ z*‖G z‖^2=‖G z‖^2*ρ z
    ring
  have hh := hfinite X hX S hS rows' ρ χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ t₁ t₂ E
    hb hX₁ hX₂ hE hW₁ hW₂ (fun z _=>hΦ z)
    (fun z hz=>hχ z (Finset.mem_filter.mp hz).2) henclose hchild
  apply (le_of_eq ?_).trans hh
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hk : keep z <;> simp only [hk,ite_true,ite_false]
  change ‖_‖^2*ρ z=ρ z*‖_‖^2
  ring

open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor QuadraticInitialBound NativeFiniteHoles
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The canonical forward family with its actual prime enclosure. Its
analytic child input is supplied, and every cutoff loss is paid by epsilon.
Common ordinary punctures and the Poisson prefactors are separate steps. -/
theorem canonical_forward_children
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
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
      radialEnergy (fun z=>row false (enclosure (Cap*Z^Lcap))
        (naturalCharacter s.character z)
        (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
        (fun i=>heightCoefficient (holeCoefficient (fun i I=>
          idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) R₀ i) t)
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control control)^2*
        (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε) := by
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let δ := ε/(2*(Lcap+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Cf,hCf,hforward⟩ := radial_forward_energy (α:=α) B δ (zero_le_one.trans hB) hδ
  obtain ⟨degree,S,hchildren⟩ := canonical_uniform_remaining_children (α:=α) M H hH Holes W
    a b radial Mcap L Lslot Lcap Cap (ε/2) lo hi κ hWs hW ha haUpper hb hrad hM
    hLslot hLcap hCap (half_pos hε) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,S,?_⟩
  intro η₀ hQη
  obtain ⟨Cc,hCc,hchildren⟩ := hchildren η₀ hQη
  refine ⟨Cf*Cap^δ*Cc,by positivity,hchildren.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  let X := Cap*Z^Lcap
  let primes := enclosure X
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (P i) (σ i) (freq i) I
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let E := Cc*diagonalControl s.radial.profile*
    ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
    (1+|t|+V)^degree*Z^(s.width+κ*(∑i,w i)+ε/2)
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le (by linarith)
    (Real.one_le_rpow hZ.1.le hLcap0)
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i := by
    refine ⟨(Finset.mem_filter.mp hI).2,?_⟩
    exact canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,B] using he
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have henclose (I : Id) (hI : Supported I)
      (hlen : (I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) :
      primeSupport I⊆primeValues primes := by
    apply support_enclosed X I hI
    have hc (Y : ℝ) (hY : 0<Y) (hYc : Y≤Z^L) : b*Y≤X :=
      mul_le_mul hCapb (hYc.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hLordinary))
        hY.le hCap0.le
    exact hlen.elim (fun h=>h.trans (hc X₁ hX₁ hc₁)) (fun h=>h.trans (hc X₂ hX₂ hc₂))
  have he := hforward X hX primes (enclosure_bound X) (fun z=>naturalCharacter s.character z)
    pool βc P hP hp hβc W₁ W₂ b X₁ X₂ t₁ t₂ E (zero_le_one.trans hb) hX₁ hX₂ hE
    (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2)
    (effectiveState s).radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos
    s.radial_support s.radial.nonneg
    (fun z hz=>natural_character_off_supported s.character z (s.row_ne_zero z hz.1))
    henclose (by
      intro T frozen _ d hd
      have hn := divisor_supported hd
      exact hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bmask s hQ hwidth
        W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂) X₁ X₂ hX₁ hX₂ hc₁ hc₂
        d.1 d.2 hn.1 hn.2.1 T frozen)
  have hcost := mul_le_mul_of_nonneg_left
    (cutoff_loss Z Lcap Cap ε (s.width+κ*(∑i,w i)) hZ.1.le hLcap0 hCap0.le hε)
    (show 0≤Cf*Cc*diagonalControl s.radial.profile*
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂)).control S)^2*
      (1+|t|+V)^degree by positivity)
  apply he.trans
  convert hcost using 1 <;> dsimp only [δ,X,E] <;> ring

end
end Candidate.FourthPower.NativeForwardEnergy
