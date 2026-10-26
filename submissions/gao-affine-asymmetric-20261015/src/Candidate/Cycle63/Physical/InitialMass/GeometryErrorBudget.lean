/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorColumnFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorScalarPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowLabelBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Cycle63Moment Cycle63FinalError
open CenteredMomentFirstChildProfileControl CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentFirstScale Cycle63FinalErrorCapacity RayFourExpansion
open CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O
local instance errorBudgetDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Actual supported second labels, including all inactive subsets, over
one squarefree residual projector shell. These are finite geometry gates. -/
structure ErrorResidualLabelShell (Z T B : ℝ) where
  projectors : Finset (Ideal O)
  labels : Ideal O→Finset FirstSourceLabel
  squarefree : ∀D∈projectors,Squarefree D
  dyad : ∀D∈projectors,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T
  supported : ∀D∈projectors,∀v∈labels D,Supported v.1.1 ∧ Supported v.1.2
  equalSupport : ∀D∈projectors,∀v∈labels D,primeSupport v.1.1=primeSupport v.1.2
  divides : ∀D∈projectors,∀v∈labels D,D∣v.1.1 ∧ D∣v.1.2
  norm : ∀D∈projectors,∀v∈labels D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B

/-- Exact image of the active extraction menu in the unpruned source. -/
def errorLiftedActiveAllocations {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ) : Finset (actualAllocations s.pools (Q^k)) :=
  Finset.univ.image (errorActiveAllocation s (Q^k))

theorem error_lifted_active_allocations_card {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ) :
    (errorLiftedActiveAllocations s Q k).card=
      (actualAllocations (activeInput s).pools (Q^k)).card := by
  unfold errorLiftedActiveAllocations
  rw [Finset.card_image_of_injective _ (errorActiveAllocation_injective s (Q^k)),
    Finset.card_univ,Fintype.card_coe]

/-- Reindex the literal active menu without adding unpruned allocations. -/
theorem error_lifted_active_allocations_sum {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ)
    (f : actualAllocations s.pools (Q^k)→ℝ) :
    (∑B : errorLiftedActiveAllocations s Q k,f B.val)=
      ∑B : actualAllocations (activeInput s).pools (Q^k),f (errorActiveAllocation s (Q^k) B) := by
  rw [Finset.sum_coe_sort (errorLiftedActiveAllocations s Q k) f]
  unfold errorLiftedActiveAllocations
  rw [Finset.sum_image]
  intro B _ D _ h
  exact errorActiveAllocation_injective s (Q^k) h

/-- The shell loss is paid by a genuine second-label divisor, not by the
frequency ideal. -/
theorem actual_error_projector_height_cap (Z T B εshell : ℝ)
    (hZ : 0<Z)(hT : 0≤T)(he : 0≤εshell)(D C : Ideal O)
    (hC : Supported C)(hDC : D∣C)(hdyad : T≤(D.absNorm:ℝ))
    (hcap : (C.absNorm:ℝ)≤Z^B) :
    (2*T)^(3*εshell)≤2^(3*εshell)*Z^(B*(3*εshell)) := by
  have hn : (D.absNorm:ℝ)≤C.absNorm := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm hDC)
  have hp := Real.rpow_le_rpow (by positivity : 0≤2*T)
    (mul_le_mul_of_nonneg_left (hdyad.trans (hn.trans hcap)) (by norm_num : (0:ℝ)≤2))
    (by positivity : 0≤3*εshell)
  apply hp.trans_eq
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZ.le _),
    ←Real.rpow_mul hZ.le]

/-- The scalar remaining after the genuine paid column estimate. Its
prime shifts and extracted source volume have not been canceled by definition. -/
def extractedErrorLabelScalar (reflected second : Bool) (l v : FirstSourceLabel)
    (Z M a δ reserve error εcommon V Vextract : ℝ) (p : O) (k : ℕ) : ℝ :=
  (firstErrorTailRadius reflected l Z M V a δ reserve p k/Vextract)*
    (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
    Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      v.1.1 v.1.2 v.2.val+(error-M*branchReserve k)+errorRemoval p Z k-errorMoving p Z k)

/-- Both child restrictions preserve the original fixed profile envelope.
The four mass powers remain visible until this pointwise payment. -/
theorem actual_error_fixed_source_factor {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤Cs)(hbp : 1≤bp)
    (s : Input α)(hcard : Fintype.card α≤N)(hM : ∀j,s.M j≤Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)(q : Chain s)(η : Character)(v : ℝ) :
    let src := withHeight q.extracted η v
    src.toData.profileFactor*(∏j,src.M j)^2≤2*bp^2*Cs^(4*N) := by
  intro src
  have hfirst := child_mass s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
  have hextract := child_mass q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂
  have hm : mass src≤mass s := hextract.trans hfirst
  have hprod : mass s≤Cs^N := by
    apply (Finset.prod_le_prod₀ (fun j _=>zero_le_one.trans (s.M_ge_one j)) (fun j _=>hM j)).trans
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hCs hcard
  have hbound := pow_le_pow_left₀ (mass_nonneg src) (hm.trans hprod) 4
  have hfactor : src.toData.profileFactor*(∏j,src.M j)^2=2*bp^2*(mass src)^4 := by
    change (2*(max 1 s.b₁*max 1 s.b₂))*(∏j,src.M j)^2*(∏j,src.M j)^2=_
    rw [hb₁,hb₂,max_eq_right hbp]
    dsimp only [mass]
    ring
  rw [hfactor]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq
  rw [←pow_mul]
  congr 2
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Full extracted scalar payment: original first labels, residual
projectors, all second labels, all ray characters and actual active prime
allocations. The original prime denominator cancels only after counting. -/
theorem eventual_actual_error_full_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ),
    0≤εcommon → 1≤T → p≤B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
    ∀labels : Finset FirstSourceLabel,
    (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
    (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
    (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
    (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
    (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
    (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
    ∀Rfirst : Ideal O,
    ∀alloc : (l : labels)→actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1),
    ∀(χ : labels→Character)(t : ℝ),
    (∀l : labels,frozenCoefficient (alloc l).val (if reflected then l.val.1.2 else l.val.1.1)
      Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→Input (CenteredMomentCommonProfile.liveIndices (alloc l).val) := fun l=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l) (χ l) t
    ∀P : Finset (Ideal O),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
    (∀l : labels,∀q : elementPool P,∀j I,I∈(u l).slots j→IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels) (q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l q i→Character)
      (vheight : ℝ)
      (shell : (l : labels)→(q : elementPool P)→(i : Fin 3)→RayCharacter→Bps l q i→
        ErrorResidualLabelShell Z T B),
    (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
      ∑l : labels,∑ψ : RayCharacter,∑Bp : Bps l q i,
        ∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
              (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ)*
        ∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*Z^(-M*branchReserve (errorIndex i+1)) := by
  obtain ⟨Kf,hKf,hfirst⟩ := actual_first_low_label_count B (ε/2) hB (half_pos hε)
  obtain ⟨Ks,hKs,hsecond⟩ := actual_low_reciprocal_projector_shell B (ε/2) hB (half_pos hε)
  let Kray : ℝ := Fintype.card RayCharacter
  have hKray : 0<Kray := by dsimp [Kray]; exact_mod_cast Fintype.card_pos
  refine ⟨56*Kray*Kf*Ks,by positivity,?_⟩
  filter_upwards [eventual_actual_twice_error_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a δ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Rfirst alloc χ t halloc
    u P hne hprime hbad hslot Bps υ vheight shell
  have hZ : 0<Z := by linarith
  have hcount := hfirst Z (by linarith) p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpair (l : labels)(q : elementPool P)(i : Fin 3)
      (ψ : RayCharacter)(Bp : Bps l q i) :
      (∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
        extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
          (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
            (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*(Ks*Z^(ε/2)) := by
    let sh := shell l q i ψ Bp
    have hc := hsecond second Z T hZ2 hT sh.projectors sh.squarefree sh.dyad sh.labels
      sh.supported sh.equalSupport sh.divides sh.norm
    calc
      _ ≤ ∑D∈sh.projectors,∑v∈sh.labels D,
          Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))/
            ((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        apply Finset.sum_le_sum
        intro v hv
        have hq := elementPool_data P hprime hbad q.val q.property
        have hq0 : q.val≠0 := hq.1.ne_zero
        have hm := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1 (hsup l.val l.property).2
          (heq l.val l.property) Rfirst (alloc l) (χ l) t (halloc l) q.val hq0 (errorIndex i+1)
          (hslot l q) (Bp.val) (υ l q i ψ Bp) vheight
          v.1.1 v.1.2 (sh.supported D hD v hv).1 (sh.supported D hD v hv).2 v.2.val
          M a δ reserve (error-M*branchReserve (errorIndex i+1)) εcommon B hecommon (by
            cases second
            · exact (sh.norm D hD v hv).1
            · exact (sh.norm D hD v hv).2)
        apply hm.trans
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith [hgeom l.val l.property]
      _ = Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*
          (∑D∈sh.projectors,∑v∈sh.labels D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
        simp only [Finset.mul_sum,mul_one_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hZ.le _)
  have hprimeIdeal (q : elementPool P) : Prime (Ideal.span {q.val}) := by
    have h := (elementPool_data P hprime hbad q.val q.property).2.1
    exact hprime _ h
  have halloccount (l : labels)(q : elementPool P)(i : Fin 3) :
      (Fintype.card (Bps l q i):ℝ)≤errorIndex i+2 := by
    have hh := actual_amplification_allocations_card (u l).pools
      (Ideal.span {q.val}) (hprimeIdeal q) (errorIndex i+1) (by
        intro j I hI
        exact ⟨(u l).pools_ne _ _ hI,hslot l q j I hI⟩)
    have hsubset : (errorLiftedActiveAllocations (u l) (Ideal.span {q.val})
        (errorIndex i+1)).card≤(actualAllocations (u l).pools
          ((Ideal.span {q.val})^(errorIndex i+1))).card := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
    dsimp only [Bps]
    rw [Fintype.card_coe]
    exact_mod_cast hsubset.trans hh
  have htotal (q : elementPool P)(i : Fin 3) :
      (∑l : labels,∑ψ : RayCharacter,∑Bp : Bps l q i,
        ∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
              (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      Kray*(errorIndex i+2:ℝ)*
        (Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-M*branchReserve (errorIndex i+1)) := by
    let E := Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*(Ks*Z^(ε/2))
    have hE : 0≤E := by dsimp [E]; positivity
    calc
      _ ≤ ∑l : labels,∑ψ : RayCharacter,∑_Bp : Bps l q i,E := by
        apply Finset.sum_le_sum
        intro l _
        exact Finset.sum_le_sum (fun ψ _=>Finset.sum_le_sum (fun Bp _=>hpair l q i ψ Bp))
      _ ≤ ∑_l : labels,Kray*(errorIndex i+2:ℝ)*E := by
        apply Finset.sum_le_sum
        intro l _
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        dsimp only [Kray]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (halloccount l q i) hE)
          (Nat.cast_nonneg (Fintype.card RayCharacter))
      _ = (labels.card:ℝ)*(Kray*(errorIndex i+2:ℝ)*E) := by simp
      _ ≤ (Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Kray*(errorIndex i+2:ℝ)*E) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by
        dsimp only [E]
        simp only [Real.rpow_add hZ,Real.rpow_sub hZ]
        have he : Z^ε=Z^(ε/2)*Z^(ε/2) := by rw [←Real.rpow_add hZ,add_halves]
        rw [he,neg_mul,Real.rpow_neg hZ.le]
        ring
  have hpcount : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hprime hbad]
  have hpc : (0:ℝ)<P.card := by exact_mod_cast hne.card_pos
  calc
    _ ≤ (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        (Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-M*branchReserve (errorIndex i+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun q _=>Finset.sum_le_sum
        (fun i _=>mul_le_mul_of_nonneg_left (htotal q i) (by positivity)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hpcount,Finset.mul_sum]
      field_simp
      apply Finset.sum_congr rfl
      intro i hi
      ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_error_full_label_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_error_fixed_source_factor

#print axioms OAI.SevenEighths.Cycle63InitialMass.error_lifted_active_allocations_card
#print axioms OAI.SevenEighths.Cycle63InitialMass.error_lifted_active_allocations_sum
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_error_projector_height_cap
