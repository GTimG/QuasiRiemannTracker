/- Copyright (c) 2026 Sil. Apache-2.0.
Finite weighted families inside the single common Fourier kernel.
The analytic pair premise in these generic transfer lemmas is discharged
by ArtificialSum in the actual nonexceptional block application.

-/
import Candidate.SilPrior.FourthPower.OuterFreshFixedWindows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Candidate.SilPrior.FourthPower.OuterFreshWeightedKernel
noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentActiveSource
open CenteredMomentLiveDomain CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentSecondHeightFamily CenteredMomentMobiusRegroup CenteredMomentCanonicalFirst
open CenteredMomentSecondLiveBlock CenteredMomentSecondDyadicRowSupport CenteredMomentSecondEnergySplit
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentSecondRadicalBudget CenteredMomentSecondScaled CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentCauchy CenteredMomentExceptionalKernel
open CenteredMomentPlainChildEnergy CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentSupport
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondIdealBlockBound
open FourierBridge OuterFreshBlock OuterFreshStructure MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The extra finite family index remains INSIDE the Fourier row index.
No family cardinality or supremum of individual energies is introduced. -/
theorem family_divisor_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (M : Fin 4→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0→|y|≤M i) (decay J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R→
      ∀{κ α β : Type*}(Ys : Finset κ)(Ls : Finset Id)(rows : κ→Finset O)
        (S : Finset α)(T : Finset β)(weight : κ→ℝ)(a : α→O)(b : β→O)
        (c : κ→Id→α→ℂ)(d : κ→Id→β→ℂ)
        (u : α→ℝ)(v : β→ℝ)(ρ x : O→ℝ)(η : O→ℂ),
      (∀y,0≤weight y)→(∀y,∀z∈rows y,‖η z‖≤1)→
      (∀y,∀z∈rows y,‖V 0 (ρ z)‖≤1)→(∀y,∀z∈rows y,‖V 1 (x z)‖≤1)→
      ∀E : ℝ,0≤E→
      (∀t : ℝ,(∑y∈Ys,weight y*∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
        ∑z∈rows y,
          ‖rowPolynomial S a (fun i=>c y L i*columnPhase (V 2) (u i) t) z‖*
          ‖rowPolynomial T b (fun j=>d y L j*star (columnPhase (V 3) (v j) t)) (-z)‖)
        ≤E*(1+‖t‖)^J)→
      (1+R)^decay*‖∑y∈Ys,(weight y:ℂ)*∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*
        ∑z∈rows y,η z*∑i∈S,∑j∈T,
          ((c y L i*idealRowHom z (Ideal.span {a i}))*
            star (d y L j*idealRowHom (-z) (Ideal.span {b j})))*
            wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤C*E := by
  obtain ⟨C,hC,hkernel⟩:=whole_kernel_paired_row_estimate W V M hM hV decay J
  refine ⟨C,hC,?_⟩
  intro R hR κ α β Ys Ls rows S T weight a b c d u v ρ x η hw hη hV₀ hV₁ E hE hpair
  let Ks : Finset (Σ _y : κ,Id×O):=Ys.sigma (fun y=>Ls×ˢrows y)
  let c' := fun (k : Σ _y : κ,Id×O)(i : α)=>
    (weight k.1:ℂ)*(UniqueFactorizationMonoid.moebius k.2.1:ℂ)*
      (c k.1 k.2.1 i*idealRowHom k.2.2 (Ideal.span {a i}))
  let d' := fun (k : Σ _y : κ,Id×O)(j : β)=>
    d k.1 k.2.1 j*idealRowHom (-k.2.2) (Ideal.span {b j})
  have hz (k : Σ _y : κ,Id×O) (hk:k∈Ks) : k.2.2∈rows k.1 :=
    (Finset.mem_product.mp (Finset.mem_sigma.mp hk).2).2
  have hnormweight (y:κ):‖(weight y:ℂ)‖=weight y := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hw y)]
  have hleft (y:κ) (L:Id) (z:O) (t:ℝ) :
      leftColumn S (c' ⟨y,(L,z)⟩) (V 2) u t=
        (weight y:ℂ)*(UniqueFactorizationMonoid.moebius L:ℂ)*
          rowPolynomial S a (fun i=>c y L i*columnPhase (V 2) (u i) t) z := by
    rw [←leftColumn_eq_rowPolynomial]
    unfold leftColumn c'
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp : ∀t:ℝ,(∑k∈Ks,‖leftColumn S (c' k) (V 2) u t‖*
      ‖rightColumn T (d' k) (V 3) v t‖)≤E*(1+‖t‖)^J := by
    intro t
    have he : (∑k∈Ks,‖leftColumn S (c' k) (V 2) u t‖*
        ‖rightColumn T (d' k) (V 3) v t‖)=
        ∑y∈Ys,weight y*∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
          ∑z∈rows y,
            ‖rowPolynomial S a (fun i=>c y L i*columnPhase (V 2) (u i) t) z‖*
            ‖rowPolynomial T b (fun j=>d y L j*star (columnPhase (V 3) (v j) t)) (-z)‖ := by
      simp only [Ks,Finset.sum_sigma,Finset.sum_product,hleft,d',
        rightColumn_eq_star_rowPolynomial,norm_star,norm_mul,hnormweight,
        Finset.mul_sum,mul_assoc]
    exact he.le.trans (hpair t)
  have hbound:=hkernel R hR Ks S T c' d' u v (fun k=>ρ k.2.2) (fun k=>x k.2.2)
    (fun k=>η k.2.2) (fun k hk=>hη k.1 k.2.2 (hz k hk))
    (fun k hk=>hV₀ k.1 k.2.2 (hz k hk)) (fun k hk=>hV₁ k.1 k.2.2 (hz k hk)) E hE hp
  apply hbound.trans_eq'
  congr 2
  simp only [Ks,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,c',d']
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem family_ray_reorder {κ : Type*} (Ys : Finset κ) (Ls : Finset Id)
    (weight : κ→ℂ) (ray : RayCharacter→RayCharacter→ℂ)
    (matrix : κ→Id→RayCharacter→RayCharacter→ℂ) :
    (∑y∈Ys,weight y*∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*
      ∑χ:RayCharacter,∑ρ:RayCharacter,ray χ ρ*matrix y L χ ρ)=
      ∑χ:RayCharacter,∑ρ:RayCharacter,ray χ ρ*
        ∑y∈Ys,weight y*∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*matrix y L χ ρ := by
  simp only [Finset.mul_sum]
  calc
    _=∑y∈Ys,∑χ:RayCharacter,∑ρ:RayCharacter,∑L∈Ls,
        weight y*((UniqueFactorizationMonoid.moebius L:ℂ)*(ray χ ρ*matrix y L χ ρ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_comm]
    _=∑χ:RayCharacter,∑ρ:RayCharacter,∑y∈Ys,∑L∈Ls,
        weight y*((UniqueFactorizationMonoid.moebius L:ℂ)*(ray χ ρ*matrix y L χ ρ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_comm]
    _=_ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ρ hρ
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro L hL
      ring

private theorem scaled_norm_sum {α:Type*} (S:Finset α)(c f:α→ℂ)
    (r:ℝ)(hr:0≤r)(B:α→ℝ)(hB:∀i∈S,r*‖f i‖≤B i) :
    r*‖∑i∈S,c i*f i‖≤∑i∈S,‖c i‖*B i := by
  calc
    _≤r*∑i∈S,‖c i*f i‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _=∑i∈S,‖c i‖*(r*‖f i‖):=by
      simp only [Finset.mul_sum,norm_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _≤_:=Finset.sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

/-- Family version of whole_kernel_actual_second_pair. The finite
reciprocity-ray mass is paid once, and the selected family stays inside
the common Fourier estimate throughout. -/
theorem family_actual_kernel (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤M i)(hV:∀i y,V i y≠0→|y|≤M i)(decay J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀R:ℝ,0<R→
      ∀{κ α β:Type*}(Ys:Finset κ)(rows:κ→Finset O)(weight:κ→ℝ)
        (S:Finset α)(T:Finset β)(D E A₀:O)(a:α→O)(b:β→O)
        (hD:Supported (Ideal.span {D}))(hE:Supported (Ideal.span {E}))
        (ha:∀i,Supported (Ideal.span {a i}))(hb:∀j,Supported (Ideal.span {b j})),
      (goodLambda^2∣D-1)→(goodLambda^2∣E-1)→
      (∀i,goodLambda^2∣a i-1)→(∀j,goodLambda^2∣b j-1)→
      (∀i,IsCoprime (D*E) (a i))→(∀j,IsCoprime (D*E) (b j))→
      ∀(q:O→ℂ)(c:κ→α→ℂ)(d:κ→β→ℂ)(u:α→ℝ)(v:β→ℝ)(ρ x:O→ℝ),
      (∀y,0≤weight y)→
      (∀y,∀z∈rows y,‖q z*actualCorrelation D E hD hE (A₀*z)‖≤1)→
      (∀y,∀z∈rows y,‖V 0 (ρ z)‖≤1)→(∀y,∀z∈rows y,‖V 1 (x z)‖≤1)→
      ∀E0:ℝ,0≤E0→
      (∀χ ξ:RayCharacter,∀t:ℝ,
        (∑y∈Ys,weight y*∑L∈divisorPool T (fun j=>Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows y,
          ‖rowPolynomial S a (fun i=>divisorCoefficient L a (movingCoefficient A₀ a (c y)) χ i*
            columnPhase (V 2) (u i) t) z‖*
          ‖rowPolynomial T b (fun j=>divisorCoefficient L b (movingCoefficient A₀ b (d y)) (ξ⁻¹) j*
            star (columnPhase (V 3) (v j) t)) (-z)‖)≤E0*(1+‖t‖)^J)→
      (1+R)^decay*‖∑y∈Ys,(weight y:ℂ)*∑z∈rows y,q z*∑i∈S,∑j∈T,
        (if IsCoprime (a i) (b j) then actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0)*(c y i*star (d y j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤C*E0 := by
  obtain ⟨C,hC,hkernel⟩:=family_divisor_kernel W V M hM hV decay J
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR κ α β Ys rows weight S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hw hq hV₀ hV₁ E0 hE0 hpair
  let Ls:=divisorPool T (fun j=>Ideal.span {b j})
  let matrix:=fun (y:κ)(L:Id)(χ ξ:RayCharacter)=>
    ∑z∈rows y,(q z*actualCorrelation D E hD hE (A₀*z))*∑i∈S,∑j∈T,
      ((divisorCoefficient L a (movingCoefficient A₀ a (c y)) χ i*idealRowHom z (Ideal.span {a i}))*
        star (divisorCoefficient L b (movingCoefficient A₀ b (d y)) (ξ⁻¹) j*
          idealRowHom (-z) (Ideal.span {b j})))*wholeKernel W V R (ρ z) (x z) (u i) (v j)
  let f:=fun χ ξ:RayCharacter=>∑y∈Ys,(weight y:ℂ)*∑L∈Ls,
    (UniqueFactorizationMonoid.moebius L:ℂ)*matrix y L χ ξ
  have hf (χ ξ:RayCharacter):(1+R)^decay*‖f χ ξ‖≤C*E0:=
    hkernel R hR Ys Ls rows S T weight a b
      (fun y L=>divisorCoefficient L a (movingCoefficient A₀ a (c y)) χ)
      (fun y L=>divisorCoefficient L b (movingCoefficient A₀ b (d y)) (ξ⁻¹))
      u v ρ x (fun z=>q z*actualCorrelation D E hD hE (A₀*z)) hw hq hV₀ hV₁ E0 hE0 (hpair χ ξ)
  have hexpand (y:κ):
      (∑z∈rows y,q z*∑i∈S,∑j∈T,
        (if IsCoprime (a i) (b j) then actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0)*(c y i*star (d y j))*wholeKernel W V R (ρ z) (x z) (u i) (v j))=
      ∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*∑χ:RayCharacter,∑ξ:RayCharacter,
        pairCoeff (phaseTable D E) χ ξ*matrix y L χ ξ :=
    actual_scaled_row_children (rows y) S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
      q (c y) (d y) (fun z i j=>wholeKernel W V R (ρ z) (x z) (u i) (v j))
  simp_rw [hexpand]
  rw [family_ray_reorder]
  change (1+R)^decay*‖∑χ:RayCharacter,∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ‖≤_
  calc
    _≤∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0) := by
      have hh:=scaled_norm_sum Finset.univ (fun _:RayCharacter=>(1:ℂ))
        (fun χ=>∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ) ((1+R)^decay) (by positivity)
        (fun χ=>∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0))
        (fun χ _=>scaled_norm_sum Finset.univ _ _ ((1+R)^decay) (by positivity) _ (fun ξ _=>hf χ ξ))
      simpa only [one_mul,norm_one] using hh
    _=(∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖)*(C*E0) := by
      simp only [Finset.sum_mul]
    _≤256*(C*E0):=mul_le_mul_of_nonneg_right (phaseTable_mass D E) (mul_nonneg hC hE0)
    _=_:=by ring

/-- Actual normalized physical blocks, with a selected-dependent row set
and coefficient for each family member. The kernel constant is uniform
before the family, source pool, common labels and all scalar scales. -/
theorem weighted_normalized_block (Φ:𝓢(ℝ,ℂ))(decay J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀{κ:Type*}(Ys:Finset κ)(weight:κ→ℝ)(rows:κ→Finset O),
      (∀y,0≤weight y)→
      ∀(τ:Character)(t:ℝ)(S:Finset Id)(β:κ→Id→ℂ)
        (C₀ E₀:Id)(hC:Supported C₀)(hE:Supported E₀),primeSupport C₀=primeSupport E₀→
      ∀(U:Finset (CommonIndex C₀ E₀))(radius K:ℝ)(n:Fin 4→ℤ),
      ∀Eraw:ℝ,0≤Eraw→
      (∀χ ρ:RayCharacter,∀w:ℝ,
        (∑y∈Ys,weight y*rawKernelPair τ t S (β y) C₀ E₀ hC hE U χ ρ w
          (dyadicScale (n 2)) (dyadicScale (n 3)) (rows y))≤Eraw*(1+‖w‖)^J)→
      (1+kernelScale n)^decay*‖∑y∈Ys,(weight y:ℂ)*
        normalizedBlock τ t S (β y) C₀ E₀ hC hE U radius (rows y) Φ K n‖≤C*Eraw := by
  obtain ⟨C,hC,hbound⟩:=family_actual_kernel Φ (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ z hz=>logAnnulus_enclosure z hz) decay J
  refine ⟨C,hC,?_⟩
  intro κ Ys weight rows hw τ t S β C₀ E₀ hC₀ hE₀ hCE U radius K n Eraw hEraw hpair
  have hcopE (I:sectorPool E₀ hE₀.1 S):
      IsCoprime (primaryGenerator C₀*primaryGenerator E₀) (sectorElement E₀ hE₀.1 S I) := by
    simpa only [mul_comm] using sectorElement_coprime E₀ C₀ hE₀ hC₀ hCE.symm S I
  have he:=hbound (kernelScale n) (kernelScale_pos n) Ys rows weight Finset.univ Finset.univ
    (primaryGenerator C₀) (primaryGenerator E₀) (oldMoving C₀ E₀ U)
    (sectorElement C₀ hC₀.1 S) (sectorElement E₀ hE₀.1 S)
    ((supported_span_primaryGenerator_iff C₀).mpr hC₀) ((supported_span_primaryGenerator_iff E₀).mpr hE₀)
    (sectorElement_supported C₀ hC₀.1 S) (sectorElement_supported E₀ hE₀.1 S)
    (primaryGenerator_spec C₀ (supported_primaryGenerator_ne_zero C₀ hC₀)).2
    (primaryGenerator_spec E₀ (supported_primaryGenerator_ne_zero E₀ hE₀)).2
    (sectorElement_primary C₀ hC₀.1 S) (sectorElement_primary E₀ hE₀.1 S)
    (sectorElement_coprime C₀ E₀ hC₀ hE₀ hCE S) hcopE
    (retainedScalar C₀ E₀ U radius)
    (fun y I=>β y (C₀*I)*heightCoeff τ t I)
    (fun y I=>β y (E₀*I)*heightCoeff τ t I)
    (fun I:sectorPool C₀ hC₀.1 S=>Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 2)))
    (fun I:sectorPool E₀ hE₀.1 S=>Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 3)))
    (fun _=>Real.log (secondEffectiveScale C₀ E₀ (oldMoving C₀ E₀ U) K/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) hw
    (fun y z hz=>actual_retained_scalar_norm C₀ E₀ hC₀ hE₀ hCE U radius z)
    (fun y z hz=>logAnnulus_norm _) (fun y z hz=>logAnnulus_norm _) Eraw hEraw
    (by simpa only [rawKernelPair,sectorElement_span] using hpair)
  have hcop (I:sectorPool C₀ hC₀.1 S)(J:sectorPool E₀ hE₀.1 S):
      IsCoprime (primaryGenerator (I:Id)) (primaryGenerator (J:Id))↔IsCoprime (I:Id) (J:Id) := by
    change IsCoprime (sectorElement C₀ hC₀.1 S I) (sectorElement E₀ hE₀.1 S J)↔_
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simpa only [normalizedBlock,kernelScale,oldMoving,sectorElement_span,idealCorrelation,
    primaryGenerator_mul,sectorElement,hcop] using he

end
end Candidate.SilPrior.FourthPower.OuterFreshWeightedKernel
