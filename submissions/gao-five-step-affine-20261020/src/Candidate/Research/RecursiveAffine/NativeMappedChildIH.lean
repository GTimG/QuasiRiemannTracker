/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualReachableChild
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Reindex

set_option autoImplicit false
set_option maxHeartbeats 450000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonRadialData
open CenteredMomentEnergyReindex Cycle63Moment Cycle153SourceReturn
open Cycle153Reachable Cycle153HighProvider

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {Current : Type} [Fintype Current]
local instance mappedCurrentDecidableEq : DecidableEq Current := Classical.decEq _
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

theorem nativeMappedFrequencyBound (embedding : Current↪alpha)(J R : Finset Current)
    (frequency : alpha→ℝ)(height : ℝ)(hfreq : ∀i,|frequency (embedding i)| ≤ height) :
    ∀i : (J\R).map embedding,|frequency i| ≤ height := by
  intro i
  obtain ⟨j,hj,heq⟩ := Finset.mem_map.mp i.property
  rw [←heq]
  exact hfreq j

/-- Actual native current carriers may be finite subtypes. Treating the
carrier abstractly keeps its classical native allocation instance fixed;
the literal embedding, rather than an instance cast, identifies every
surviving slot with its original ray. -/
theorem actual_mapped_child_from_strict_depth
    (hH : RayOrthogonality.globalUnits M ≤ H)(C : SourceContext (α:=alpha) M H)
    (parentStage childStage : Fin 4)(hdepth : parentStage.val<childStage.val)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ))
    (hIH : StrictDepthIH hH C parentStage constant eps Bsrc control degree boxes)
    (embedding : Current↪alpha)(Zparent parentUnit u oldMask : ℝ)
    (hZ : 1<Zparent)(hu : 0<u)(hu1 : u ≤ 1)(hbase : Zparent=C.globalBase^parentUnit)
    (st : NaturalState Zparent oldMask 2)(hwidth : st.width ≤ u)
    (hmask : (st.puncture.absNorm:ℝ) ≤ (Zparent^u)^(20:ℝ))(J R : Finset Current)
    (p : Profiles (1/4) (9/4))(X1 X2 : ℝ)(hX1 : 0<X1)(hX2 : 0<X2)
    (P : PrefixHighPresentation (prefixDictionary childStage.val C.etaSeed) st.character st.puncture)
    (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap childStage.val))
    (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)(t height : ℝ)(hheight : 0 ≤ height)
    (hfreq : ∀i : Current,|C.frequency (embedding i)| ≤ height)
    (geom : NativeChildGeometry C childStage Zparent parentUnit u ((J\R).map embedding) X1 X2)
    (hPhistory : Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
      modelMissing childStage geom.coordinates+modelReduction childStage geom.coordinates+
        ((childStage.val:ℝ)+1)/1000000000000000) :
    let child := nodeOfNativeContinuation C childStage Zparent parentUnit u oldMask hu hbase st hwidth hmask
      ((J\R).map embedding) p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight
      (nativeMappedFrequencyBound embedding J R C.frequency height hfreq) geom hPhistory
    ∃out : NodeOutput hH child (constant childStage) (eps childStage) (Bsrc childStage)
      (control childStage) (degree childStage) (boxes childStage),
    let F := rebaseDepthReturnedFamily hZ hu hu1 C.normCap_nonneg out.family
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : ↥(J\R)=>CenteredMomentPrimeSlot.primePool M H 2
        (Zparent^(C.originalWeight (embedding i.val)/parentUnit)))
      (fun (i : ↥(J\R)) I=>idealCoeff
        (relativeCharacter M H hH C.etaSeed (C.theta (embedding i.val))) I*
        HeckePrimeAnnular.annularWeight C.W (Zparent^(C.originalWeight (embedding i.val)/parentUnit))
          (C.sigma (embedding i.val)) (C.frequency (embedding i.val)) I)
      (fun i : ↥(J\R)=>Zparent^(C.originalWeight (embedding i.val)/parentUnit)) X1 X2
      st.radial.keep st.radial.profile st.radial.scale ≤
      constant childStage*QuadraticInitialBound.diagonalControl child.state.radial.profile*
        (child.profiles.control (control childStage))^2*(1+|child.t|+child.height)^(degree childStage)*
        ((Zparent^u)^(1+eps childStage)+F.value) := by
  intro child
  obtain ⟨out⟩ := hIH childStage hdepth child
  refine ⟨out,?_⟩
  intro F
  have hvalue : F.value=out.family.value :=
    rebaseDepthReturnedFamily_value hZ hu hu1 C.normCap_nonneg out.family
  have hsource := nodeOfNativeContinuation_energy hH C childStage Zparent parentUnit u oldMask hu hbase
    st hwidth hmask ((J\R).map embedding) p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight
    (nativeMappedFrequencyBound embedding J R C.frequency height hfreq) geom hPhistory
  have hflatten := energy_subset_map embedding (J\R) st.character st.mask 1 (p.profile 0) (p.profile 1)
    (fun i=>CenteredMomentPrimeSlot.primePool M H 2 (Zparent^(C.originalWeight i/parentUnit)))
    (fun i I=>idealCoeff (relativeCharacter M H hH C.etaSeed (C.theta i)) I*
      HeckePrimeAnnular.annularWeight C.W (Zparent^(C.originalWeight i/parentUnit))
        (C.sigma i) (C.frequency i) I)
    (fun i=>Zparent^(C.originalWeight i/parentUnit)) t X1 X2 st.radial.keep st.radial.profile st.radial.scale
  rw [hflatten,←hsource,hvalue]
  exact out.energy

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_mapped_child_from_strict_depth
