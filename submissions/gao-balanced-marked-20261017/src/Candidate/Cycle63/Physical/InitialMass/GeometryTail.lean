import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
local instance geometryTailDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- One tail constant and threshold work before the surviving slot subset
is chosen. The bound is for the literal original discarded energy. -/
theorem actual_subset_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (b wlo whi B ξ saving : ℝ)(hb : 0≤b)(hwlo : 0<wlo)
    (hwhi : 0≤whi)(hB : 0≤B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(J : Finset α)(s : Input J)(W₁ W₂ : 𝓢(ℝ,ℂ)),s.W₁=W₁ → s.W₂=W₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi →
      (∀i,s.hi i≤b) → ∀(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),
      0<K → volume s.toData≤Z^B → Tsec≤Z^B → (volume s.toData)^2/K≤Tsec →
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  have hex (J : Finset α) := second_input_tail_arbitrary_saving (fun _ : J=>b)
    wlo whi B ξ saving (fun _=>hb) hwlo hwhi hB hξ
  choose F C hC hbound using hex
  let F₀ := Finset.univ.biUnion F
  let C₀ := ∑J : Finset α,C J
  have hCp : 0<C₀ := Finset.sum_pos (fun J _=>hC J) Finset.univ_nonempty
  refine ⟨F₀,C₀,hCp,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro J s W₁ W₂ he₁ he₂ hs₁ hs₂ hhi R seed Φ K Tsec hK hV hT hnom
  have ht := (hZ J).2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hhi R seed Φ K Tsec hK hV hT hnom
  have hCJ : C J≤C₀ := Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
  have hF : (F J).sup (schwartzSeminormFamily ℝ ℝ ℂ)≤F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.sup_mono (Finset.subset_biUnion_of_mem F (Finset.mem_univ J))
  have hFΦ := hF Φ
  have hzpos : 0<Z := zero_lt_one.trans (hZ J).1
  have hCJpos := (hC J).le
  have hfinal : C J*(plainControl s W₁ W₂)^2*(F J).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving)≤
      C₀*(plainControl s W₁ W₂)^2*F₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
    gcongr
  exact le_trans ht hfinal

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_subset_second_tail
