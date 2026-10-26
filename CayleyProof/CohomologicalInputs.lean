module

public import CayleyProof.SheafMonodromyBridge
public import CayleyProof.Theorem22

/-! Explicit interface for the permitted external cohomological results.

The categories below are the constructible l-adic coefficient categories,
represented abstractly because mathlib does not yet provide the required
Rf_! package.  Existing mathlib categories, functors, monoidal categories,
groups, topologies, characters, matrices and measures are reused.

No field asserts the constant-coordinate factorization, zero-family SL
containment, a determinant-one Frobenius, arithmetic containment, or a limit
for the scalar laws.  Those are proved by the consuming theorems.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MeasureTheory Filter Matrix
open scoped BigOperators Topology Classical

namespace CayleyProof

structure FullFamilySheafData
    (G Γ Δ : Type) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (det : G →* ℂˣ) (ρ₀ : Δ → G) (rπ : Γ → Δ) (α : Γ → G) where
  CX : Type
  CD : Type
  CXT : Type
  CDT : Type
  [catX : Category CX]
  [catD : Category CD]
  [catXT : Category CXT]
  [catDT : Category CDT]
  [monD : MonoidalCategory CD]
  [monDT : MonoidalCategory CDT]
  R : Type
  [addR : Add R]
  AS : R → CDT
  additivity : ∀ f g, AS (f + g) ≅ AS f ⊗ AS g
  r : CX ⥤ CD
  rT : CXT ⥤ CDT
  pushX : CXT ⥤ CX
  pushD : CDT ⥤ CD
  πpull : CD ⥤ CDT
  baseChange : ∀ L, pushD.obj (rT.obj L) ≅ r.obj (pushX.obj L)
  projection : ∀ L T, pushD.obj (L ⊗ πpull.obj T) ≅ pushD.obj L ⊗ T
  f : R
  c : R
  L : CXT
  T : CD
  hf : AS f ≅ rT.obj L
  hc : AS c ≅ πpull.obj T
  rep : CD → Γ → G
  isoConjugacy : ∀ U V, (U ≅ V) → ∃ C : G, ∀ γ, rep U γ = C * rep V γ * C⁻¹
  tensorPullback : ∀ γ, rep (r.obj (pushX.obj L) ⊗ T) γ = α γ * ρ₀ (rπ γ)
  katzFullFamily : (det.ker : Set G) ⊆ closure (Set.range (rep (pushD.obj (AS (f + c)))))

attribute [instance] FullFamilySheafData.catX FullFamilySheafData.catD
  FullFamilySheafData.catXT FullFamilySheafData.catDT FullFamilySheafData.monD
  FullFamilySheafData.monDT FullFamilySheafData.addR

theorem FullFamilySheafData.factorization
    {G Γ Δ : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {det : G →* ℂˣ} {ρ₀ : Δ → G} {rπ : Γ → Δ} {α : Γ → G}
    (S : FullFamilySheafData G Γ Δ det ρ₀ rπ α) :
    ∃ ρfull : Γ → G, (∀ γ, ρfull γ = α γ * ρ₀ (rπ γ)) ∧
      (det.ker : Set G) ⊆ closure (Set.range ρfull) :=
  sheaf_factorization_supplies_monodromy_input S.AS S.additivity
    S.r S.rT S.pushX S.pushD S.πpull S.baseChange S.projection
    S.f S.c S.L S.T S.hf S.hc det S.rep S.isoConjugacy
    ρ₀ rπ α S.tensorPullback S.katzFullFamily

/-- A concrete list of standard geometric data for the exact-degree m+3
zero-constant coefficient scheme and its full-family extension.  See
EXTERNAL_INPUTS.md for the source of EVERY non-definitional field. -/
structure CoefficientCohomologyData
    (m : ℕ) (F : Type) [Field F] [Fintype F]
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (ψ : AddChar F ℂ) (c : ℂ) where
  P : Type
  Q : Type
  G : Type
  Γ : Type
  [groupP : Group P]
  [topP : TopologicalSpace P]
  [compactP : CompactSpace P]
  [groupQ : Group Q]
  [topQ : TopologicalSpace Q]
  [hausdorffQ : T2Space Q]
  [groupG : Group G]
  [ellTopology : TopologicalSpace G]
  [ellGroup : IsTopologicalGroup G]
  π : P →* Q
  continuousπ : Continuous π
  surjectiveπ : Function.Surjective π
  ρ : P →* G
  continuousρ : Continuous ρ
  det : G →* ℂˣ
  zariski : TopologicalSpace G
  zariskiMul : @SeparatelyContinuousMul G zariski _
  H₀ : Subgroup G
  ellClosed : @IsClosed G ellTopology (H₀ : Set G)
  zariskiClosed : @IsClosed G zariski (H₀ : Set G)
  closure_eq : (H₀ : Set G) = @closure G zariski (Set.range (fun x : π.ker => ρ x.val))
  connectedSL : @IsPreconnected G zariski (det.ker : Set G)
  rπ : Γ → π.ker
  α : Γ → G
  scalarSet : Set G
  finiteScalars : scalarSet.Finite
  scalar_mem : ∀ γ, α γ ∈ scalarSet
  fullSheaves : @FullFamilySheafData G Γ π.ker groupG zariski zariskiMul
    det (fun x => ρ x.val) rπ α
  frob : Fˣ → P
  frob_generator : ∀ u, DenseRange (fun n : ℤ => π (frob u) ^ n)
  eigenvalues : Fˣ → Fin (m + 2) → ℂ
  determinant : ∀ u, (det (ρ (frob u))).val = ∏ i, eigenvalues u i
  powerTrace : ∀ (u : Fˣ) (n : ℕ), (∑ i, eigenvalues u i ^ (n + 1)) =
    -(c ^ (n + 1)) * ∑ t : E n,
      traceLift (E := E n) ψ (algebraMap F (E n) (u : F) * t ^ (m + 3))
  K : Type
  [groupK : Group K]
  [topK : TopologicalSpace K]
  [measurableK : MeasurableSpace K]
  [borelK : BorelSpace K]
  [compactK : CompactSpace K]
  M : K →* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ
  continuousM : Continuous (fun x => (M x).val)
  unitary : ∀ x, (M x).val ∈ Matrix.unitaryGroup (Fin (m + 2)) ℂ
  complexComparison : G ≃* (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ
  complexDet : ∀ g, (complexComparison g).val.det = (det g).val
  compactIntersection : ∀ A : (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ,
    A.val ∈ Matrix.unitaryGroup (Fin (m + 2)) ℂ →
    complexComparison.symm A ∈ H₀ → ∃ x, M x = A
  haar : ProbabilityMeasure K
  [haarOpenPositive : (haar : Measure K).IsOpenPosMeasure]
  θ : ∀ n, {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} → K
  trace : ∀ n b, representedNegativeTrace M continuousM (θ n b) =
    normalizedCharacterSum (traceLift (E := E n) ψ) b.val
  deligne : ρ.range ≤ H₀ → ∀ f : C(K, ℝ),
    (∀ x y, f (y * x * y⁻¹) = f x) →
    Tendsto (fun n =>
      (Fintype.card {b : Fin (m + 3) → E n // b (Fin.last (m + 2)) ≠ 0} : ℝ)⁻¹ *
        ∑ b, f (θ n b)) atTop (𝓝 (∫ x, f x ∂(haar : Measure K)))

attribute [instance] CoefficientCohomologyData.groupP CoefficientCohomologyData.topP
  CoefficientCohomologyData.compactP CoefficientCohomologyData.groupQ
  CoefficientCohomologyData.topQ CoefficientCohomologyData.hausdorffQ
  CoefficientCohomologyData.groupG CoefficientCohomologyData.ellTopology
  CoefficientCohomologyData.ellGroup CoefficientCohomologyData.groupK
  CoefficientCohomologyData.topK CoefficientCohomologyData.measurableK
  CoefficientCohomologyData.borelK CoefficientCohomologyData.compactK
  CoefficientCohomologyData.haarOpenPositive

/-- After unitarizing a maximal compact subgroup, it is the intersection
of the complex monodromy group with U.  SU containment is a deduction from
this standard realization and the proved SL containment, not an external
monodromy assumption. -/
theorem CoefficientCohomologyData.compactSL
    {m : ℕ} {F : Type} [Field F] [Fintype F]
    {E : ℕ → Type} [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    {ψ : AddChar F ℂ} {c : ℂ}
    (D : CoefficientCohomologyData m F E ψ c) (hSL : D.det.ker ≤ D.H₀) :
    ∀ A ∈ Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ, ∃ x, (D.M x).val = A := by
  intro A hA
  obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  let B : (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)ˣ :=
    Unitary.toUnits ⟨A, hU⟩
  have hker : D.complexComparison.symm B ∈ D.det.ker := by
    change D.det (D.complexComparison.symm B) = 1
    apply Units.ext
    rw [← D.complexDet, D.complexComparison.apply_symm_apply]
    exact hdet
  obtain ⟨x, hx⟩ := D.compactIntersection B hU (hSL hker)
  exact ⟨x, congrArg Units.val hx⟩

theorem theorem22_from_standard_data
    (m : ℕ) {F : Type} [Field F] [Fintype F]
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    {v : ℕ} (hdiv : m + 3 ∣ Fintype.card F - 1) (hcard : Fintype.card F = v ^ 2)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : ∀ n, AddChar (E n) ℂ) (hχ : ∀ n, χ n ≠ 1)
    (hHD : ∀ n, HasseDavenportIdentity (E := E n) ψ)
    (c : ℂ) (hc : c ^ 2 * Fintype.card F = 1)
    (D : CoefficientCohomologyData m F E ψ c) :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n => katzSampleLaw (χ n) (m + 2)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ).support ⊆ Set.Icc (-(m + 2 : ℝ)) (m + 2 : ℝ) ∧
      (μ : Measure ℝ).support.Infinite := by
  have hh : ∃ ρfull : D.Γ → D.G,
      (∀ γ, ρfull γ = D.α γ * D.ρ (D.rπ γ).val) ∧
      (D.det.ker : Set D.G) ⊆ @closure D.G D.zariski (Set.range ρfull) := by
    let : TopologicalSpace D.G := D.zariski
    let : SeparatelyContinuousMul D.G := D.zariskiMul
    exact D.fullSheaves.factorization
  obtain ⟨ρfull, hfactor, hKatz⟩ := hh
  exact theorem22_from_cohomological_data m E hrank hdiv hcard ψ hψ χ hχ hHD c hc
    D.π D.continuousπ D.surjectiveπ D.ρ D.continuousρ D.det D.zariski D.zariskiMul
    D.H₀ D.ellClosed D.zariskiClosed D.closure_eq D.connectedSL
    ρfull D.rπ D.α hfactor D.scalarSet D.finiteScalars D.scalar_mem hKatz
    D.frob D.frob_generator D.eigenvalues D.determinant D.powerTrace
    D.M D.continuousM D.unitary D.compactSL D.haar D.θ D.trace D.deligne

end CayleyProof
