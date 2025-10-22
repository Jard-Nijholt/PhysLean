/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Analysis.InnerProductSpace.Trace
import PhysLean.Mathematics.Calculus.AdjFDeriv
import PhysLean.SpaceAndTime.Space.Basic
/-!

# Divergence

In this module we define and create an API around the divergence of a map `f : E → E`
where `E` is a normed space over a field `𝕜`.

-/
noncomputable section
open Module
open scoped InnerProductSpace

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- The divergence of a map `f : E → E` where `E` is a normed space over `𝕜`. -/
noncomputable def divergence (f : E → E) (x : E) : 𝕜 := (fderiv 𝕜 f x).toLinearMap.trace _ _

@[simp]
lemma divergence_zero : divergence 𝕜 (fun _ : E => 0) = fun _ => 0 := by
  unfold divergence
  simp

lemma divergence_eq_sum_fderiv {s : Finset E} (b : Basis s 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i : s, b.repr (fderiv 𝕜 f x (b i)) i := by
  funext x
  unfold divergence
  rw[LinearMap.trace_eq_matrix_trace_of_finset (s:=s) _ b]
  simp[Matrix.trace,Matrix.diag,LinearMap.toMatrix]

lemma divergence_eq_sum_fderiv' {ι} [Fintype ι] (b : Basis ι 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i, b.repr (fderiv 𝕜 f x (b i)) i := by
  let s : Finset E := Finset.univ.map ⟨b, Basis.injective b⟩
  let f' : ι → s := fun i => ⟨b i, by simp [s]⟩
  have h : Function.Injective f' := by
    intro i j h
    simp [f'] at h
    exact Basis.injective b h
  have h' : Function.Surjective f' := by
    intro ⟨x, hx⟩
    simp [s] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [f']
  let e : ι ≃ s := Equiv.ofBijective f' ⟨h, h'⟩
  let b' : Basis s 𝕜 E := b.reindex e
  rw [divergence_eq_sum_fderiv b']
  ext x
  rw [← e.symm.sum_comp]
  simp [b']

lemma divergence_eq_space_div {d} (f : Space d → Space d)
    (h : Differentiable ℝ f) : divergence ℝ f = Space.div f := by
  let b := (Space.basis (d:=d)).toBasis
  rw[divergence_eq_sum_fderiv' b]
  funext x
  simp +zetaDelta only [Space.basis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, Space.div, Space.deriv,
    Space.coord, PiLp.inner_apply, EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr
  funext i
  have h1 : (fderiv ℝ (fun x => f x i) x)
    = fderiv ℝ (Space.coordCLM i ∘ f) x := by
    congr
    ext j
    simp only [Function.comp_apply]
    rw [Space.coordCLM_apply, Space.coord_apply]
  rw [h1]
  rw [fderiv_comp]
  simp [Space.coordCLM_apply, Space.coord_apply]
  · fun_prop
  · exact h x

lemma divergence_prodMk [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {f : E×F → E} {g : E×F → F} {xy : E×F}
    (hf : DifferentiableAt 𝕜 f xy) (hg : DifferentiableAt 𝕜 g xy) :
    divergence 𝕜 (fun xy : E×F => (f xy, g xy)) xy
    =
    divergence 𝕜 (fun x' => f (x',xy.2)) xy.1
    +
    divergence 𝕜 (fun y' => g (xy.1,y')) xy.2 := by
  obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis 𝕜 E
  haveI : Fintype s := FiniteDimensional.fintypeBasisIndex bX
  obtain ⟨sY, ⟨bY⟩⟩ := Basis.exists_basis 𝕜 F
  haveI : Fintype sY := FiniteDimensional.fintypeBasisIndex bY
  let bXY := bX.prod bY
  rw[divergence_eq_sum_fderiv' bX]
  rw[divergence_eq_sum_fderiv' bY]
  rw[divergence_eq_sum_fderiv' bXY]
  simp[hf.fderiv_prodMk hg,bXY,fderiv_wrt_prod hf,fderiv_wrt_prod hg]

lemma divergence_add {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x + g x) x
    =
    divergence 𝕜 f x + divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_fun_add hf hg]

lemma divergence_neg {f : E → E} {x : E} :
    divergence 𝕜 (fun x => -f x) x = -divergence 𝕜 f x := by
  unfold divergence
  simp

lemma divergence_sub {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun x => f x - g x) x
    =
    divergence 𝕜 f x - divergence 𝕜 g x := by
  unfold divergence
  simp [fderiv_fun_sub hf hg]

lemma divergence_const_smul {f : E → E} {x : E} {c : 𝕜}
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (fun x => c • f x) x
    =
    c * divergence 𝕜 f x := by
  unfold divergence
  simp [fderiv_fun_const_smul hf]

lemma LinearMap.toMatrix_smulRight {R M M₁ m n : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid M₁] [Module R M] [Module R M₁] [Finite m] [Fintype n] [DecidableEq n]
    (f : M₁ →ₗ[R] R) (x : M) (v₁ : Module.Basis n R M₁) (v₂ : Module.Basis m R M) :
    toMatrix v₁ v₂ (f.smulRight x) = Matrix.vecMulVec (v₂.repr x) (⇑f ∘ ⇑v₁) := by
  ext i j
  simpa [toMatrix_apply, Matrix.vecMulVec_apply] using mul_comm _ _

-- from latest mathlib
@[simp]
theorem Matrix.trace_vecMulVec {R n : Type*} [Fintype n] [NonUnitalNonAssocSemiring R]
    (a b : n → R) : trace (vecMulVec a b) = a ⬝ᵥ b := by
  rw [vecMulVec_eq Unit, trace_replicateCol_mul_replicateRow]

@[simp]
lemma LinearMap.trace_smulRight {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] R) (x : M) :
    trace R M (f.smulRight x) = f x := by
  classical
  rw [trace_eq_matrix_trace _ (Module.Free.chooseBasis R M)]
  simp only [toMatrix_smulRight, Matrix.trace_vecMulVec, dotProduct, Function.comp_apply]
  simp_rw +singlePass [← smul_eq_mul, ← map_smul, ← map_sum, Module.Basis.sum_repr]

@[simp]
lemma ContinuousLinearMap.smulRight_toLinearMap {M₁ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {R : Type*} {S : Type*}
    [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S] [Module S M₂]
    [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂] (c : M₁ →L[R] S) (f : M₂) :
    (↑(ContinuousLinearMap.smulRight c f) : M₁ →ₗ[R] M₂) =
      LinearMap.smulRight (↑c : M₁ →ₗ[R] S) f :=
  rfl

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

lemma divergence_smul [InnerProductSpace' 𝕜 E] {f : E → 𝕜} {g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    [FiniteDimensional 𝕜 E] :
    divergence 𝕜 (fun x => f x • g x) x
    = f x * divergence 𝕜 g x + ⟪adjFDeriv 𝕜 f x 1, g x⟫ := by
  unfold divergence
  simp [fderiv_fun_smul hf hg]
  obtain ⟨s, b⟩ := Basis.exists_basis 𝕜 E
  let basis := Classical.choice b
  have s_fin : Fintype s := FiniteDimensional.fintypeBasisIndex basis
  have h_basis : Basis (↑s) 𝕜 E = Basis s.toFinset 𝕜 E := by
    simp only [Set.mem_toFinset]
  rw [h_basis] at basis
  rw [LinearMap.trace_eq_matrix_trace_of_finset (s := s.toFinset) _ basis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix]
  simp_all only [Set.mem_toFinset, Finset.univ_eq_attach, LinearEquiv.trans_apply, LinearMap.toMatrix'_apply,
    LinearEquiv.arrowCongr_apply, Basis.equivFun_symm_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    ↓reduceIte, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply, map_smul, Basis.equivFun_apply,
    Pi.smul_apply, smul_eq_mul]
  -- comes from aesop, clean up
  rw [adjFDeriv]
  have h₁ : ⟪adjoint 𝕜 (⇑(fderiv 𝕜 f x)) 1, g x⟫ = (fderiv 𝕜 f x)  (g x):= by
    rw [HasAdjoint.adjoint_inner_left]
    · simp_all only [RCLike.inner_apply, map_one, mul_one]
      rfl
    · haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
      apply hf.hasAdjFDerivAt.hasAdjoint_fderiv
  rw [h₁]
  have hg_sum : g x = ∑ x_1 ∈ s.toFinset.attach, (basis.repr (g x) x_1) • basis x_1 := by
    exact Eq.symm (basis.sum_repr (g x))
  calc
    ∑ x_1 ∈ s.toFinset.attach, (fderiv 𝕜 f x) (basis x_1) * (basis.repr (g x)) x_1
      = ∑ x_1 ∈  s.toFinset.attach, (fderiv 𝕜 f x) ((basis.repr (g x) x_1) • basis x_1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        calc
          (fderiv 𝕜 f x) (basis i) * (basis.repr (g x) i) =
            (basis.repr (g x) i) * (fderiv 𝕜 f x) (basis i) := by
            exact mul_comm _ _
          _ = (fderiv 𝕜 f x) ((basis.repr (g x) i) • basis i) := by
            rw [map_smul]
            rfl
    _ = (fderiv 𝕜 f x) (∑ x_1 ∈ s.toFinset.attach, (basis.repr (g x) x_1) • basis x_1) := by
      rw [map_sum]
    _ = (fderiv 𝕜 f x) (g x) := by
      rw [hg_sum]
      apply congrArg (fderiv 𝕜 f x)
      simp only [← hg_sum]

lemma divergence_smul_2 [InnerProductSpace' 𝕜 E] {f : E → 𝕜} {g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
    [FiniteDimensional 𝕜 E] :
    divergence 𝕜 (fun x => f x • g x) x
    = f x * divergence 𝕜 g x + ⟪adjFDeriv 𝕜 f x 1, g x⟫ := by
  unfold divergence
  simp [fderiv_fun_smul hf hg]
  rw [adjFDeriv]
  have h₁ : ⟪adjoint 𝕜 (⇑(fderiv 𝕜 f x)) 1, g x⟫ = (fderiv 𝕜 f x)  (g x):= by
    rw [HasAdjoint.adjoint_inner_left]
    · simp_all only [RCLike.inner_apply, map_one, mul_one]
      rfl
    · haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
      apply hf.hasAdjFDerivAt.hasAdjoint_fderiv
  rw [h₁]
