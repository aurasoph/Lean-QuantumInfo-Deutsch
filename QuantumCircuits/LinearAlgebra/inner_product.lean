import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import QuantumInfo.QuantumCircuits.LinearAlgebra.matrix
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Defs

open Matrix Complex

variable {n : Type} [Fintype n] [DecidableEq n]

-- Inner product on ℂ^n as column vectors
noncomputable def innerProduct (v w : Matrix n (Fin 1) ℂ) : ℂ :=
  dotProduct (fun i => v i 0) (fun i => star (w i 0))

notation "⟪" v ", " w "⟫" => innerProduct v w


-- Inner product with itself: sum of squared norms
lemma inner_product_self_eq_sum_norm_sq (v : Matrix n (Fin 1) ℂ) :
    ⟪v, v⟫ = ∑ i, (v i 0 * star (v i 0)) := by
  unfold innerProduct dotProduct
  rfl


-- Inner product with itself: imaginary part is zero
--theorem inner_self_im{𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
--RCLike.im (inner 𝕜 x x) = 0


-- Positive semidefinite ⟪v, v⟫ ≥ 0
--theorem Matrix.PosSemidef.re_dotProduct_nonneg{n : Type u_2} {𝕜 : Type u_4} [Fintype n] [RCLike 𝕜] {M : Matrix n n 𝕜} (hM : M.PosSemidef) (x : n → 𝕜) :
--0 ≤ RCLike.re (star x ⬝ᵥ M.mulVec x)


-- <v,v>=0 iff v = 0
--theorem dotProduct_self_star_eq_zero{n : Type u_2} {R : Type u_4} [Fintype n] [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R] [NoZeroDivisors R] {v : n → R} :
--v ⬝ᵥ star v = 0 ↔ v = 0


--  ⟪v + w, v + w⟫ expansion
--theorem InnerProductSpace.Core.inner_add_add_self{𝕜 : Type u_1} {F : Type u_3} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F] (x y : F) :
--inner 𝕜 (x + y) (x + y) = inner 𝕜 x x + inner 𝕜 x y + inner 𝕜 y x + inner 𝕜 y y


-- ⟪-v, -v⟫ = ⟪v, v⟫
--theorem inner_neg_neg{𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
--inner 𝕜 (-x) (-y) = inner 𝕜 x y


-- Scalar multiplication on the left side of inner prod
--theorem InnerProductSpace.Core.inner_smul_left{𝕜 : Type u_1} {F : Type u_3} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F] (x y : F) {r : 𝕜} :
--inner 𝕜 (r • x) y = (starRingEnd 𝕜) r * inner 𝕜 x y

-- Scalar multiplication on the right side of inner prod
--theorem InnerProductSpace.Core.inner_smul_right{𝕜 : Type u_1} {F : Type u_3} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F] (x y : F) {r : 𝕜} :
--inner 𝕜 x (r • y) = r * inner 𝕜 x y


-- Zero on the right side ⟪v, 0⟫=0
--theorem inner_zero_right{𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
--inner 𝕜 x 0 = 0

-- Zero on the left side ⟪0, v⟫=0
--theorem inner_zero_left{𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
--inner 𝕜 0 x = 0


-- Conjugate innerproduct symmetry ⟪v, w⟫ = ⟪w, v⟫
--theorem InnerProductSpace.Core.inner_conj_symm{𝕜 : Type u_1} {F : Type u_3} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F] (x y : F) :
--(starRingEnd 𝕜) (inner 𝕜 y x) = inner 𝕜 x y


-- |⟪v, w⟫| = |⟪w, v⟫|
--theorem norm_inner_symm{𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
--‖inner 𝕜 x y‖ = ‖inner 𝕜 y x‖
