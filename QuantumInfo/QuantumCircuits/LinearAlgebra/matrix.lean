import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic

open Complex Matrix

variable {m n : Type} [Fintype m] [Fintype n]

-- Notation for absolute value of a complex number
notation "|" x "|" => Complex.abs x

-- Notation for a complex Conjugate
notation x "†" => Complex.conj x

-- Adjoint: conjugate transpose for Complex-valued matrices
noncomputable
def adjoint (M: Matrix m n ℂ) : Matrix n m ℂ :=
  M.conjTranspose

-- Trace sum of diagonal entries
noncomputable
def trace (M: Matrix n n ℂ) : ℂ :=
  Matrix.trace M

-- Partial trace over the first substem (n) of a bipartie system n x m
noncomputable
def partialTraceFirst (M : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  λ i j => ∑ k : n, M (k, i) (k, j)

-- Partial trace over the second subsystem
noncomputable
def partialTraceSecond (M : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  λ a b => ∑ c : m, M (a, c) (b, c)
