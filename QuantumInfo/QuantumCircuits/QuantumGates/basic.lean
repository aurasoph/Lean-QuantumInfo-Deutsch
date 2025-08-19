import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap

abbrev Bit := Qubit

open Finite Qubit Real Complex

namespace Qubit

-- Here are some definitions of basic gates copied from QuantumInfo:

-- Pauli Z gate on a qubit
--def Z : 𝐔[Qubit] :=
--  ⟨!![1, 0; 0, -1], by constructor <;> matrix_expand⟩


-- Pauli X gate on a qubit
--def X : 𝐔[Qubit] :=
--  ⟨!![0, 1; 1, 0], by constructor <;> matrix_expand⟩


-- Pauli Y gate on a qubit
--def Y : 𝐔[Qubit] :=
--  ⟨!![0, -I; I, 0], by constructor <;> matrix_expand⟩


-- The H gate (Hadamard gate) on a qubit
--def Y : 𝐔[Qubit] :=
--  ⟨!![0, -I; I, 0], by constructor <;> matrix_expand⟩


-- The S gate, or Rz(π/2) rotation on a qubit
--def S : 𝐔[Qubit] :=
--  ⟨!![1, 0; 0, I], by constructor <;> matrix_expand⟩


-- The T gate, or Rz(π/4) rotation on a qubit
--noncomputable def T : 𝐔[Qubit] :=
--  ⟨!![1, 0; 0, (1 + I)/√2], by constructor <;> matrix_expand⟩


-- Controllize: Given a unitary `U` on some Hilbert space `k`, we have the controllized version that acts on `Fin 2 ⊗ k`
--where `U` is conditionally applied if the first qubit is `1`.
--def controllize (g : 𝐔[k]) : 𝐔[Qubit × k] :=
--  ⟨Matrix.of fun (q₁,t₁) (q₂,t₂) ↦
--    if (q₁,q₂) = (0,0) then
--      (if t₁ = t₂ then 1 else 0)
--    else if (q₁,q₂) = (1,1) then
--      g t₁ t₂
--    else 0
--    , by
--      rw [Matrix.mem_unitaryGroup_iff]
--      matrix_expand [-Complex.ext_iff] with ti tj;
--      · congr 1
--        exact propext eq_comm
--      · exact congrFun₂ g.2.2 ti tj
--    ⟩


open Real
open Complex

variable {k : Type*} [Fintype k] [DecidableEq k]

-- S^-1 gate, the Rz(-π/2) (inverse of S gate)
def Sin : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -I], by constructor <;> matrix_expand⟩


-- T^-1 gate, or Rz(-π/4) rotation on a qubit
noncomputable def Tin : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, (1 - I)/√2], by constructor <;> matrix_expand⟩


-- CNOT Gate A to B
noncomputable def CNOT : 𝐔[Qubit × Qubit] :=
  controllize X


-- CCNOT Gate
noncomputable def CCNOT : 𝐔[Qubit × Qubit × Qubit] :=
  controllize CNOT


-- CNOT reverse direction (B to A)
noncomputable def CNOTR : 𝐔[Qubit × Qubit] :=
  (Matrix.unitary_kron H H) * CNOT * (Matrix.unitary_kron H H)


-- SWAP gate
noncomputable def SWAP : 𝐔[Qubit × Qubit] :=
  CNOT * CNOTR * CNOT

end Qubit
