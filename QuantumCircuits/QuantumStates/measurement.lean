import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.QuantumCircuits.QuantumGates.basic

namespace Qubit

@[simp] noncomputable def ket0_vec : Bit → ℂ := fun i => if i = 0 then 1 else 0
@[simp] noncomputable def ket1_vec : Bit → ℂ := fun i => if i = 1 then 1 else 0

@[simp] noncomputable def ketMinus_vec : Bit → ℂ :=
  ((Qubit.H : 𝐔[Bit]).val).mulVec ket1_vec


@[simp] lemma ketMinus_eval (y : Bit) :
  ketMinus_vec y = (Qubit.H : 𝐔[Bit]).val y 1 := by
  classical
  simp [ketMinus_vec, Matrix.mulVec, ket1_vec]

end Qubit
