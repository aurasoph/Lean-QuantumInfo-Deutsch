import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.QuantumCircuits.QuantumGates.basic


namespace Qubit

@[simp] def xor : Bit → Bit → Bit
  | 0,0 => 0 | 0,1 => 1 | 1,0 => 1 | 1,1 => 0
@[simp] lemma xor_0_0 : xor (0:Bit) (0:Bit) = 0 := rfl
@[simp] lemma xor_0_1 : xor (0:Bit) (1:Bit) = 1 := rfl
@[simp] lemma xor_1_0 : xor (1:Bit) (0:Bit) = 1 := rfl
@[simp] lemma xor_1_1 : xor (1:Bit) (1:Bit) = 0 := rfl
end Qubit


-- Increment gate
@[simp] def inc : Bit → Bit
  | 0 => 1
  | 1 => 0
@[simp] lemma inc_0 : inc (0:Bit) = 1:= rfl
@[simp] lemma inc_1 : inc (1:Bit) = 0 := rfl


-- Deincrement gate one bit (the same action as inc gate)


-- Two qubit Decrementer
@[simp] def dec2 : Bit × Bit → Bit × Bit
  | (0,0) => (1,1)
  | (0,1) => (0,0)
  | (1,0) => (0,1)
  | (1,1) => (1,0)

@[simp] lemma dec2_00 : dec2 (0,0) = (1,1) := rfl
@[simp] lemma dec2_01 : dec2 (0,1) = (0,0) := rfl
@[simp] lemma dec2_10 : dec2 (1,0) = (0,1) := rfl
@[simp] lemma dec2_11 : dec2 (1,1) = (1,0) := rfl
