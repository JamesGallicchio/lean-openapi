import Std

structure Int32 where
  unsigned : UInt32

namespace Int32

@[inline] def offset : Nat := 2^31

def toInt (i : Int32) : Int := Int.subNatNat i.unsigned.toNat offset
def ofInt (i : Int) : Option Int32 :=
  let i' := i + offset
  if h : 0 ≤ i' then
    let i'' := i'.toNat
    if h : i'' < UInt32.size then
      some ⟨i'', h⟩
    else none
  else none

theorem lowerBound (i : Int32) : -(2^31 : Nat) ≤ i.toInt := by
  simp [toInt, offset, Int.subNatNat_eq_coe]
  apply Int.le_sub_left_of_add_le
  simp [Int.add_right_neg, Int.ofNat_nonneg]

def upperExcl (i : Int32) : i.toInt < (2^31 : Nat) := by
  simp [toInt, offset, Int.subNatNat_eq_coe]
  apply Int.sub_left_lt_of_lt_add
  rw [Int.ofNat_add_ofNat, Int.ofNat_lt, ←Nat.mul_two, ←Nat.pow_succ]
  apply Fin.isLt (UInt32.val _)

@[simp] theorem ofInt_toInt : ofInt (toInt i) = some i := by
  simp [toInt, Int.subNatNat_eq_coe]
  simp [ofInt, Int.ofNat_nonneg, UInt32.toNat]

@[simp] theorem toInt_ofInt : ofInt i = some i' → toInt i' = i := by
  intro h
  simp [ofInt] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp at h
  cases h
  simp [toInt, Int.subNatNat_eq_coe, UInt32.toNat]
  rw [Int.toNat_eq_max, Int.max_eq_left ‹_›]
  simp

end Int32

structure Int64 where
  unsigned : UInt64

namespace Int64

@[inline] def offset : Nat := 2^63

def toInt (i : Int64) : Int := Int.subNatNat i.unsigned.toNat offset
def ofInt (i : Int) : Option Int64 :=
  let i' := i + offset
  if h : 0 ≤ i' then
    let i'' := i'.toNat
    if h : i'' < UInt64.size then
      some ⟨i'', h⟩
    else none
  else none

theorem lowerBound (i : Int64) : -(2^63 : Nat) ≤ i.toInt := by
  simp [toInt, offset, Int.subNatNat_eq_coe]
  apply Int.le_sub_left_of_add_le
  simp [Int.add_right_neg, Int.ofNat_nonneg]

def upperExcl (i : Int64) : i.toInt < (2^63 : Nat) := by
  simp [toInt, offset, Int.subNatNat_eq_coe]
  apply Int.sub_left_lt_of_lt_add
  rw [Int.ofNat_add_ofNat, Int.ofNat_lt, ←Nat.mul_two, ←Nat.pow_succ]
  apply Fin.isLt (UInt64.val _)

@[simp] theorem ofInt_toInt : ofInt (toInt i) = some i := by
  simp [toInt, Int.subNatNat_eq_coe]
  simp [ofInt, Int.ofNat_nonneg, UInt64.toNat]

@[simp] theorem toInt_ofInt : ofInt i = some i' → toInt i' = i := by
  intro h
  simp [ofInt] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp at h
  cases h
  simp [toInt, Int.subNatNat_eq_coe, UInt64.toNat]
  rw [Int.toNat_eq_max, Int.max_eq_left ‹_›]
  simp

end Int64
