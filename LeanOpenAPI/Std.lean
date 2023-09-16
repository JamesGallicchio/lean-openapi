import Std

instance [Inhabited ε] : Alternative (Except ε) where
  failure := Except.error default
  orElse f g := f.orElseLazy g

def Array.pmap (A : Array α) (f : (a : α) → (∃ i : Fin A.size, A[i] = a) → β) : Array β :=
  Array.ofFn (fun i => f (A[i]) ⟨i, rfl⟩)

def Array.forall_of_all {A : Array α} (f : α → Bool) :
    A.all f → ∀ i : Fin A.size, f A[i] := by
  rintro h ⟨i,hi⟩
  have : A.all f i := by
    induction i with
    | zero => exact h
    | succ i ih =>
      have := ih (Nat.lt_of_succ_lt hi)
      simp [all, allM, Id.run, anyM] at this ⊢
      unfold anyM.loop at this
      simp [Nat.lt_of_succ_lt hi] at this
      split at this
      · contradiction
      · assumption
  simp [all, Id.run, allM, anyM] at this
  unfold anyM.loop at this
  simp [hi] at this
  split at this
  · contradiction
  · simp [*]

