structure {u} signature_data (S : Type (u+1)) (D : S → Type (u+1)) :=
(g : Type u)
(σ : S)
(s t : g → D σ)

structure unchecked_diagram_data (n : ℕ) (S D) (σ : signature_data S D) :=
(s : D σ.σ)
(δ : list (σ.g × vector nat n))

definition {u} unchecked_signature_diagram_pair : ℕ → Σ T : Type (u+1), T → Type (u+1)
| 0     := ⟨ulift unit, λ _, ulift unit⟩
| (n+1) := let ⟨S, D⟩ := unchecked_signature_diagram_pair n in 
             ⟨signature_data S D, unchecked_diagram_data n S D⟩

definition {u} unchecked_signature (n : ℕ) : Type (u+1)                          := (unchecked_signature_diagram_pair n).1
definition {u} unchecked_diagram   (n : ℕ) : unchecked_signature n → Type (u+1) := (unchecked_signature_diagram_pair n).2

