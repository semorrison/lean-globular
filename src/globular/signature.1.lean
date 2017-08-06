inductive dependent_list (A : Type) (f : A → Type) (g : Π a : A, f a → A) : A → Type
| nil  : Π a: A, (dependent_list a)
| cons : Π { a : A }, Π x : f a, (dependent_list a) → dependent_list (g a x)

open nat

definition divisor_chain : ℕ → Type := dependent_list ℕ (λ n: ℕ, { m : ℕ // m ∣ n }) (λ _ m, m)
definition divisor_chain.nil : Π n : ℕ, divisor_chain n := @dependent_list.nil ℕ (λ n: ℕ, { m : ℕ // m ∣ n }) (λ _ m, m)
definition divisor_chain.cons : Π {n : ℕ}, Π m : { m // m ∣ n }, divisor_chain n → divisor_chain m := λ n m c, @dependent_list.cons ℕ (λ n: ℕ, { m : ℕ // m ∣ n }) (λ _ m, m) n m c

open divisor_chain

definition example_1 : divisor_chain 10 := nil 10
definition example_2 : divisor_chain 5 := cons ⟨ 5, begin exact dec_trivial end ⟩ (nil 10)

notation a ## b := divisor_chain.cons ⟨ a, by exact dec_trivial ⟩ b
definition example_3 := (20 ## (nil 40))
definition example_4 := 5 ## example_3
-- definition example_5 := 5 ## (20 ## (nil 40))

-- In this first section, we define
-- * signature data
-- * diagram_data
-- * embedding_data
-- all parametrised by dummy types, which we'll later specialise recursively into the appropriate types one level down.

structure {u} signature_data (Signature : Type (u+1)) (Diagram : Signature → Type (u+1)) :=
(g : Type u)
(σ : Signature)
(s t : g → Diagram σ)

structure diagram_data (n : ℕ) (Signature Diagram) (EmbeddingInto : Type) (σ : signature_data Signature Diagram) :=
(s : Diagram σ.σ)
(δ : list (σ.g × vector nat n))

structure embedding_data (Diagram Diagram' : Type) (s : Diagram → Diagram') (Embedding: Diagram' → Diagram' → Type) (S T : Diagram) :=
(h : ℕ)
(e : Embedding (s S) (s T))



definition {u} signature_diagram_pair : ℕ → (Σ T : Type (u+1), T → Type (u+1))
| 0     := ⟨ulift unit, λ _, ulift unit⟩
| (n+1) := let ⟨S, D⟩ := signature_diagram_pair n in 
             ⟨signature_data S D, diagram_data n S D⟩

definition {u} signature (n : ℕ) : Type (u+1)                := (signature_diagram_pair n).1
definition {u} diagram   (n : ℕ) : signature n → Type (u+1) := (signature_diagram_pair n).2

