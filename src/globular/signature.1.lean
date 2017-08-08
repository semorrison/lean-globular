inductive {u} dependent_list (A : Type u) (f : A → Type u) (g : Π a : A, f a → A) : A → A → Type (u+1)
| nil  : Π a: A, (dependent_list a a)
| cons : Π { a b : A }, Π x : f b, (dependent_list a b) → dependent_list a (g b x)

open nat

definition divisor_chain : ℕ → ℕ → Type 1 := dependent_list ℕ (λ m: ℕ, { k : ℕ // k ∣ m }) (λ _ n, n)
definition divisor_chain.nil : Π n : ℕ, divisor_chain n n := @dependent_list.nil ℕ (λ m: ℕ, { k : ℕ // k ∣ m }) (λ _ n, n)
definition divisor_chain.cons : Π {m n : ℕ}, Π k : { k // k ∣ n }, divisor_chain m n → divisor_chain m k := λ m n k c, @dependent_list.cons _ (λ m: ℕ, { k : ℕ // k ∣ m }) _ m n k c

open divisor_chain

definition example_1 : divisor_chain 10 10 := nil 10
definition example_2 : divisor_chain 10 5 := cons ⟨ 5, begin exact dec_trivial end ⟩ (nil 10)

notation a ## b := divisor_chain.cons ⟨ a, by exact dec_trivial ⟩ b
definition example_3 := (20 ## (nil 40))
definition example_4 := 5 ## example_3
-- definition example_5 := 5 ## (20 ## (nil 40))

-- In this first section, we define
-- * signature_data
-- * diagram_data
-- * embedding_data
-- all parametrised by dummy types, which we'll later specialise recursively into the appropriate types one level down.

structure {u} signature_data (Signature : Type (u+1)) (Diagram : Signature → Type (u+1)) :=
(g : Type u)
(σ : Signature)
(s t : g → Diagram σ)

definition {u} embedding_chain_data (Diagram : Type u) (Rewrite : Diagram → Type u) (result : Π d : Diagram, Rewrite d → Diagram) : Diagram → Diagram → Type (u+1) :=
dependent_list Diagram (λ d, Rewrite d) result

structure {u} diagram_data
  (Signature : Type (u+1))
  (Diagram : Signature → Type (u+1)) 
  (Rewrite : Π σ : Signature, Diagram σ → Type (u+1)) 
  (result : Π σ : Signature, Π d : Diagram σ, Rewrite σ d → Diagram σ) 
  (σ : signature_data Signature Diagram) :=
(s t : Diagram σ.σ)
(δ : embedding_chain_data (Diagram σ.σ) (Rewrite σ.σ) (result σ.σ) s t)

structure embedding_data (Diagram Diagram' : Type) (s : Diagram → Diagram') (Embedding: Diagram' → Diagram' → Type) (S T : Diagram) :=
(h : ℕ)
(e : Embedding (s S) (s T))



definition {u} signature_diagram_pair : ℕ → (Σ T : Type (u+1), T → Type (u+1))
| 0     := ⟨ulift unit, λ _, ulift unit⟩
| (n+1) := let ⟨S, D⟩ := signature_diagram_pair n in 
             ⟨signature_data S D, diagram_data n S D⟩

definition {u} signature (n : ℕ) : Type (u+1)                := (signature_diagram_pair n).1
definition {u} diagram   (n : ℕ) : signature n → Type (u+1) := (signature_diagram_pair n).2

