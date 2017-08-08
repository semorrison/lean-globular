inductive {u} nonempty_list (A : Type u) : Type u
| start : A → nonempty_list
| cons  : A → nonempty_list → nonempty_list

open nonempty_list

definition nonempty_list.head {A} : nonempty_list A → A
| (start a)  := a
| (cons a l) := a

inductive {u} dependent_list (A : Type u) (f : A → Type u) (g : Π a : A, f a → A) : (nonempty_list A) → Type u
| nil  : Π a: A, (dependent_list (start a))
| cons : Π { l : nonempty_list A }, Π x : f (l.head), (dependent_list l) → dependent_list (cons (g (l.head) x) l)

structure {u} signature_data (Signature' : Type (u+1)) (Diagram' : Signature' → Type (u+1)) : Type (u+1) :=
(g : Type u)
(σ : Signature')
(s t : g → Diagram' σ)

definition {u} embedding_chain_data (Diagram : Type u) (Rewrite : Diagram → Type (u)) (result : Π d : Diagram, Rewrite d → Diagram) : nonempty_list Diagram → Type u :=
dependent_list Diagram (λ d, Rewrite d) result

structure {u} diagram_data
  (Signature' : Type (u+1))
  (Diagram' : Signature' → Type (u+1)) 
  (σ : signature_data Signature' Diagram')
  (rewrite : Diagram' σ.σ → Type (u+1)) 
  (result : Π d : Diagram' σ.σ, rewrite d → Diagram' σ.σ) 
  :=
(d : nonempty_list (Diagram' σ.σ))
(δ : embedding_chain_data (Diagram' σ.σ) rewrite result d)

structure embedding_data (Diagram' Diagram : Type) (s : Diagram → Diagram') (Embedding: Diagram' → Diagram' → Type) (S T : Diagram) :=
(h : ℕ)
(e : Embedding (s S) (s T))

structure {u} signature_diagram_embedding_triple :=
( signature : Type (u+1) )
( diagram : signature → Type (u+1) )
( embedding : Π σ : signature, diagram σ → diagram σ → Type (u+1) )

definition {u} recursive_type : ℕ → signature_diagram_embedding_triple.{u}
| 0     := ⟨ulift unit, λ _, ulift unit, λ _ _ _, ulift unit⟩
| (n+1) := let ⟨S', D', E'⟩ := recursive_type n in
           let S := signature_data S' D' in
           let rewrite := λ σ : S, λ d' : D' σ.σ, Σ f: σ.g, E' σ.σ (σ.s f) d' in
           let result  := λ σ : S, λ d' : D' σ.σ,  in
           let D := λ σ : S,
                      diagram_data S' D' σ (rewrite σ) (result σ) in
           let E := sorry in
             ⟨ S, D, E ⟩

