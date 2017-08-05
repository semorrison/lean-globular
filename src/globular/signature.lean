mutual inductive signature, diagram
with signature : ℕ → Type 2
| empty      : signature 0
| s          : Π n : ℕ, Π g : Type, Π σ : (signature n), Π s t : g → diagram n σ, signature (n+1)
with diagram : Π n : ℕ, Π σ : (signature n), Type 2
| empty      : diagram 0
| d          : Π n : ℕ, Π σ : (signature (n+1)), Π s : diagram n sorry, diagram (n+1) σ
