/-

I'm looking for some help learning how to do mutual inductive types. The context here is wanting to 
define Vicary's semistrict higher categories <https://arxiv.org/pdf/1610.06908.pdf> in Lean. (Partly 
just for the sake of having them as an approach to 2-, 3-, and 4- categories for mathlib, and more 
importantly as an essential step of using Globular in Lean.)

The actual mutual inductive type needed is quite complicated (it needs notions of "signature, 
diagram, slice, embedding, rewrite, and lift"), but here's a trimmed down start that I still don't 
know how to do in Lean.

We have a mutual inductive definition of "signatures" and "diagrams". I'll start with an informal 
definition, very closely following the text of their paper, except where they make mistakes...

For $n \geq 0$, an $n$-signature Sigma is a family of sets $(\Sigma_0, ..., \Sigma_n)$, such that when $n > 0$,
* $\Sigma' = (Sigma_0, ..., Sigma_{n-1})$ is an $(n-1)$-signature,
* each $g \in \Sigma_n$ is equipped with a pair of $(n-1)$-diagrams $g.s$ and $g.t$ over the signature $\Sigma'$,
* and if $n > 1$, then $g.s.s = g.t.s$ and $g.s.t = g.t.t$.
For $n \geq 0$, an $n$-diagram $D$ over an $n$-signature $\Sigma$ is a
* if $n > 0$, an $(n-1)$-diagram $D.s$ over $\Sigma'$,
* a list of elements of $Sigma_n$,
* if $n = 0$, this list must have length one, and
* some more data (the embeddings) which I want to omit for this question.

How are we meant to tell Lean about this?


-/

universes u

mutual inductive signature, diagram
with signature : Type (u+1)
| zero : Type u → signature
| succ : Type u → signature → signature
with diagram : Type (u+1)
| empty : Π (s : signature) (source : sorry), diagram
| layer : Π (s : signature) (layers : diagram)


-- mutual inductive lists.equiv, lists'.subset
-- with lists.equiv : lists α → lists α → Prop
-- | refl (l) : lists.equiv l l
-- | antisymm {l₁ l₂ : lists' α tt} :
--   lists'.subset l₁ l₂ → lists'.subset l₂ l₁ → lists.equiv ⟨_, l₁⟩ ⟨_, l₂⟩
-- with lists'.subset : lists' α tt → lists' α tt → Prop