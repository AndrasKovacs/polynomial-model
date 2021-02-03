
{-# OPTIONS --type-in-type --postfix-projections #-}

module Games where
open import Lib

{-

## Summary

This file contains a game-semantic model of MLTT. In short, every closed type
represents the rules of a two-player game, although it's perhaps better to think
of games as interaction protocols, since there is no concept of winning or
losing here.

This model is an extension of the set-based polynomial model of MLTT. A
polynomial can be viewed as a request-response interaction protocol. The idea is
to extend polynomials coinductively to arbitrary number of interactions.
It turns out that this is quite simple and
  - The restriction of the model to games with 2 moves is the polynomial model
  - The restriction of the model to games with a single move is the set model

Our games are related to those in game semantics:

    https://plato.stanford.edu/entries/games-abstraction/

However, our formalism is very different, and the category of games that we are using
has fewer morphisms than usual. The two main differences from "classical" game semantics:

  1. We have "positive" games where the player starts the interaction, instead of the opponent.
  2. We only allow synchronous "copycat" game morphisms.

Nevertheless, our definition of a game is very general, and covers every
reasonable example of a deterministic two-player alternating-move game.

## Formalization

Games and game morphisms are defined using coinduction, and we assume that their equality
is given by bisimulation.

We skip proving most of the equations and only formalize the non-equation components, because
it's fairly tedious to handle the dependent equalities plus the extensional equalities of
codata. It would be a lot more convenient in a future version of cubical Agda with UIP, since
in that setting we have extensionalily for codata and computing transports.

We use --type-in-type for convenience. Everything here obviously works without
--type-in-type. I've already formalized the polynomial model with explicit
universe levels everywhere, and levels work the same way in the game model.

-}


-- CwF of games
--------------------------------------------------------------------------------

{-
We define a category-with-families of games. We use usual type-theoretic component names.

  Con : contexts, objects of the underlying category
  Sub : substitutions, morphisms of the underlying category
  Ty  : types, "dependent objects"
  Tm  : terms, "dependent morphisms"
-}

-- the type of games
record Con : Set where
  coinductive
  constructor send
  field
    M    : Set        -- M for "moves", set of possible moves
    next : M → Con    -- a game (coinductively) for every possible move
open Con

{-
In every game, the player starts.  If we have a game where the *player* has to
move in ⊥, that game is empty, i.e. it cannot be played.  If the *opponent* has
to move in ⊥, that's just the end of the game.  So there's an asymmetry between
player and opponent.
-}

-- example
game1 : Con
game1 =
  send ℕ λ n →      -- player sends a number
  send ℕ λ m →      -- opponent responds with a number
  send ⊤ λ _ →      -- player sends an element of ⊤
  send ⊥ (λ ())     -- opponent cannot respond: game ends

{-
The equality of games is understood to be strong bisimulation.
-}
record Con≡ (Γ Δ : Con) : Set where
  coinductive
  field
    M    : Γ .M ≡ Δ .M
    next : ∀ (γ : Γ .Con.M) → Con≡ (Γ .next γ) (Δ .next (coe M γ))
{-
Sub≡ is analogous. We won't prove any Con≡/Sub≡ in this file, but it's pretty
easy to check equations informally.
-}

{-
A game morphism is a synchronous level-wise translation between games.

For example, we may think of a game where moves can be played in English or
French. There's a morphism which simply translates between English and French
moves synchronously.
-}

record Sub (Γ Δ : Con) : Set where
  coinductive
  constructor sub
  field
    -- translates Γ move to Δ move
    M    : M Γ → M Δ
    -- Translates from the rest of Δ game to the rest of Γ game. The direction flips
    -- in the coinductive case, as we have to translate back-and-forth.
    next : ∀ γ → Sub (next Δ (M γ)) (next Γ γ)
open Sub

-- Γ    f     Δ
-- γ₀  -->    δ₀
-- γ₁  <--    δ₁
-- γ₂  -->    δ₂

{-

Note: Con : Set is isomorphic to the set of presheaves over ℕ≥, also known as trees.

  https://ncatlab.org/nlab/show/tree#as_functors

However, the current game model is *not* a presheaf model, because at each level
in morphisms the direction of component arrows is flipped. In short, although
a game is a presheaf tree, a game morphism is not a natural transformation.

Our morphisms are called "copycat" in game semantics literature. There is a more general
notion of morphisms which is not necessarily copycat.

  - A copycat morphism is purely a translator: it's only allowed to map moves from one game
    to another.
  - A general (async) morphism between Γ and Δ can choose between translating a
    move to the other game and making a move in the current game. So it's not a
    pure translator, it's allowed to play the game as well. For example, an async
    morphism between finite Γ and Δ games is allowed to first play out a full game in Γ,
    then play out a full game in Δ.
-}


{-
Strategy functors:
  _ᴾ : Con   → Set
  _ᴼ : Conᵒᵖ → Set

For Γ : Con, Γᴾ : Set is the set of *player strategies* for Γ. An element of Γᴾ
is just a player, or a program implementing the Γ protocol. An element of Γᴼ is
again a player/implementation, but where we consider Γ to start with an opponent
move instead of a player move.

I haven't yet checked if _ᴾ/_ᴼ extends to a model morphism of TT, and what kind of morphism.
It's a weak morphism at best, I haven't looked at what kind of weak morphism.

-}

-- action on objects
record Conᴾ (Γ : Con) : Set
record Conᴼ (Γ : Con) : Set

record Conᴾ Γ where
  coinductive
  constructor send
  field
    move : Γ .M
    next : Conᴼ (Γ .next move)
open Conᴾ

record Conᴼ Γ where
  coinductive
  constructor send
  field
    next : (γ : Γ .M) → Conᴾ (Γ .next γ)
open Conᴼ

-- action on morphisms
Subᴾ : ∀ {Γ Δ} → Sub Γ Δ → Conᴾ Γ → Conᴾ Δ
Subᴼ : ∀ {Γ Δ} → Sub Γ Δ → Conᴼ Δ → Conᴼ Γ
Subᴾ f Γᴾ .move = f .M (Γᴾ .move)
Subᴾ f Γᴾ .next = Subᴼ (f .next (Γᴾ .move)) (Γᴾ .next)
Subᴼ f Δᴼ .next = λ γ → Subᴾ (f .next γ) (Δᴼ .next (f .M γ))

-- example
strat₁ : Conᴾ game1
strat₁ =
  send 10 (     -- player sends 10
  send λ n →    -- no mattter what the opponent responds ("n")
  send tt (     -- signal the end of the game
  send (λ ()))) -- the opponent cannot respond


--------------------------------------------------------------------------------

Id : ∀ {Γ} → Sub Γ Γ
Id {Γ} .M    γ = γ
Id {Γ} .next γ = Id {Γ .next γ}

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(f ∘ g) .M    ξ = f .M (g .M ξ)
(f ∘ g) .next ξ = g .next ξ ∘ f .next (g .M ξ)

-- Coproduct of games. Player chooses which game to play.
-- If a player is able to play Γ + Δ, then they are able to either play Γ or Δ.
infixr 4 _+_
_+_ : Con → Con → Con
(Γ + Δ) .M    = Γ .M ⊎ Δ .M
(Γ + Δ) .next = case (Γ .next) (Δ .next)

Inj₁ : ∀ {Γ Δ} → Sub Γ (Γ + Δ)
Inj₁ .M    γ = inj₁ γ
Inj₁ .next γ = Id

Inj₂ : ∀ {Γ Δ} → Sub Δ (Γ + Δ)
Inj₂ .M    δ = inj₂ δ
Inj₂ .next δ = Id

-- recursion principle for coproduct
+-rec : ∀ {Γ Δ Ξ} → Sub Γ Ξ → Sub Δ Ξ → Sub (Γ + Δ) Ξ
+-rec f g .M    = case (f .M) (g .M)
+-rec f g .next = ⊎-elim _ (f .next) (g .next)

-- empty game (initial game)
⊘ : Con
⊘ .M    = ⊥
⊘ .next ()

Init : ∀ {Γ} → Sub ⊘ Γ
Init .M  ()
Init .next ()

-- terminal game: player signals end-of-game.
∙ : Con
∙ .M      = ⊤
∙ .next _ = ⊘

-- unique morphism into ∙
ε : ∀ {Γ} → Sub Γ ∙
ε .M    _ = _
ε .next _ = Init

{-
In the current model, all type dependency happens in the first turn (2
moves). We only use dependent types to negotiate with the opponent in the first
turn, about which game to play.

The same thing happens in the polynomial model: the request part models type
dependency, but responses only model simple type theory.

An inutitive reason is the following: when we switch to the opponent, we flip
polarity, so every construction in the model is dualized. However, while it is
possible to take the opposite of a category, it's not possible to take the
opposite of a CwF.

In a CwF, a term is a dependent morphism, but the domains and codomains cannot
be generally flipped, because the latter depends on the former. So if (f : M.Sub
Γ Δ) is in M, then (f : Mᵒᴾ.Sub Δ Γ), but for (t : Tm Γ A) we can't do this. The
only thing we can do is to restrict M to a "simply typed democratic CwF", where
(Tm Γ A) can be reversed to (Tm (F A) (G Γ)), where (F,G) is an isomorphism
between types and contexts.

Thus all type dependency is on the first player move.
-}

Ty : Con → Set
Ty Γ = Γ .M → Con

infix 6 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
(A [ f ]T) γ = A (f .M γ)

[id]T : ∀ {Γ}{A : Ty Γ} → A [ Id {Γ} ]T ≡ A
[id]T = refl

[∘]T : ∀ {Γ Δ Σ}{A : Ty Σ}{f : Sub Δ Σ}{g : Sub Γ Δ} → A [ f ]T [ g ]T ≡ A [ f ∘ g ]T
[∘]T = refl

{-
A term is a dependent morphism from Γ to A : Ty Γ. This is *not* coinductively defined, because
we only have to take care of dependency in the first move, then switch to non-dependent morphisms.
-}
record Tm (Γ : Con)(A : Ty Γ) : Set where
  constructor tm
  field
    M    : ∀ γ → M (A γ)                           -- dependency
    next : ∀ γ → Sub (A γ .next (M γ)) (Γ .next γ) -- continuing with a normal morphism (non-dependent)
open Tm

infix 6 _[_]t
_[_]t : ∀ {Γ Δ A}(t : Tm Δ A)(f : Sub Γ Δ) → Tm Γ (A [ f ]T)
(t [ f ]t) .M    γ = t .M (f .M γ)
(t [ f ]t) .next γ = f .next γ ∘ t .next (f .M γ)

{-
Context extension is like a sigma of games.
- The player starts with a sigma of first moves in Γ and A.
- The opponent chooses to continue playing in Γ or in A.

If A is non-dependent (constant), then Γ ▶ A is the product of Γ and A. In this
case, a player can play Γ ▶ A iff they can play Γ and A.

If A is dependent, then a player can play Γ ▶ A iff there exists a "γ" first move of Γ s.t.
the player can play Γ starting from γ and can also play (A γ).
-}
infixl 3 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
(Γ ▶ A) .M            = ∃ λ γ → A γ .M            -- sigma (product/negative)
(Γ ▶ A) .next (γ , α) = Γ .next γ + A _ .next α   -- coproduct (positive)

p : ∀ {Γ A} → Sub (Γ ▶ A) Γ
p .M    (γ , α) = γ
p .next (γ , α) = Inj₁

q : ∀ {Γ A} → Tm (Γ ▶ A) (A [ p {Γ}{A} ]T)
q .M    (γ , α) = α
q .next (γ , α) = Inj₂

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ A}(f : Sub Γ Δ) → Tm Γ (A [ f ]T) → Sub Γ (Δ ▶ A)
(f ,ₛ t) .M    γ = (f .M γ) , (t .M γ)
(f ,ₛ t) .next γ = +-rec (f .next γ) (t .next γ)

--------------------------------------------------------------------------------

{-
There are a number of exotic animals in the category of games. For example, we
have two different symmetric monoidal products. I give here their definition and
a sample of monoidal ops.

Both work by playing two games in a interleaved fashion.

In the first interleaving product, the player always has to play in both games,
then the opponent chooses which game to respond in. This is rather weird: in Γ ⊗
Δ games must always end at the exact same time, because the game can only end if
player can make moves both in Γ and Δ, but opponent cannot respond to either. So
if (Γ ⊗ Δ) cannot always be played in a ways such that Γ and Δ end
simultaneously, then (Γ ⊗ Δ) is the empty game!
-}

infixr 4 _⊗_
_⊗_ : Con → Con → Con
(Γ ⊗ Δ) .M                            = Γ .M × Δ .M                   -- player both games
(Γ ⊗ Δ) .next (γ , δ) .M              = Γ .next γ .M ⊎ Δ .next δ .M   -- opponent pick which game to continue
(Γ ⊗ Δ) .next (γ , δ) .next (inj₁ γ') = Γ .next γ .next γ' ⊗ Δ
(Γ ⊗ Δ) .next (γ , δ) .next (inj₂ δ') = Γ ⊗ Δ .next δ .next δ'

⊗-map : ∀ {Γ Γ' Δ Δ'} → Sub Γ Γ' → Sub Δ Δ' → Sub (Γ ⊗ Δ) (Γ' ⊗ Δ')
⊗-map f g .M    (γ , δ)                 = (f .M γ) , (g .M δ)
⊗-map f g .next (γ , δ) .M    (inj₁ γ') = inj₁ (f .next γ .M γ')
⊗-map f g .next (γ , δ) .M    (inj₂ δ') = inj₂ (g .next δ .M δ')
⊗-map f g .next (γ , δ) .next (inj₁ γ') = ⊗-map (f .next γ .next γ') g
⊗-map f g .next (γ , δ) .next (inj₂ δ') = ⊗-map f (g .next δ .next δ')

-- + functor action on id, ∘

⊗-idl→ : ∀ {Γ} → Sub (Γ ⊗ ∙) Γ
⊗-idl→ .M    (γ , _)          = γ
⊗-idl→ .next (γ , _) .M    γ' = inj₁ γ'
⊗-idl→ .next (γ , _) .next γ' = ⊗-idl→

⊗-idl← : ∀ {Γ} → Sub Γ (Γ ⊗ ∙)
⊗-idl← .M    γ                 = γ , tt
⊗-idl← .next γ .M    (inj₁ γ') = γ'
⊗-idl← .next γ .next (inj₁ γ') = ⊗-idl←

-- ⊗-idr→ : ∀ {Γ} → Sub (∙ ⊗ Γ) Γ
-- ⊗-idr← : ∀ {Γ} → Sub Γ (∙ ⊗ Γ)

⊗-ass→ : ∀ {Γ Δ Ξ} → Sub ((Γ ⊗ Δ) ⊗ Ξ) (Γ ⊗ Δ ⊗ Ξ)
⊗-ass→ .M    ((γ , δ) , ξ)                        = γ , δ , ξ
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₁ γ')        = inj₁ (inj₁ γ')
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₂ (inj₁ δ')) = inj₁ (inj₂ δ')
⊗-ass→ .next ((γ , δ) , ξ) .M    (inj₂ (inj₂ ξ')) = inj₂ ξ'
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₁ γ')        = ⊗-ass→
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₂ (inj₁ δ')) = ⊗-ass→
⊗-ass→ .next ((γ , δ) , ξ) .next (inj₂ (inj₂ ξ')) = ⊗-ass→

-- ⊗-ass← : ∀ {Γ Δ Ξ} → Sub (Γ ⊗ Δ ⊗ Ξ) ((Γ ⊗ Δ) ⊗ Ξ)
-- etc...

⊗-comm : ∀ {Γ Δ} → Sub (Γ ⊗ Δ) (Δ ⊗ Γ)
⊗-comm .M    (γ , δ)                 = δ , γ
⊗-comm .next (γ , δ) .M    (inj₁ γ') = inj₂ γ'
⊗-comm .next (γ , δ) .M    (inj₂ δ') = inj₁ δ'
⊗-comm .next (γ , δ) .next (inj₁ γ') = ⊗-comm
⊗-comm .next (γ , δ) .next (inj₂ δ') = ⊗-comm

⊗-proj₁ : ∀ {Γ Δ} → Sub (Γ ⊗ Δ) Γ
⊗-proj₁ = ⊗-idl→ ∘ ⊗-map Id ε

⊗-proj₂ : ∀ {Γ Δ} → Sub (Γ ⊗ Δ) Δ
⊗-proj₂ = ⊗-proj₁ ∘ ⊗-comm

{-
The second symmetric monoidal product operation is a lot more intuitive as interleaving: here
the player chooses which game to move in. So if one game ends, (Γ ⊕ Δ) just continues
in the other game, and it ends if both games end.
-}

infixr 4 _⊕_
_⊕_ : Con → Con → Con
(Γ ⊕ Δ) .M                      = Γ .M ⊎ Δ .M
(Γ ⊕ Δ) .next (inj₁ γ) .M       = Γ .next γ .M
(Γ ⊕ Δ) .next (inj₁ γ) .next γ' = Γ .next γ .next γ' ⊕ Δ  -- we made a turn in Γ, but did nothing in Δ
(Γ ⊕ Δ) .next (inj₂ δ) .M       = Δ .next δ .M
(Γ ⊕ Δ) .next (inj₂ δ) .next δ' = Γ ⊕ Δ .next δ .next δ'  -- we made a turn in Δ

⊕-map : ∀ {Γ Γ' Δ Δ'} → Sub Γ Γ' → Sub Δ Δ' → Sub (Γ ⊕ Δ) (Γ' ⊕ Δ')
⊕-map f g .M    (inj₁ γ)          = inj₁ (f .M γ)
⊕-map f g .M    (inj₂ δ)          = inj₂ (g .M δ)
⊕-map f g .next (inj₁ γ) .M    γ' = f .next γ .M γ'
⊕-map f g .next (inj₁ γ) .next γ' = ⊕-map (f .next γ .next γ') g
⊕-map f g .next (inj₂ δ) .M    δ' = g .next δ .M δ'
⊕-map f g .next (inj₂ δ) .next δ' = ⊕-map f (g .next δ .next δ')

⊕-idl→ : ∀ {Γ} → Sub (Γ ⊕ ⊘) Γ
⊕-idl→ .M    (inj₁ γ)          = γ
⊕-idl→ .next (inj₁ γ) .M    γ' = γ'
⊕-idl→ .next (inj₁ γ) .next γ' = ⊕-idl→

⊕-idl← : ∀ {Γ} → Sub Γ (Γ ⊕ ⊘)
⊕-idl← .M    γ          = inj₁ γ
⊕-idl← .next γ .M    γ' = γ'
⊕-idl← .next γ .next γ' = ⊕-idl←

-- + all other stuff


-- Pi
--------------------------------------------------------------------------------

{-
Pi is the most complicated part, and if you ask me it's the only complicated part.

The basic idea is the same as in "Higher-Order Containers":

  http://www.cs.ox.ac.uk/people/samuel.staton/papers/cie10.pdf

But we have more dependencies and a bit more data related to games.

The goal is to define Π in a way such that there is a natural
isomorphism (Tm (Γ ▶ A) B ≃ Tm Γ (Π A B)).

To simplify things, first let's consider the case when Γ = ∙.

Now, (Tm (∙ ▶ A) B ≃ Tm ∙ (Π A B)) is not too hard to define.

Tm ∙ (Π A B) is necessarily a morphism which translates from ⊤ to (Π A B tt .M),
then stops there, since we cannot map back to (∙ .next tt) which is ⊥, unless
(Π A B .next tt) is also ⊥.

In general, Tm ∙ A is equivalent to (A tt .M).

Hence, in the empty context, we can simply define (Π A B tt .M) to be (Tm (A tt) (λ α → B (tt , α)))
and (Π A B tt .next) as constantly ⊥. So this is a game where player sends a term and we stop.

However, this is wrong in non-empty contexts, because (Π A B γ .next = λ _ → ⊥) implies that
translation stops after the first move, and a Tm Γ (Π A B) can't have any action on later Γ
moves. So we need to put at least *some* information in (Π A B γ .next), in order to represent
dependency on Γ. The Γ = ∙ case will still degenerate to what we've seen above.

We define (Π A B γ .M) to be the set of a particular kind of *partial* terms from A to B.

First, from A : Ty Γ we define an A' : Ty Γ as follows:

  A' γ = send (A γ .M) λ α → ∙ + A γ .next α

This is the A game except the player has the choice to stop the game after the first turn.

Hence, Tm (A' γ) (λ α → B (γ, α)) is a translation from A to B except the translation has the
choice to stop after doing one trip from A to B then back.

The choice to stop can be also viewed as the ability to throw an exception.

Then, we define (Π A B γ .next t .M) as the *set of throwing traces* for (Π A B .γ .M).
A trace consists of an α move in A γ .M and β' move in B (γ , α) .M, and this is a throwing
trace if (Π A B γ .M) elects to throw an exception on it.

We define (Π A B γ .next t .next (α , β' , p)) as (B (γ , α) .next (t .M α) .next β'). This
becomes an *exception handler*: for every throwing trace, we're allowed to continue the game
in B.

So, to summarize a Π A B game.
- First, player sends a partial term from A to B.
- Opponent has to reply with a throwing trace for the term. If there is no throwing trace,
  then the game stops here and the term is actually total. If there is a throwing trace, the
  game continues as the B game at the point of throwing.

Now, to explain Lam and App.

For Lam, we have (t : Tm (Γ ▶ A) B) and want to define (Tm Γ (Π A B)).
  - We first need to map a γ move in Γ to a partial term from A to B.
    - The term is given by first mapping from A to B, then using the backwards
      map from "t" to go from B to (Γ ▶ A). Here, this means a map from B to (Γ + A).
    - Whenever the map returns in Γ, the term throws an exception.
    - Whenever the map returns in A, the term continues.
  - Then we need to map a throwing trace back to Γ. We simply use "t", since
    a throwing trace includes evidence that "t" maps that particular trace to Γ.

For App, we have (t : Tm Γ (Π A B)), and want to define (Tm (Γ ▶ A) B)
  - We first need to map (γ, α) in (Γ ▶ A) to a move in B, for this we just
    take the partial term given by "t" at γ, and use its action on A's first moves.
  - We need to map from B back to (Γ ▶ A). For this, we use again the partial term;
    when it throws, we use "t" to map the throwing trace to Γ and get a Sub Γ B,
    otherwise the partial term maps to A and we get a Sub A B.
-}


Π : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Π A B γ .M                         = Tm (send (A γ .M) λ α → ∙ + A γ .next α) (λ α → B (γ , α))
Π A B γ .next t .M                 = ∃₂ λ α β' → isLeft (t .next α .M β')
Π A B γ .next t .next (α , β' , p) = B (γ , α) .next (t .M α) .next β'

Lam : ∀ {Γ A B} → Tm (Γ ▶ A) B → Tm Γ (Π {Γ} A B)
Lam t .M γ .M    α       = t .M (γ , α)
Lam t .M γ .next α .M β' = lmap (t .next (γ , α) .M β') _
Lam t .M γ .next α .next β' with t .next (γ , α) .M β' | t .next (γ , α) .next β'
... | inj₁ γ' | t' = Init
... | inj₂ α' | t' = t'
Lam t .next γ .M (α , β' , p) with t .next (γ , α) .M β'
... | inj₁ γ' = γ'
... | inj₂ α' = ⊥-elim p
Lam t .next γ .next (α , β' , p) with t .next (γ , α) .M β' | t .next (γ , α) .next β'
... | inj₁ γ' | t' = t'
... | inj₂ α' | t' = ⊥-elim p

App : ∀ {Γ A B} → Tm Γ (Π {Γ} A B) → Tm (Γ ▶ A) B
App t .M    (γ , α) = t .M γ .M α
App t .next (γ , α) .M    β' with t .M γ .next α .M β' | inspect (t .M γ .next α .M) β'
                                | t .M γ .next α .next β'
... | inj₁ tt | [ eq ] | t' = inj₁ (t .next γ .M (α , β' , tr isLeft (eq ⁻¹) tt))
... | inj₂ α' | [ eq ] | t' = inj₂ α'
App t .next (γ , α) .next β' with t .M γ .next α .M β' | inspect (t .M γ .next α .M) β'
                                | t .M γ .next α .next β'
... | inj₁ tt | [ eq ] | t' = t .next γ .next _
... | inj₂ α' | [ eq ] | t' = t'


-- Sigma
--------------------------------------------------------------------------------

{- Sigma is just a more parametrized version of _▶_ -}

Sg : ∀ {Γ}(A : Ty Γ) → Ty (Γ ▶ A) → Ty Γ
Sg A B γ .M            = Σ (A γ .M) λ α → B (γ , α) .M        -- sigma
Sg A B γ .next (α , β) = A γ .next α + B (γ , α) .next β      -- chooses which projection to respond to

Proj₁ : ∀ {Γ A B} → Tm Γ (Sg {Γ} A B) → Tm Γ A
Proj₁ t .M    γ = t .M γ .₁
Proj₁ t .next γ = t .next γ ∘ Inj₁

Proj₂ : ∀ {Γ A B}(t : Tm Γ (Sg {Γ} A B)) → Tm Γ (B [ Id ,ₛ Proj₁ t ]T)
Proj₂ t .M    γ = t .M γ .₂
Proj₂ t .next γ = t .next γ ∘ Inj₂

Pair : ∀ {Γ A B}(t : Tm Γ A) → Tm Γ (B [ Id ,ₛ t ]T) → Tm Γ (Sg {Γ} A B)
Pair t u .M    γ = (t .M γ) , (u .M γ)
Pair t u .next γ = +-rec (t .next γ) (u .next γ)


-- Universe
--------------------------------------------------------------------------------

{-
Universe is just player giving a game. This is universe in Coquand style, where
El and code form a natural isomorphism. Without --type-in-type we'd have a level
bump in U.
-}

U : ∀ {Γ} → Ty Γ
U γ .M      = Con          -- player gives a game
U γ .next _ = ⊘            -- stop

El : ∀ {Γ} → Tm Γ (U {Γ}) → Ty Γ
El a γ .M    = a .M γ .M
El a γ .next = a .M γ .next

code : ∀ {Γ} → Ty Γ → Tm Γ (U {Γ})
code A .M    γ = A γ
code A .next γ = Init


-- Identity
--------------------------------------------------------------------------------

Eq : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
Eq {Γ}{A} t u γ .M      = t .M γ ≡ u .M γ           -- equality of first moves
Eq {Γ}{A} t u γ .next p = ⊘                         -- stop

Refl : ∀ {Γ A}(t : Tm Γ A) → Tm Γ (Eq t t)
Refl t .M    γ = refl
Refl t .next γ = Init

UIP' : ∀ {Γ A}{t u : Tm Γ A}{e e' : Tm Γ (Eq t u)} → Tm Γ (Eq e e')
UIP' .M    γ = UIP _ _
UIP' .next γ = Init

Tr : ∀ {Γ A}(B : Ty (Γ ▶ A)){t u : Tm Γ A}(e : Tm Γ (Eq t u))
     → Tm Γ (B [ Id ,ₛ t ]T) → Tm Γ (B [ Id ,ₛ u ]T)
Tr {Γ} {A} B {t} {u} e bt .M    γ = tr (λ x → M (B (γ , x))) (e .M γ) (bt .M γ)
Tr {Γ} {A} B {t} {u} e bt .next γ =
  J (λ uγ eq → Sub (B (γ , uγ) .next (tr (λ x → M (B (γ , x))) eq (bt .M γ)))
                   (Γ .next γ))
    (e .M γ) (bt .next γ)

¬FunExt : (∀ {Γ A B}{t u : Tm Γ (Π {Γ} A B)} → Tm (Γ ▶ A) (Eq (App t) (App u)) → Tm Γ (Eq t u))
        → ⊥
¬FunExt fext with
  ap (λ t → t .next _ .M _)
  (fext {∙}{λ _ → send ⊤ λ _ → send Bool λ _ → ⊘}
          {λ _ → send ⊤ λ _ → send ⊤ λ _ → ⊘}
          {tm (λ _ → tm _ (λ _ → sub (λ _ → inj₂ true) λ _ → Init))
              (λ _ → sub (λ ()) λ ())}
          {tm (λ _ → tm _ (λ _ → sub (λ _ → inj₂ false) λ _ → Init))
              (λ _ → sub (λ ()) λ ())}
          (tm (λ _ → refl) λ _ → Init)
          .M _)
... | ()

-- But note that since (Reflect → FunExt), we have (¬Funext → ¬Reflect) anyway
¬Reflect : (∀ {Γ A t u} → Tm Γ (Eq {Γ}{A} t u) → t ≡ u) → ⊥
¬Reflect rf with
    ap (λ t → t .next _ . M _)
    (rf {send ⊤ λ _ → send Bool λ _ → ⊘}
        {λ _ → send ⊤ λ _ → ∙}
        {tm _ λ _ → sub (λ _ → true) λ _ → Init}
        {tm _ λ _ → sub (λ _ → false) λ _ → Init}
        (tm (λ _ → refl) λ _ → Init))
... | ()


-- Nat
--------------------------------------------------------------------------------

Nat : ∀ {Γ} → Ty Γ
Nat γ .M      = ℕ           -- give a ℕ
Nat γ .next _ = ⊘           -- stop

Zero : ∀ {Γ} → Tm Γ (Nat {Γ})
Zero .M    _ = zero
Zero .next γ = Init

Suc : ∀ {Γ} → Tm Γ (Nat {Γ}) → Tm Γ (Nat {Γ})
Suc t .M    γ = suc (t .M γ)
Suc t .next γ = Init

NatElim : ∀ {Γ}(B : Ty (Γ ▶ Nat {Γ}))
          → Tm Γ (B [ Id ,ₛ Zero {Γ} ]T)
          → Tm (Γ ▶ Nat {Γ} ▶ B) (λ {((γ , n) , bn) → B (γ , suc n)})
          → Tm (Γ ▶ Nat {Γ}) B
NatElim B z s .M    (γ , zero)  = z .M γ
NatElim B z s .M    (γ , suc n) = s .M ((γ , n) , NatElim B z s .M (γ , n))
NatElim B z s .next (γ , zero)  = Inj₁ ∘ z .next γ
NatElim B z s .next (γ , suc n) = +-rec Id (NatElim B z s .next (γ , n)) ∘ s .next ((γ , n), _)

-- List
--------------------------------------------------------------------------------

{-
An example for a parametrized inductive type.  Player sends a list of moves,
then opponent chooses one move from the list to respond to.  This means that if
player sends an empty list, the game ends.

Pretty much any inductive type works in an analogous way.
-}

open import Data.List renaming (List to list)

List : ∀ {Γ} → Ty Γ → Ty Γ
List {Γ} A γ .M             = list (A γ .M)                       -- player sends a list of  moves
List {Γ} A γ .next []       = ⊘                                   -- opponent chooses to respond to one
List {Γ} A γ .next (α ∷ αs) = A γ .next α + List {Γ} A γ .next αs --   move in the list

Nil : ∀ {Γ A} → Tm Γ (List {Γ} A)
Nil .M    γ = []
Nil .next γ = Init

Cons : ∀ {Γ A} → Tm Γ A → Tm Γ (List {Γ} A) → Tm Γ (List {Γ} A)
Cons t u .M    γ = t .M γ ∷ u .M γ
Cons t u .next γ = +-rec (t .next γ) (u .next γ)

Foldr : ∀ {Γ}{A B : Ty Γ} → Tm (Γ ▶ A  ▶ B [ p {Γ}{A} ]T) (B [ p {Γ}{A} ∘ p {Γ ▶ A}{B [ p {Γ}{A} ]T} ]T)
                          → Tm Γ B → Tm (Γ ▶ List {Γ} A) (B [ p {Γ}{List {Γ} A} ]T)
Foldr t u .M (γ , [])     = u .M  γ
Foldr t u .M (γ , α ∷ αs) = t .M ((γ , α) , Foldr t u .M (γ , αs))
Foldr t u .next (γ , [])     = Inj₁ ∘ u .next γ
Foldr t u .next (γ , α ∷ αs) = +-rec (+-rec Inj₁ (Inj₂ ∘ Inj₁)) (+-rec Inj₁ (Inj₂ ∘ Inj₂)
                             ∘ Foldr t u .next (γ , αs))
                             ∘ t .next ((γ , α) , _)
