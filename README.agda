
{-

A polynomial model of a Martin-Löf type theory. Based on:

- https://www.repository.cam.ac.uk/handle/1810/254394
- https://gist.github.com/bobatkey/0d1f04057939905d35699f1b1c323736

The model supports the negation of function extensionality, together with the
eta rule for functions and a wealth of type formers. So this is a nice
formalization of the unprovability of function extensionality in a reasonably
feature-rich type theory.

This project was checked with Agda 2.6.1 with standard library 1.3.

We use funext and UIP in the metatheory.

-}

module README where

-- A bundle of imports and lemmas. Lemmas are mostly about shuffling transports
-- and properties of the binary sum type, which is prominently used in the model.
open import Lib

open import CwF -- category-with-families
open import Pi
open import Sigma
open import Univ
open import Nat
open import Identity
open import Unit
open import Empty
open import Bool
open import NoFunExt -- refutation of function extensionality
