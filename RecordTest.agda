module RecordTest where

open import Data.Bool
open import Data.Nat
open import Data.Vec hiding (map)
open import Data.Product
open import Data.String


record Person : Set where
  constructor person
  field
    name : String
    age : ℕ


me : Person
me = person "Sean" 20
