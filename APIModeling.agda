
-- | modeling apis as presheaves
-- subtyping!
module ServerClient where

-- A Universe of Servers
data API : Set where
  v0 : API
  v1 : API
  v2 : API

-- | We define a poset relation on servers
data _≤_ : API -> API -> Set where
  id : {s : API} -> s ≤ s
  f : v1 ≤ v2

_∘_ : {a b c : API} -> b ≤ c -> a ≤ b -> a ≤ c
id ∘ y = y
f ∘ id = f

-- | Servers are presheaves...
data Server : API -> Set where
  server : {needs has : API} -> needs ≤ has -> Server needs

-- | i.e. contravariant functors.
-- | A Server b coerces to a Server b
-- | while an a is a subapi of b
coerceServer : {a b : API} -> a ≤ b -> Server b -> Server a
coerceServer rel _ = server rel

-- | Clients are presheaves
data Client : API -> Set where
  client : {needs has : API} -> needs ≤ has -> Client needs

-- | i.e. contravariant functors
coerceClient : {a b : API} -> a ≤ b -> Client b -> Client a
coerceClient rel _ = client rel

-- | We can only talk if we speak the same api
data Talk : API -> API -> Set where
  talk : {a : API} -> Server a -> Client a -> Talk a a

-- | We can communicate successfully if we find common "ground"
makeTalk : {a b c : API} -> a ≤ b -> a ≤ c -> Server b -> Client c -> Talk a a
makeTalk rel-ser rel-cli ser cli =
  talk
  (coerceServer rel-ser ser)
  (coerceClient rel-cli cli)
