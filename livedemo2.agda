import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Agda.Primitive

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n

inv-s≤s m≤n = ?

-- Where are m and n?
--inv-s≤s {m} {n} m≤n = ?


inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
  
inv-z≤n z≤n = ?


-- Same question – what's the type where m and zero are equal?
inv-z≤n′ : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → _≡_ {_} {ℕ} m zero
  
inv-z≤n′ m≤z = ?


 
