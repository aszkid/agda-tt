import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- one natural is less than or equal to another if...
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}       -- the first natural is zero
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}     -- its predecessor is less than the other's predecessor
    → m ≤ n
      -------------
    → suc m ≤ suc n
