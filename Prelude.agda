module OTT.Prelude where

open import Level renaming (zero to lzero; suc to lsuc) using (Level) public
open import Function public
open import Data.Empty public
open import Data.Unit.Base using (⊤; tt) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base public
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc) public
open import Data.Product hiding (,_) renaming (map to pmap) public

infix 4 ,_

pattern ,_ y = _ , y
