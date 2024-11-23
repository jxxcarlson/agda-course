module Main where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import IO.Primitive

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}

main : IO ⊤
main = putStrLn "Hello, Agda!"

{-

Great! You've now got a working "Hello, World!" program in Agda. This is a good foundation for more complex programs.
Just to explain what's happening in this code:
open import Agda.Builtin.IO gives us the IO monad
open import Agda.Builtin.Unit provides ⊤ (top/unit type)
open import Agda.Builtin.String gives us the String type
The postulate and FOREIGN/COMPILE pragmas create the bridge between Agda and Haskell's runtime system
main : IO ⊤ declares the main function that returns an IO action with unit result type
If you want to write more complex IO programs, you might want to look into:
Using do notation for sequential IO operations
Working with other IO primitives like getLine
Handling files
Converting between different string types
Would you like to explore any of these next?

-}