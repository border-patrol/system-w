||| Module    : Main.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Data.List

import Test.Golden

%default total

tests : TestPool
tests
  = MkTestPool "TODO Tests"
        []
        Nothing
        [ "000-todo"
        ]

covering
main : IO ()
main
  = runner [ tests ]

-- [ EOF ]
