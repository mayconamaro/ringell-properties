module Lib
    ( someFunc
    ) where

import Semantic
import Unroll
import EvalL
import EvalR

someFunc :: IO ()
someFunc = putStrLn "someFunc"
