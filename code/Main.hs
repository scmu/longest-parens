module Main where

import LongestParens03

main = do inp <- getContents
          let t = lbs inp
          putStr (pr' t)
